use crate::hal::{BufferDirection, Dma, Hal, PhysAddr};
use crate::transport::Transport;
use crate::{nonnull_slice_from_raw_parts, pages, Error, Result};
use alloc::vec::Vec;
use bitflags::bitflags;
use core::hint::spin_loop;
use core::mem::{size_of, take};
use core::ptr::NonNull;
use core::sync::atomic::{fence, Ordering};
use log::info;
use zerocopy::FromBytes;
// use log::{debug, info};

pub struct PackedQueue<H: Hal, const SIZE: usize> {
    /// DMA guard
    layout: PackedQueueLayout<H>,

    /// Descriptor table
    ///
    /// The device may be able to modify this, even though it's not supposed to, so we shouldn't
    /// trust values read back from it. Use `desc_shadow` instead to keep track of what we wrote to
    /// it.
    desc: NonNull<[Descriptor]>,

    indirect_desc_vec: Vec<Option<Dma<H>>>,
    driver_event_suppression: NonNull<PvirtqEventSuppress>,
    device_event_suppression: NonNull<PvirtqEventSuppress>,

    /// The number of descriptors currently in use.
    avail_wrap_count: bool,
    used_wrap_count: bool,
    avail_used_flags: DescFlags,

    /// The index of queue
    queue_idx: u16,

    /// Our trusted copy of `desc` that the device can't access.
    desc_shadow: [Descriptor; SIZE],
    /// Our trusted copy of `avail.idx`.
    last_used_idx: u16,
    free_head: u16,
    num_used: u16,

    indirect_desc: bool,
}


impl<H: Hal, const SIZE: usize> PackedQueue<H, SIZE> {
    /// Create a new VirtQueue.
    ///
    /// Ref: 4.2.3.2 Virtqueue Configuration
    pub fn new<T: Transport>(transport: &mut T, idx: u16, indirect_desc: bool) -> Result<Self> {
        if transport.queue_used(idx) {
            return Err(Error::AlreadyUsed);
        }
        if !SIZE.is_power_of_two()
            || SIZE > u16::MAX.into()
            || transport.max_queue_size(idx) < SIZE as u32
        {
            return Err(Error::InvalidParam);
        }
        let size = SIZE as u16;

        let layout = PackedQueueLayout::allocate(size)?;

        transport.queue_set(
            idx,
            size.into(),
            layout.descriptors_paddr(),
            layout.driver_area_paddr(),
            layout.device_area_paddr(),
        );

        let mut indirect_desc_vec = Vec::<Option<Dma<H>>>::with_capacity(SIZE);
        info!("SIZE = {}", SIZE);
        for _ in 0..SIZE {
            indirect_desc_vec.push(None);
        }
        let desc =
            nonnull_slice_from_raw_parts(layout.descriptors_vaddr().cast::<Descriptor>(), SIZE);
        let driver_event_suppression = layout.driver_event_suppression_vaddr().cast();
        let device_event_suppression = layout.device_event_suppression_vaddr().cast();

        let desc_shadow: [Descriptor; SIZE] = FromBytes::new_zeroed();

        Ok(PackedQueue {
            layout,
            desc,
            driver_event_suppression,
            device_event_suppression,
            indirect_desc_vec,
            queue_idx: idx,
            avail_wrap_count: true,
            used_wrap_count: true,
            avail_used_flags: DescFlags::VIRTQ_DESC_F_AVAIL,
            desc_shadow,
            free_head: 0,
            num_used: 0,
            last_used_idx: 0,
            indirect_desc,
        })
    }

    /// Unshares buffers in the list starting at descriptor index `head` and adds them to the free
    /// list. Unsharing may involve copying data back to the original buffers, so they must be
    /// passed in too.
    ///
    /// Ref: linux virtio_ring.c detach_buf_split
    /// This will push all linked descriptors at the front of the free list.
    ///
    /// # Safety
    ///
    /// The buffers in `inputs` and `outputs` must match the set of buffers originally added to the
    /// queue by `add`.
    unsafe fn recycle_descriptors<'a>(
        &mut self,
        head: u16,
        inputs: &'a [&'a [u8]],
        outputs: &'a mut [&'a mut [u8]],
    ) -> usize {
        // let original_free_head = self.free_head;
        let mut next = head;
        let mut len = 0;

        if self.indirect_desc {
            let desc: &mut Descriptor = &mut self.desc_shadow[usize::from(next)];
            len = desc.len as usize / size_of::<Descriptor>();
            desc.unset_buf();
            self.write_desc(next);
            self.num_used = self.num_used.wrapping_sub(1);
            next += 1;
            if next == SIZE as u16 {
                next = 0;
                self.used_wrap_count ^= true;
            }
            self.last_used_idx = next;

            
        } else {
            for (buffer, direction) in InputOutputIter::new(inputs, outputs) {
                let desc_index = next;
                let desc: &mut Descriptor = &mut self.desc_shadow[usize::from(desc_index)];

                let paddr = desc.addr;
                desc.unset_buf();
                self.num_used = self.num_used.wrapping_sub(1);
                next += 1;
                if next == SIZE as u16 {
                    next = 0;
                    self.used_wrap_count ^= true;
                }

                self.write_desc(desc_index);

                // Safe because the caller ensures that the buffer is valid and matches the descriptor
                // from which we got `paddr`.
                unsafe {
                    // Unshare the buffer (and perhaps copy its contents back to the original buffer).
                    H::unshare(paddr as usize, buffer, direction);
                }
                self.last_used_idx = next;
            }
        }
        len

    }

    // TODO: will be deleted in the further
    /// queue by `add`.
    unsafe fn recycle_descriptors_sync<'a>(&mut self, head: u16) -> usize {
        // let original_free_head = self.free_head;
        let mut next = head;
        let mut len = 0;

        loop {
            let desc_index = next;
            let desc: &mut Descriptor = &mut self.desc_shadow[usize::from(desc_index)];

            let id = desc.id;
            desc.unset_buf();
            self.num_used = self.num_used.wrapping_sub(1);
            let old_next = next;
            next += 1;
            if next == SIZE as u16 {
                next = 0;
                self.used_wrap_count ^= true;
            }

            self.write_desc(desc_index);
            len += 1;
            self.last_used_idx = next;

            if id == head || old_next == head {
                break;
            }
        }
        return len
    }

    /// Copies the descriptor at the given index from `desc_shadow` to `desc`, so it can be seen by
    /// the device.
    fn write_desc(&mut self, index: u16) {
        let index = usize::from(index);
        // Safe because self.desc is properly aligned, dereferenceable and initialised, and nothing
        // else reads or writes the descriptor during this block.
        unsafe {
            (*self.desc.as_ptr())[index] = self.desc_shadow[index].clone();
        }
    }
}

impl<H: Hal, const SIZE: usize> PackedQueue<H, SIZE> {
    /// Add buffers to the virtqueue, return a token.
    ///
    /// Ref: linux virtio_ring.c virtqueue_add
    /// Ref: Section 2.7.13
    ///
    /// # Safety
    ///
    /// The input and output buffers must remain valid and not be accessed until a call to
    /// `pop_used` with the returned token succeeds.
    pub unsafe fn add<'a, 'b>(
        &mut self,
        inputs: &'a [&'b [u8]],
        outputs: &'a mut [&'b mut [u8]],
    ) -> Result<u16> {
        if inputs.is_empty() && outputs.is_empty() {
            return Err(Error::InvalidParam);
        }

        let desc_nr_needed = inputs.len() + outputs.len();
        if self.indirect_desc {
            if (SIZE - self.num_used as usize) < 1 || desc_nr_needed > SIZE {
                return Err(Error::QueueFull);
            }
        } else {
            if desc_nr_needed + self.num_used as usize > SIZE {
                return Err(Error::QueueFull);
            }
        }

        // allocate descriptors from free list
        let head = self.free_head;
        let id = head;
        let mut last = 0;
        let mut first_flags = DescFlags::empty();

        if self.indirect_desc && desc_nr_needed > 1 {
            let size_indirect_descs =
                size_of::<Descriptor>() * (inputs.len() + outputs.len()) as usize;
            let indirect_descs_dma =
                Dma::<H>::new(pages(size_indirect_descs), BufferDirection::DriverToDevice)?;
            let indirect_descs = nonnull_slice_from_raw_parts(
                indirect_descs_dma.vaddr(0).cast::<Descriptor>(),
                size_indirect_descs,
            );

            self.indirect_desc_vec[id as usize] = Some(indirect_descs_dma);
            let mut index = 0;
            for (buffer, direction) in InputOutputIter::new(inputs, outputs) {
                // Write to desc_shadow then copy.
                let mut desc = Descriptor::new();
                // let flag = self.avail_used_flags;
                let flag = DescFlags::empty();

                desc.set_buf::<H>(buffer, direction, flag);
                unsafe {
                    (*indirect_descs.as_ptr())[index] = desc;
                }
                index += 1;
            }
            let indirect_descs = unsafe {
                core::slice::from_raw_parts(
                    indirect_descs.as_ptr() as *const u8,
                    size_indirect_descs,
                )
            };
            let desc = &mut self.desc_shadow[usize::from(self.free_head)];
            desc.set_buf::<H>(
                indirect_descs.into(),
                BufferDirection::DriverToDevice,
                DescFlags::empty(),
            );
            last = self.free_head;
            self.free_head += 1;
            first_flags |= self.avail_used_flags;
            first_flags |= DescFlags::VIRTQ_DESC_F_INDIRECT;

            if self.free_head == SIZE as u16 {
                self.free_head = 0;
                self.avail_wrap_count ^= true;
                self.avail_used_flags ^=
                    DescFlags::VIRTQ_DESC_F_AVAIL | DescFlags::VIRTQ_DESC_F_USED;
            }
            self.write_desc(last);
            self.num_used += 1;
        } else {
            // A buffer consists of zero or more device-readable physically-contiguous elements followed by zero or more physically-contiguous device-writable elements (each has at least one element).
            for (buffer, direction) in InputOutputIter::new(inputs, outputs) {
                // Write to desc_shadow then copy.
                let mut flags = DescFlags::VIRTQ_DESC_F_NEXT;
                let desc = &mut self.desc_shadow[usize::from(self.free_head)];
                if head != self.free_head {
                    flags |= self.avail_used_flags;
                } else {
                    first_flags |= self.avail_used_flags;
                }
                desc.set_buf::<H>(buffer, direction, flags);
                last = self.free_head;
                self.free_head += 1;

                if self.free_head == SIZE as u16 {
                    self.free_head = 0;
                    self.avail_wrap_count ^= true;
                    self.avail_used_flags ^=
                        DescFlags::VIRTQ_DESC_F_AVAIL | DescFlags::VIRTQ_DESC_F_USED;
                }
                self.write_desc(last);
            }
            self.num_used += (inputs.len() + outputs.len()) as u16;
        }
        // set last_elem.next = NULL
        // 将last desc_shadow 的flag中的NEXT位置为0，然后往desc中写一遍
        self.desc_shadow[usize::from(last)].id = id;
        self.desc_shadow[usize::from(last)]
            .flags
            .remove(DescFlags::VIRTQ_DESC_F_NEXT);
        self.write_desc(last);
        self.desc_shadow[usize::from(id)].flags.insert(first_flags);

        // Write barrier so that device sees changes to descriptor table and available ring before
        // change to available index.
        // The driver performs a suitable memory barrier to ensure the device sees the updated descriptor table and available ring before the next step.
        //
        // Ref: Section 2.7.13
        fence(Ordering::SeqCst);
        self.write_desc(id);

        // Write barrier so that device can see change to available index after this method returns.
        // The driver performs a suitable memory barrier to ensure that it updates the idx field before checking for notification suppression.
        fence(Ordering::SeqCst);

        Ok(id)
    }

    /// Add the given buffers to the virtqueue, notifies the device, blocks until the device uses
    /// them, then pops them.
    ///
    /// This assumes that the device isn't processing any other buffers at the same time.
    pub fn add_notify_wait_pop<'a>(
        &mut self,
        inputs: &'a [&'a [u8]],
        outputs: &'a mut [&'a mut [u8]],
        transport: &mut impl Transport,
        support_event: bool,
    ) -> Result<u32> {
        // Safe because we don't return until the same token has been popped, so the buffers remain
        // valid and are not otherwise accessed until then.

        let token = unsafe { self.add(inputs, outputs) }?;

        // // Notify the queue.
        if self.should_notify(support_event) {
            transport.notify(self.queue_idx);
        }

        // Wait until there is at least one element in the used ring.
        while !self.can_pop() {
            spin_loop();
        }

        // Safe because these are the same buffers as we passed to `add` above and they are still
        // valid.
        unsafe { self.pop_used(token, inputs, outputs) }
    }

    // TODO: will be deleted in the further (this method does not support event)
    /// Add the given buffers to the virtqueue, notifies the device, blocks until the device uses
    /// them, then pops them.
    ///
    /// This assumes that the device isn't processing any other buffers at the same time.
    pub fn add_notify_wait_pop_old<'a>(
        &mut self,
        inputs: &'a [&'a [u8]],
        outputs: &'a mut [&'a mut [u8]],
        transport: &mut impl Transport,
    ) -> Result<u32> {
        // Safe because we don't return until the same token has been popped, so the buffers remain
        // valid and are not otherwise accessed until then.

        let token = unsafe { self.add(inputs, outputs) }?;

        // // Notify the queue.
        if self.should_notify(false) {
            transport.notify(self.queue_idx);
        }

        // Wait until there is at least one element in the used ring.
        while !self.can_pop() {
            spin_loop();
        }

        // Safe because these are the same buffers as we passed to `add` above and they are still
        // valid.
        unsafe { self.pop_used(token, inputs, outputs) }
    }

    // TODO: need modify 
    /// Returns whether the driver should notify the device after adding a new buffer to the
    /// virtqueue.
    ///
    /// Ref: virtio_ring.c virtqueue_kick_prepare_split
    /// This will be false if the device has supressed notifications.
    pub fn should_notify(&self, support_event: bool) -> bool {
        // Read barrier, so we read a fresh value from the device.
        fence(Ordering::SeqCst);

        // Safe because self.used points to a valid, aligned, initialised, dereferenceable, readable
        // instance of UsedRing.
        let flags = unsafe { (*self.device_event_suppression.as_ptr()).flags };
        let off_wrap = unsafe { (*self.device_event_suppression.as_ptr()).off_wrap };
        if flags != PackedQueueFlag::RING_EVENT_FLAGS_DESC.bits() {
            flags != PackedQueueFlag::RING_EVENT_FLAGS_DISABLE.bits()
        } else {
            let event_offset = off_wrap & ((1 << 15) - 1);
            let event_wrap_counter = off_wrap & (1 << 15);
            
            false
        }

    }

    /// Returns whether the driver should notify the device after adding a new buffer to the
    /// virtqueue.
    ///
    /// Ref: virtio_ring.c virtqueue_kick_prepare_split
    /// This will be false if the device has supressed notifications.
    pub fn should_notify_old(&self) -> bool {
        // Read barrier, so we read a fresh value from the device.
        fence(Ordering::SeqCst);

        // Safe because self.used points to a valid, aligned, initialised, dereferenceable, readable
        // instance of UsedRing.
        unsafe { (*self.device_event_suppression.as_ptr()).flags & 0x0001 == 0 }
    }

    /// If the given token is next on the device used queue, pops it and returns the total buffer
    /// length which was used (written) by the device.
    ///
    /// Ref: linux virtio_ring.c virtqueue_get_buf_ctx
    ///
    /// # Safety
    ///
    /// The buffers in `inputs` and `outputs` must match the set of buffers originally added to the
    /// queue by `add` when it returned the token being passed in here.
    pub unsafe fn pop_used<'a>(
        &mut self,
        token: u16,
        inputs: &'a [&'a [u8]],
        outputs: &'a mut [&'a mut [u8]],
    ) -> Result<u32> {
        if !self.can_pop() {
            return Err(Error::NotReady);
        }
        // Read barrier not necessary, as can_pop already has one.

        // Get the index of the start of the descriptor chain for the next element in the used ring.
        let index = token;
        let len;

        // Safe because the caller ensures the buffers are valid and match the descriptor.
        len = unsafe {
            self.recycle_descriptors(index, inputs, outputs)
        };
        if self.indirect_desc {
            self.indirect_desc_vec[index as usize] = None;
        }
        // self.last_used_idx = self.last_used_idx.wrapping_add(1);

        Ok(len as u32)
    }

    /// queue by `add` when it returned the token being passed in here.
    pub unsafe fn pop_used_async<'a>(&mut self, token: u16) -> Result<u32> {
        if !self.can_pop() {
            return Err(Error::NotReady);
        }
        // Read barrier not necessary, as can_pop already has one.

        // Get the index of the start of the descriptor chain for the next element in the used ring.
        let index: u16 = token;
        let len;

        // Safe because the caller ensures the buffers are valid and match the descriptor.
        len = unsafe {
            self.recycle_descriptors_sync(index)
        };
        // self.last_used_idx = self.last_used_idx.wrapping_add(1);

        Ok(len as u32)
    }

    /// Returns the descriptor index (a.k.a. token) of the next used element without popping it, or
    /// `None` if the used ring is empty.
    fn peek_used(&self) -> Option<u16> {
        if self.can_pop() {
            let last_used_slot = self.last_used_idx;
            // Safe because self.used points to a valid, aligned, initialised, dereferenceable,
            // readable instance of UsedRing.
            Some(unsafe { (*self.desc.as_ptr())[last_used_slot as usize].id as u16 })
        } else {
            None
        }
    }

    /// Returns whether there is a used element that can be popped.
    pub fn can_pop(&self) -> bool {
        // Read barrier, so we read a fresh value from the device.
        fence(Ordering::SeqCst);

        // Safe because self.used points to a valid, aligned, initialised, dereferenceable, readable
        // instance of UsedRing.
        let next_used = self.last_used_idx as usize;
        let avail =
            unsafe { (*self.desc.as_ptr())[next_used].flags & DescFlags::VIRTQ_DESC_F_AVAIL };
        let used = unsafe { (*self.desc.as_ptr())[next_used].flags & DescFlags::VIRTQ_DESC_F_USED };
        (avail.is_empty() ^ self.used_wrap_count) && (used.is_empty() ^ self.used_wrap_count)
    }

    fn last_used_idx(&self) -> u16 {
        self.last_used_idx & (SIZE as u16 - 1)
    }
    /// Returns the number of free descriptors.
    fn available_desc(&self) -> usize {
        SIZE - self.num_used as usize
    }
}

// bitflags! {
//     /// Descriptor flags
//     ///
//     /// Ref: Section 2.7.5 The Virtqueue Descriptor Table
//     #[derive(Copy, Clone, Debug, Default, Eq, FromBytes, PartialEq)]
//     struct DescFlags: u16 {
//         /// This marks a buffer as continuing via the next field.
//         const VIRTQ_DESC_F_NEXT = 1;
//         /// This marks a buffer as write-only (otherwise read-only).
//         const VIRTQ_DESC_F_WRITE = 1 << 1;
//         /// This means the buffer contains a list of buffer descriptors.
//         const VIRTQ_DESC_F_INDIRECT = 1 << 2;

//         ///
//         /// Mark a descriptor as available or used in packed ring.
//         /// Notice: they are defined as shifts instead of shifted values.
//         ///
//         const VIRTQ_DESC_F_AVAIL = 1 << 7;
//         const VIRTQ_DESC_F_USED = 1 << 15;
//     }
// }

/// Descriptor flags
#[derive(Copy, Clone, Debug, Default, Eq, FromBytes, PartialEq)]
#[repr(transparent)]
struct DescFlags(u16);

bitflags! {
    impl DescFlags: u16 {
        /// This marks a buffer as continuing via the next field.
        const VIRTQ_DESC_F_NEXT = 1;
        /// This marks a buffer as write-only (otherwise read-only).
        const VIRTQ_DESC_F_WRITE = 1 << 1;
        /// This means the buffer contains a list of buffer descriptors.
        const VIRTQ_DESC_F_INDIRECT = 1 << 2;

        ///
        /// Mark a descriptor as available or used in packed ring.
        /// Notice: they are defined as shifts instead of shifted values.
        ///
        const VIRTQ_DESC_F_AVAIL = 1 << 7;
        const VIRTQ_DESC_F_USED = 1 << 15;
    }
}

#[derive(Clone, Debug, FromBytes)]
pub(crate) struct Descriptor {
    /// Buffer Address
    addr: u64,
    /// Buffer Length
    len: u32,
    /// Buffer ID
    id: u16,
    /// The flags depending on descriptor type
    flags: DescFlags,
}

impl Descriptor {
    /// Sets the buffer address, length and flags, and shares it with the device.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the buffer lives at least as long as the descriptor is active.
    ///
    /// Ref: Section 2.7.13.1
    unsafe fn set_buf<H: Hal>(
        &mut self,
        buf: NonNull<[u8]>,
        direction: BufferDirection,
        extra_flags: DescFlags,
    ) {
        self.addr = H::share(buf, direction) as u64;
        self.len = buf.len() as u32;

        // If buffer is device-writable, set d.flags to VIRTQ_DESC_F_WRITE, otherwise 0.
        self.flags = extra_flags
            | match direction {
                BufferDirection::DriverToDevice => DescFlags::empty(),
                BufferDirection::DeviceToDriver => DescFlags::VIRTQ_DESC_F_WRITE,
                BufferDirection::Both => {
                    panic!("Buffer passed to device should never use BufferDirection::Both.")
                }
            };
    }

    fn new() -> Self {
        Self {
            addr: 0,
            len: 0,
            id: 0,
            flags: DescFlags::empty(),
        }
    }

    /// Sets the buffer address and length to 0.
    ///
    /// This must only be called once the device has finished using the descriptor.
    fn unset_buf(&mut self) {
        self.addr = 0;
        self.len = 0;
        self.id = 0;
    }
}

#[derive(Debug)]
struct PvirtqEventSuppress {
    /// Descriptor Ring Change Event Offset/Wrap Counter.
    off_wrap: u16,
    /// Descriptor Ring Change Event Flags.
    flags: u16,
}

/// The inner layout of a VirtQueue.
///
/// Ref: 2.6 Split Virtqueues
#[derive(Debug)]
struct PackedQueueLayout<H: Hal> {
    /// The whole region used for the communication between device and driver.
    whole_dma: Dma<H>,
    /// The region used for the desc area.
    device_event_offset: usize,
    /// The offset from the start of the `driver_to_device_dma` region to the driver area
    /// (available ring).
    driver_event_offset: usize,
}

impl<H: Hal> PackedQueueLayout<H> {
    /// Allocates separate DMA regions for the the different parts of the virtqueue, as supported by
    /// non-legacy interfaces.
    ///
    /// This is preferred over `allocate_legacy` where possible as it reduces memory fragmentation
    /// and allows the HAL to know which DMA regions are used in which direction.
    fn allocate(queue_size: u16) -> Result<Self> {
        let (desc, device_event, driver_event) = queue_part_sizes(queue_size);
        let whole_dma = Dma::new(
            pages(desc + device_event + driver_event),
            BufferDirection::DriverToDevice,
        )?;
        Ok(Self {
            whole_dma,
            device_event_offset: desc,
            driver_event_offset: desc + device_event,
        })
    }

    /// Returns the physical address of the descriptor area.
    fn descriptors_paddr(&self) -> PhysAddr {
        self.whole_dma.paddr()
    }

    /// Returns a pointer to the descriptor table (in the descriptor area).
    fn descriptors_vaddr(&self) -> NonNull<u8> {
        self.whole_dma.vaddr(0)
    }

    /// Returns the physical address of the driver area.
    fn driver_area_paddr(&self) -> PhysAddr {
        self.whole_dma.paddr() + self.device_event_offset
    }

    /// Returns a pointer to the driver event suppression structure (in the driver area).
    fn driver_event_suppression_vaddr(&self) -> NonNull<u8> {
        self.whole_dma.vaddr(self.device_event_offset)
    }

    /// Returns the physical address of the device area.
    fn device_area_paddr(&self) -> PhysAddr {
        self.whole_dma.paddr() + self.driver_event_offset
    }

    /// Returns a pointer to the device event suppression (in the driver area).
    fn device_event_suppression_vaddr(&self) -> NonNull<u8> {
        self.whole_dma.vaddr(self.driver_event_offset)
    }
}

/// Returns the size in bytes of the descriptor table, available ring and used ring for a given
/// queue size.
///
/// Ref: 2.6 Split Virtqueues
fn queue_part_sizes(queue_size: u16) -> (usize, usize, usize) {
    assert!(
        queue_size.is_power_of_two(),
        "queue size should be a power of 2"
    );
    let desc = size_of::<Descriptor>() * queue_size as usize;
    let device_event = size_of::<PvirtqEventSuppress>();
    let driver_event = size_of::<PvirtqEventSuppress>();
    (desc, device_event, driver_event)
}

bitflags! {
    struct PackedQueueFlag: u16 {
        const RING_EVENT_FLAGS_ENABLE = 0;
        const RING_EVENT_FLAGS_DISABLE = 1;
        const RING_EVENT_FLAGS_DESC = 2;
    }
}

struct InputOutputIter<'a, 'b> {
    inputs: &'a [&'b [u8]],
    outputs: &'a mut [&'b mut [u8]],
}

impl<'a, 'b> InputOutputIter<'a, 'b> {
    fn new(inputs: &'a [&'b [u8]], outputs: &'a mut [&'b mut [u8]]) -> Self {
        Self { inputs, outputs }
    }
}

impl<'a, 'b> Iterator for InputOutputIter<'a, 'b> {
    type Item = (NonNull<[u8]>, BufferDirection);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(input) = take_first(&mut self.inputs) {
            Some(((*input).into(), BufferDirection::DriverToDevice))
        } else {
            let output = take_first_mut(&mut self.outputs)?;
            Some(((*output).into(), BufferDirection::DeviceToDriver))
        }
    }
}

// TODO: Use `slice::take_first` once it is stable
// (https://github.com/rust-lang/rust/issues/62280).
fn take_first<'a, T>(slice: &mut &'a [T]) -> Option<&'a T> {
    let (first, rem) = slice.split_first()?;
    *slice = rem;
    Some(first)
}

// TODO: Use `slice::take_first_mut` once it is stable
// (https://github.com/rust-lang/rust/issues/62280).
fn take_first_mut<'a, T>(slice: &mut &'a mut [T]) -> Option<&'a mut T> {
    let (first, rem) = take(slice).split_first_mut()?;
    *slice = rem;
    Some(first)
}
