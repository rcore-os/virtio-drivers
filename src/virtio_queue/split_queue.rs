extern crate alloc;

use crate::hal::{BufferDirection, Dma, Hal, PhysAddr};
use crate::transport::Transport;
use crate::{align_up, nonnull_slice_from_raw_parts, pages, Error, Result, PAGE_SIZE};
use bitflags::bitflags;
#[cfg(test)]
use core::cmp::min;
use core::hint::spin_loop;
use core::mem::{size_of, take};
#[cfg(test)]
use core::ptr;
use core::ptr::NonNull;
use core::sync::atomic::{fence, Ordering};
use zerocopy::FromBytes;

use alloc::vec::Vec;

/// The mechanism for bulk data transport on virtio devices.
///
/// Each device can have zero or more virtqueues.
///
/// * `SIZE`: The size of the queue. This is both the number of descriptors, and the number of slots in the available and used rings. Queue Size value is always a power of 2. The maximum Queue Size value is 32768. This value is specified in a bus-specific way.
#[derive(Debug)]
pub struct SplitQueue<H: Hal, const SIZE: usize> {
    /// DMA guard
    layout: VirtQueueLayout<H>,
    /// Descriptor table
    ///
    /// The device may be able to modify this, even though it's not supposed to, so we shouldn't
    /// trust values read back from it. Use `desc_shadow` instead to keep track of what we wrote to
    /// it.
    desc: NonNull<[Descriptor]>,

    indirect_desc_vec: Vec<Option<Dma<H>>>,
    /// Available ring: When the driver wants to send a buffer to the device, it fills in a slot in the descriptor table (or chains several together), and writes the descriptor index into the available ring. It then notifies the device.
    ///
    /// The device may be able to modify this, even though it's not supposed to, so we shouldn't
    /// trust values read back from it. The only field we need to read currently is `idx`, so we
    /// have `avail_idx` below to use instead.
    avail: NonNull<AvailRing<SIZE>>,
    /// Used ring: When the device has finished a buffer, it writes the descriptor index into the used ring, and sends a used buffer notification.
    used: NonNull<UsedRing<SIZE>>,

    /// The index of queue
    queue_idx: u16,
    /// The number of descriptors currently in use.
    num_used: u16,
    /// The head desc index of the free list.
    free_head: u16,
    /// Our trusted copy of `desc` that the device can't access.
    desc_shadow: [Descriptor; SIZE],
    /// Our trusted copy of `avail.idx`.
    avail_idx: u16,
    last_used_idx: u16,

    indirect_desc: bool,
}

impl<H: Hal, const SIZE: usize> SplitQueue<H, SIZE> {
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

        let layout = if transport.requires_legacy_layout() {
            VirtQueueLayout::allocate_legacy(size)?
        } else {
            VirtQueueLayout::allocate_flexible(size)?
        };

        transport.queue_set(
            idx,
            size.into(),
            layout.descriptors_paddr(),
            layout.driver_area_paddr(),
            layout.device_area_paddr(),
        );

        let desc =
            nonnull_slice_from_raw_parts(layout.descriptors_vaddr().cast::<Descriptor>(), SIZE);
        let avail = layout.avail_vaddr().cast();
        let used = layout.used_vaddr().cast();

        let mut desc_shadow: [Descriptor; SIZE] = FromBytes::new_zeroed();
        // Link descriptors together.
        for i in 0..(size - 1) {
            desc_shadow[i as usize].next = i + 1;
            // Safe because `desc` is properly aligned, dereferenceable, initialised, and the device
            // won't access the descriptors for the duration of this unsafe block.
            unsafe {
                (*desc.as_ptr())[i as usize].next = i + 1;
            }
        }

        let mut indrect_desc_vec = Vec::<Option<Dma<H>>>::with_capacity(SIZE);
        for _ in 0..SIZE {
            indrect_desc_vec.push(None);
        }

        Ok(SplitQueue {
            layout,
            desc,
            indirect_desc_vec: indrect_desc_vec,
            avail,
            used,
            queue_idx: idx,
            num_used: 0,
            free_head: 0,
            desc_shadow,
            avail_idx: 0,
            last_used_idx: 0,
            indirect_desc,
        })
    }
}
impl<H: Hal, const SIZE: usize> SplitQueue<H, SIZE> {
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
        let mut last = self.free_head;

        let size_indirect_descs = size_of::<Descriptor>() * (inputs.len() + outputs.len()) as usize;
        let indirect_descs_dma =
            Dma::<H>::new(pages(size_indirect_descs), BufferDirection::DriverToDevice)?;
        let indirect_descs = nonnull_slice_from_raw_parts(
            indirect_descs_dma.vaddr(0).cast::<Descriptor>(),
            size_indirect_descs,
        );

        self.indirect_desc_vec[head as usize] = Some(indirect_descs_dma);

        if self.indirect_desc {
            let mut index = 0;
            let mut desc = Descriptor::new();
            for (buffer, direction) in InputOutputIter::new(inputs, outputs) {
                // Write to desc_shadow then copy.
                desc = Descriptor::new();

                // let flag = self.avail_used_flags;
                desc.set_buf::<H>(buffer, direction, DescFlags::NEXT);
                desc.next = index + 1;

                unsafe {
                    (*indirect_descs.as_ptr())[index as usize] = desc.clone();
                }
                index += 1;
            }
            desc.flags.remove(DescFlags::NEXT);
            unsafe {
                (*indirect_descs.as_ptr())[(index - 1) as usize] = desc.clone();
            }

            let indirect_descs = unsafe {
                core::slice::from_raw_parts(
                    indirect_descs.as_ptr() as *const u8,
                    size_indirect_descs,
                )
            };
            let desc = &mut self.desc_shadow[usize::from(last)];
            desc.set_buf::<H>(
                indirect_descs.into(),
                BufferDirection::DriverToDevice,
                DescFlags::INDIRECT,
            );
            self.free_head = desc.next;

            self.write_desc(last);
        } else {
            // A buffer consists of zero or more device-readable physically-contiguous elements followed by zero or more physically-contiguous device-writable elements (each has at least one element).
            for (buffer, direction) in InputOutputIter::new(inputs, outputs) {
                // Write to desc_shadow then copy.
                let desc = &mut self.desc_shadow[usize::from(self.free_head)];
                desc.set_buf::<H>(buffer, direction, DescFlags::NEXT);
                last = self.free_head;
                self.free_head = desc.next;

                self.write_desc(last);
            }
        }

        // set last_elem.next = NULL
        // 将last desc_shadow 的flag中的NEXT位置为0，然后往desc中写一遍
        self.desc_shadow[usize::from(last)]
            .flags
            .remove(DescFlags::NEXT);
        self.write_desc(last);

        if self.indirect_desc {
            self.num_used += 1;
        } else {
            self.num_used += (inputs.len() + outputs.len()) as u16;
        }

        let avail_slot = self.avail_idx & (SIZE as u16 - 1);
        // Safe because self.avail is properly aligned, dereferenceable and initialised.
        unsafe {
            (*self.avail.as_ptr()).ring[avail_slot as usize] = head;
        }

        // Write barrier so that device sees changes to descriptor table and available ring before
        // change to available index.
        // The driver performs a suitable memory barrier to ensure the device sees the updated descriptor table and available ring before the next step.
        //
        // Ref: Section 2.7.13
        fence(Ordering::SeqCst);

        // increase head of avail ring
        self.avail_idx = self.avail_idx.wrapping_add(1);
        // Safe because self.avail is properly aligned, dereferenceable and initialised.
        unsafe {
            (*self.avail.as_ptr()).idx = self.avail_idx;
        }

        // Write barrier so that device can see change to available index after this method returns.
        // The driver performs a suitable memory barrier to ensure that it updates the idx field before checking for notification suppression.
        fence(Ordering::SeqCst);

        Ok(head)
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

        // Notify the queue.
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

        // Notify the queue.
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
        if support_event {
            unsafe { (*self.avail.as_ptr()).idx == (*self.used.as_ptr()).avail_event }
        } else {
            unsafe { ((*self.used.as_ptr()).flags & 0x0001) == 0 }
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

        unsafe { (*self.used.as_ptr()).flags & 0x0001 == 0 }
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

    /// Returns whether there is a used element that can be popped.
    pub fn can_pop(&self) -> bool {
        // Read barrier, so we read a fresh value from the device.
        fence(Ordering::SeqCst);

        // Safe because self.used points to a valid, aligned, initialised, dereferenceable, readable
        // instance of UsedRing.
        self.last_used_idx != unsafe { (*self.used.as_ptr()).idx }
    }

    /// Returns the descriptor index (a.k.a. token) of the next used element without popping it, or
    /// `None` if the used ring is empty.
    pub fn peek_used(&self) -> Option<u16> {
        if self.can_pop() {
            let last_used_slot = self.last_used_idx & (SIZE as u16 - 1);
            // Safe because self.used points to a valid, aligned, initialised, dereferenceable,
            // readable instance of UsedRing.
            Some(unsafe { (*self.used.as_ptr()).ring[last_used_slot as usize].id as u16 })
        } else {
            None
        }
    }

    /// Returns the number of free descriptors.
    pub fn available_desc(&self) -> usize {
        SIZE - self.num_used as usize
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
    ) {
        let original_free_head = self.free_head;
        self.free_head = head;
        let mut next = Some(head);

        if self.indirect_desc {
            let desc_index = next.expect("Descriptor chain was shorter than expected.");
            let desc = &mut self.desc_shadow[usize::from(desc_index)];
            desc.unset_buf();
            self.num_used -= 1;
            next = desc.next();
            if next.is_none() {
                desc.next = original_free_head;
            }

            self.write_desc(desc_index);
        } else {
            for (buffer, direction) in InputOutputIter::new(inputs, outputs) {
                let desc_index = next.expect("Descriptor chain was shorter than expected.");
                let desc = &mut self.desc_shadow[usize::from(desc_index)];

                let paddr = desc.addr;
                desc.unset_buf();
                self.num_used -= 1;
                next = desc.next();
                if next.is_none() {
                    desc.next = original_free_head;
                }

                self.write_desc(desc_index);

                // Safe because the caller ensures that the buffer is valid and matches the descriptor
                // from which we got `paddr`.
                unsafe {
                    // Unshare the buffer (and perhaps copy its contents back to the original buffer).
                    H::unshare(paddr as usize, buffer, direction);
                }
            }
        }

        if next.is_some() {
            panic!("Descriptor chain was longer than expected.");
        }
    }

    // TODO: will be deleted in the further
    /// The buffers in `inputs` and `outputs` must match the set of buffers originally added to the
    /// queue by `add`.
    unsafe fn recycle_descriptors_async<'a>(&mut self, head: u16) {
        let original_free_head = self.free_head;
        self.free_head = head;
        let mut next = Some(head);

        if self.indirect_desc {
            let desc_index = next.expect("Descriptor chain was shorter than expected.");
            let desc = &mut self.desc_shadow[usize::from(desc_index)];
            desc.unset_buf();
            self.num_used -= 1;
            next = desc.next();
            if next.is_none() {
                desc.next = original_free_head;
            }

            self.write_desc(desc_index);
        } else {
            loop {
                let desc_index = next.expect("Descriptor chain was shorter than expected.");
                let desc = &mut self.desc_shadow[usize::from(desc_index)];

                let paddr = desc.addr;
                desc.unset_buf();
                self.num_used -= 1;
                next = desc.next();
                if next.is_none() {
                    desc.next = original_free_head;
                }

                self.write_desc(desc_index);
                if next.is_none() {
                    break;
                }
            }
        }

        if next.is_some() {
            panic!("Descriptor chain was longer than expected.");
        }
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
        let last_used_slot = self.last_used_idx & (SIZE as u16 - 1);
        let index;
        let len;
        // Safe because self.used points to a valid, aligned, initialised, dereferenceable, readable
        // instance of UsedRing.
        unsafe {
            index = (*self.used.as_ptr()).ring[last_used_slot as usize].id as u16;
            len = (*self.used.as_ptr()).ring[last_used_slot as usize].len;
        }

        if index != token {
            // The device used a different descriptor chain to the one we were expecting.
            return Err(Error::WrongToken);
        }
        if self.indirect_desc {
            self.indirect_desc_vec.insert(index as usize, None);
        }

        // Safe because the caller ensures the buffers are valid and match the descriptor.
        unsafe {
            self.recycle_descriptors(index, inputs, outputs);
        }
        self.last_used_idx = self.last_used_idx.wrapping_add(1);

        Ok(len)
    }

    // TODO: will be deleted in the further
    /// If the given token is next on the device used queue, pops it and returns the total buffer
    /// length which was used (written) by the device.
    ///
    /// Ref: linux virtio_ring.c virtqueue_get_buf_ctx
    ///
    /// # Safety
    ///
    /// The buffers in `inputs` and `outputs` must match the set of buffers originally added to the
    /// queue by `add` when it returned the token being passed in here.
    pub unsafe fn pop_used_async<'a>(&mut self, token: u16) -> Result<u32> {
        if !self.can_pop() {
            return Err(Error::NotReady);
        }
        // Read barrier not necessary, as can_pop already has one.

        // Get the index of the start of the descriptor chain for the next element in the used ring.
        let last_used_slot = self.last_used_idx & (SIZE as u16 - 1);
        let index;
        let len;
        // Safe because self.used points to a valid, aligned, initialised, dereferenceable, readable
        // instance of UsedRing.
        unsafe {
            index = (*self.used.as_ptr()).ring[last_used_slot as usize].id as u16;
            len = (*self.used.as_ptr()).ring[last_used_slot as usize].len;
        }

        if index != token {
            // The device used a different descriptor chain to the one we were expecting.
            return Err(Error::WrongToken);
        }
        if self.indirect_desc {
            self.indirect_desc_vec.insert(index as usize, None);
        }

        // Safe because the caller ensures the buffers are valid and match the descriptor.
        unsafe {
            self.recycle_descriptors_async(index);
        }
        self.last_used_idx = self.last_used_idx.wrapping_add(1);

        Ok(len)
    }
}

/// The inner layout of a VirtQueue.
///
/// Ref: 2.6 Split Virtqueues
#[derive(Debug)]
enum VirtQueueLayout<H: Hal> {
    Legacy {
        dma: Dma<H>,
        avail_offset: usize,
        used_offset: usize,
    },
    Modern {
        /// The region used for the descriptor area and driver area.
        driver_to_device_dma: Dma<H>,
        /// The region used for the device area.
        device_to_driver_dma: Dma<H>,
        /// The offset from the start of the `driver_to_device_dma` region to the driver area
        /// (available ring).
        avail_offset: usize,
    },
}

impl<H: Hal> VirtQueueLayout<H> {
    /// Allocates a single DMA region containing all parts of the virtqueue, following the layout
    /// required by legacy interfaces.
    ///
    /// Ref: 2.6.2 Legacy Interfaces: A Note on Virtqueue Layout
    fn allocate_legacy(queue_size: u16) -> Result<Self> {
        let (desc, avail, used) = queue_part_sizes(queue_size);
        // 需要在Available Ring 和 Used Ring 之间插入一段 padding space以达到align这两段空间的目的
        let size = align_up(desc + avail) + align_up(used);
        // Allocate contiguous pages.
        let dma = Dma::new(size / PAGE_SIZE, BufferDirection::Both)?;
        Ok(Self::Legacy {
            dma,
            avail_offset: desc,
            used_offset: align_up(desc + avail),
        })
    }

    /// Allocates separate DMA regions for the the different parts of the virtqueue, as supported by
    /// non-legacy interfaces.
    ///
    /// This is preferred over `allocate_legacy` where possible as it reduces memory fragmentation
    /// and allows the HAL to know which DMA regions are used in which direction.
    fn allocate_flexible(queue_size: u16) -> Result<Self> {
        let (desc, avail, used) = queue_part_sizes(queue_size);
        let driver_to_device_dma = Dma::new(pages(desc + avail), BufferDirection::DriverToDevice)?;
        let device_to_driver_dma = Dma::new(pages(used), BufferDirection::DeviceToDriver)?;
        Ok(Self::Modern {
            driver_to_device_dma,
            device_to_driver_dma,
            avail_offset: desc,
        })
    }

    /// Returns the physical address of the descriptor area.
    fn descriptors_paddr(&self) -> PhysAddr {
        match self {
            Self::Legacy { dma, .. } => dma.paddr(),
            Self::Modern {
                driver_to_device_dma,
                ..
            } => driver_to_device_dma.paddr(),
        }
    }

    /// Returns a pointer to the descriptor table (in the descriptor area).
    fn descriptors_vaddr(&self) -> NonNull<u8> {
        match self {
            Self::Legacy { dma, .. } => dma.vaddr(0),
            Self::Modern {
                driver_to_device_dma,
                ..
            } => driver_to_device_dma.vaddr(0),
        }
    }

    /// Returns the physical address of the driver area.
    fn driver_area_paddr(&self) -> PhysAddr {
        match self {
            Self::Legacy {
                dma, avail_offset, ..
            } => dma.paddr() + avail_offset,
            Self::Modern {
                driver_to_device_dma,
                avail_offset,
                ..
            } => driver_to_device_dma.paddr() + avail_offset,
        }
    }

    /// Returns a pointer to the available ring (in the driver area).
    fn avail_vaddr(&self) -> NonNull<u8> {
        match self {
            Self::Legacy {
                dma, avail_offset, ..
            } => dma.vaddr(*avail_offset),
            Self::Modern {
                driver_to_device_dma,
                avail_offset,
                ..
            } => driver_to_device_dma.vaddr(*avail_offset),
        }
    }

    /// Returns the physical address of the device area.
    fn device_area_paddr(&self) -> PhysAddr {
        match self {
            Self::Legacy {
                used_offset, dma, ..
            } => dma.paddr() + used_offset,
            Self::Modern {
                device_to_driver_dma,
                ..
            } => device_to_driver_dma.paddr(),
        }
    }

    /// Returns a pointer to the used ring (in the driver area).
    fn used_vaddr(&self) -> NonNull<u8> {
        match self {
            Self::Legacy {
                dma, used_offset, ..
            } => dma.vaddr(*used_offset),
            Self::Modern {
                device_to_driver_dma,
                ..
            } => device_to_driver_dma.vaddr(0),
        }
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
    let queue_size = queue_size as usize;
    let desc = size_of::<Descriptor>() * queue_size;
    let avail = size_of::<u16>() * (3 + queue_size);
    let used = size_of::<u16>() * 3 + size_of::<UsedElem>() * queue_size;
    (desc, avail, used)
}

/// The descriptor table refers to the buffers the driver is using for the device.
/// Each descriptor describes a buffer which is read-only for the device (“device-readable”) or write-only for the device (“device-writable”),
///
/// Ref: 2.7.5 The Virtqueue Descriptor Table
#[repr(C, align(16))]
#[derive(Clone, Debug, FromBytes)]
pub(crate) struct Descriptor {
    /// a *physical* address
    addr: u64,

    len: u32,

    flags: DescFlags,
    /// Next field if flags & NEXT
    next: u16,
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
                BufferDirection::DeviceToDriver => DescFlags::WRITE,
                BufferDirection::DriverToDevice => DescFlags::empty(),
                BufferDirection::Both => {
                    panic!("Buffer passed to device should never use BufferDirection::Both.")
                }
            };
    }

    /// Sets the buffer address and length to 0.
    ///
    /// This must only be called once the device has finished using the descriptor.
    fn unset_buf(&mut self) {
        self.addr = 0;
        self.len = 0;
    }

    /// Returns the index of the next descriptor in the chain if the `NEXT` flag is set, or `None`
    /// if it is not (and thus this descriptor is the end of the chain).
    fn next(&self) -> Option<u16> {
        if self.flags.contains(DescFlags::NEXT) {
            Some(self.next)
        } else {
            None
        }
    }

    fn new() -> Self {
        Self {
            addr: 0,
            len: 0,
            flags: DescFlags::empty(),
            next: 0,
        }
    }
}


/// Descriptor flags
#[derive(Copy, Clone, Debug, Default, Eq, FromBytes, PartialEq)]
#[repr(transparent)]
struct DescFlags(u16);

bitflags! {
    impl DescFlags: u16 {
        /// This marks a buffer as continuing via the next field
        const NEXT = 1;
        /// This marks a buffer as device write-only (otherwise device read-only)
        const WRITE = 2;
        /// This means the buffer contains a list of buffer descriptors
        const INDIRECT = 4;
    }
}

/// The driver uses the available ring to offer buffers to the device:
/// each ring entry refers to the head of a descriptor chain.
/// It is only written by the driver and read by the device.
///
/// Ref: Section 2.7.6 The Virtqueue Available Ring
#[repr(C)]
#[derive(Debug)]
struct AvailRing<const SIZE: usize> {
    flags: u16,
    /// idx field indicates where the driver would put the next descriptor entry in the ring (modulo the queue size). This starts at 0, and increases.
    idx: u16,
    ring: [u16; SIZE],
    /// Only if VIRTIO_F_EVENT_IDX
    used_event: u16, // unused
}

/// The used ring is where the device returns buffers once it is done with them:
/// it is only written to by the device, and read by the driver.
///
/// Ref: Section 2.7.8 The Virtqueue Used Ring
#[repr(C)]
#[derive(Debug)]
struct UsedRing<const SIZE: usize> {
    flags: u16,
    /// idx field indicates where the device would put the next descriptor entry in the ring (modulo the queue size). This starts at 0, and increases.
    idx: u16,
    ring: [UsedElem; SIZE],

    /// Only if VIRTIO_F_EVENT_IDX
    avail_event: u16, // unused
}

#[repr(C)]
#[derive(Debug)]
struct UsedElem {
    /// id indicates the head entry of the descriptor chain describing the buffer (this matches an entry placed in the available ring by the guest earlier),
    id: u32,
    /// The number of bytes written into the device writable portion of the buffer described by the descriptor chain.
    len: u32,
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

/// Simulates the device reading from a VirtIO queue and writing a response back, for use in tests.
///
/// The fake device always uses descriptors in order.
#[cfg(test)]
pub(crate) fn fake_read_write_queue<const QUEUE_SIZE: usize>(
    descriptors: *const [Descriptor; QUEUE_SIZE],
    queue_driver_area: *const u8,
    queue_device_area: *mut u8,
    handler: impl FnOnce(Vec<u8>) -> Vec<u8>,
) {
    use core::{ops::Deref, slice};

    let available_ring = queue_driver_area as *const AvailRing<QUEUE_SIZE>;
    let used_ring = queue_device_area as *mut UsedRing<QUEUE_SIZE>;

    // Safe because the various pointers are properly aligned, dereferenceable, initialised, and
    // nothing else accesses them during this block.
    unsafe {
        // Make sure there is actually at least one descriptor available to read from.
        assert_ne!((*available_ring).idx, (*used_ring).idx);
        // The fake device always uses descriptors in order, like VIRTIO_F_IN_ORDER, so
        // `used_ring.idx` marks the next descriptor we should take from the available ring.
        let next_slot = (*used_ring).idx & (QUEUE_SIZE as u16 - 1);
        let head_descriptor_index = (*available_ring).ring[next_slot as usize];
        let mut descriptor = &(*descriptors)[head_descriptor_index as usize];

        // Loop through all input descriptors in the chain, reading data from them.
        let mut input = Vec::new();
        while !descriptor.flags.contains(DescFlags::WRITE) {
            input.extend_from_slice(slice::from_raw_parts(
                descriptor.addr as *const u8,
                descriptor.len as usize,
            ));

            if let Some(next) = descriptor.next() {
                descriptor = &(*descriptors)[next as usize];
            } else {
                break;
            }
        }
        let input_length = input.len();

        // Let the test handle the request.
        let output = handler(input);

        // Write the response to the remaining descriptors.
        let mut remaining_output = output.deref();
        if descriptor.flags.contains(DescFlags::WRITE) {
            loop {
                assert!(descriptor.flags.contains(DescFlags::WRITE));

                let length_to_write = min(remaining_output.len(), descriptor.len as usize);
                ptr::copy(
                    remaining_output.as_ptr(),
                    descriptor.addr as *mut u8,
                    length_to_write,
                );
                remaining_output = &remaining_output[length_to_write..];

                if let Some(next) = descriptor.next() {
                    descriptor = &(*descriptors)[next as usize];
                } else {
                    break;
                }
            }
        }
        assert_eq!(remaining_output.len(), 0);

        // Mark the buffer as used.
        (*used_ring).ring[next_slot as usize].id = head_descriptor_index as u32;
        (*used_ring).ring[next_slot as usize].len = (input_length + output.len()) as u32;
        (*used_ring).idx += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        hal::fake::FakeHal,
        transport::mmio::{MmioTransport, VirtIOHeader, MODERN_VERSION},
    };
    use core::ptr::NonNull;

    #[test]
    fn invalid_queue_size() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        // Size not a power of 2.
        assert_eq!(
            SplitQueue::<FakeHal, 3>::new(&mut transport, 0, false).unwrap_err(),
            Error::InvalidParam
        );
    }

    #[test]
    fn queue_too_big() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        assert_eq!(
            SplitQueue::<FakeHal, 8>::new(&mut transport, 0, false).unwrap_err(),
            Error::InvalidParam
        );
    }

    #[test]
    fn queue_already_used() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        SplitQueue::<FakeHal, 4>::new(&mut transport, 0, false).unwrap();
        assert_eq!(
            SplitQueue::<FakeHal, 4>::new(&mut transport, 0, false).unwrap_err(),
            Error::AlreadyUsed
        );
    }

    #[test]
    fn add_empty() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        let mut queue = SplitQueue::<FakeHal, 4>::new(&mut transport, 0, false).unwrap();
        assert_eq!(
            unsafe { queue.add(&[], &mut []) }.unwrap_err(),
            Error::InvalidParam
        );
    }

    #[test]
    fn add_too_many() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        let mut queue = SplitQueue::<FakeHal, 4>::new(&mut transport, 0, false).unwrap();
        assert_eq!(queue.available_desc(), 4);
        assert_eq!(
            unsafe { queue.add(&[&[], &[], &[]], &mut [&mut [], &mut []]) }.unwrap_err(),
            Error::QueueFull
        );
    }

    #[test]
    fn add_buffers() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        let mut queue = SplitQueue::<FakeHal, 4>::new(&mut transport, 0, false).unwrap();
        assert_eq!(queue.available_desc(), 4);

        // Add a buffer chain consisting of two device-readable parts followed by two
        // device-writable parts.
        let token = unsafe { queue.add(&[&[1, 2], &[3]], &mut [&mut [0, 0], &mut [0]]) }.unwrap();

        assert_eq!(queue.available_desc(), 0);
        assert!(!queue.can_pop());

        // Safe because the various parts of the queue are properly aligned, dereferenceable and
        // initialised, and nothing else is accessing them at the same time.
        unsafe {
            let first_descriptor_index = (*queue.avail.as_ptr()).ring[0];
            assert_eq!(first_descriptor_index, token);
            assert_eq!(
                (*queue.desc.as_ptr())[first_descriptor_index as usize].len,
                2
            );
            assert_eq!(
                (*queue.desc.as_ptr())[first_descriptor_index as usize].flags,
                DescFlags::NEXT
            );
            let second_descriptor_index =
                (*queue.desc.as_ptr())[first_descriptor_index as usize].next;
            assert_eq!(
                (*queue.desc.as_ptr())[second_descriptor_index as usize].len,
                1
            );
            assert_eq!(
                (*queue.desc.as_ptr())[second_descriptor_index as usize].flags,
                DescFlags::NEXT
            );
            let third_descriptor_index =
                (*queue.desc.as_ptr())[second_descriptor_index as usize].next;
            assert_eq!(
                (*queue.desc.as_ptr())[third_descriptor_index as usize].len,
                2
            );
            assert_eq!(
                (*queue.desc.as_ptr())[third_descriptor_index as usize].flags,
                DescFlags::NEXT | DescFlags::WRITE
            );
            let fourth_descriptor_index =
                (*queue.desc.as_ptr())[third_descriptor_index as usize].next;
            assert_eq!(
                (*queue.desc.as_ptr())[fourth_descriptor_index as usize].len,
                1
            );
            assert_eq!(
                (*queue.desc.as_ptr())[fourth_descriptor_index as usize].flags,
                DescFlags::WRITE
            );
        }
    }
}
