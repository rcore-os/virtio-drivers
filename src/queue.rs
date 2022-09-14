#[cfg(test)]
use core::cmp::min;
use core::mem::size_of;
use core::ptr::{self, addr_of_mut, NonNull};
use core::sync::atomic::{fence, Ordering};

use super::*;
use crate::transport::Transport;
use bitflags::*;

/// The mechanism for bulk data transport on virtio devices.
///
/// Each device can have zero or more virtqueues.
#[derive(Debug)]
pub struct VirtQueue<H: Hal> {
    /// DMA guard
    dma: DMA<H>,
    /// Descriptor table
    desc: NonNull<[Descriptor]>,
    /// Available ring
    avail: NonNull<AvailRing>,
    /// Used ring
    used: NonNull<UsedRing>,

    /// The index of queue
    queue_idx: u32,
    /// The size of the queue.
    ///
    /// This is both the number of descriptors, and the number of slots in the available and used
    /// rings.
    queue_size: u16,
    /// The number of used queues.
    num_used: u16,
    /// The head desc index of the free list.
    free_head: u16,
    avail_idx: u16,
    last_used_idx: u16,
}

impl<H: Hal> VirtQueue<H> {
    /// Create a new VirtQueue.
    pub fn new<T: Transport>(transport: &mut T, idx: usize, size: u16) -> Result<Self> {
        if transport.queue_used(idx as u32) {
            return Err(Error::AlreadyUsed);
        }
        if !size.is_power_of_two() || transport.max_queue_size() < size as u32 {
            return Err(Error::InvalidParam);
        }
        let layout = VirtQueueLayout::new(size);
        // Allocate contiguous pages.
        let dma = DMA::new(layout.size / PAGE_SIZE)?;

        transport.queue_set(
            idx as u32,
            size as u32,
            dma.paddr(),
            dma.paddr() + layout.avail_offset,
            dma.paddr() + layout.used_offset,
        );

        let desc = NonNull::new(ptr::slice_from_raw_parts_mut(
            dma.vaddr() as *mut Descriptor,
            size as usize,
        ))
        .unwrap();
        let avail = NonNull::new((dma.vaddr() + layout.avail_offset) as *mut AvailRing).unwrap();
        let used = NonNull::new((dma.vaddr() + layout.used_offset) as *mut UsedRing).unwrap();

        // Link descriptors together.
        for i in 0..(size - 1) {
            // Safe because `desc` is properly aligned, dereferenceable, initialised, and the device
            // won't access the descriptors for the duration of this unsafe block.
            unsafe {
                (*desc.as_ptr())[i as usize].next = i + 1;
            }
        }

        Ok(VirtQueue {
            dma,
            desc,
            avail,
            used,
            queue_size: size,
            queue_idx: idx as u32,
            num_used: 0,
            free_head: 0,
            avail_idx: 0,
            last_used_idx: 0,
        })
    }

    /// Add buffers to the virtqueue, return a token.
    ///
    /// Ref: linux virtio_ring.c virtqueue_add
    pub fn add(&mut self, inputs: &[&[u8]], outputs: &[&mut [u8]]) -> Result<u16> {
        if inputs.is_empty() && outputs.is_empty() {
            return Err(Error::InvalidParam);
        }
        if inputs.len() + outputs.len() + self.num_used as usize > self.queue_size as usize {
            return Err(Error::BufferTooSmall);
        }

        // allocate descriptors from free list
        let head = self.free_head;
        let mut last = self.free_head;

        // Safe because self.desc is properly aligned, dereferenceable and initialised, and nothing
        // else reads or writes the free descriptors during this block.
        unsafe {
            for input in inputs.iter() {
                let mut desc = self.desc_ptr(self.free_head);
                (*desc).set_buf::<H>(input);
                (*desc).flags = DescFlags::NEXT;
                last = self.free_head;
                self.free_head = (*desc).next;
            }
            for output in outputs.iter() {
                let desc = self.desc_ptr(self.free_head);
                (*desc).set_buf::<H>(output);
                (*desc).flags = DescFlags::NEXT | DescFlags::WRITE;
                last = self.free_head;
                self.free_head = (*desc).next;
            }

            // set last_elem.next = NULL
            (*self.desc_ptr(last)).flags.remove(DescFlags::NEXT);
        }
        self.num_used += (inputs.len() + outputs.len()) as u16;

        let avail_slot = self.avail_idx & (self.queue_size - 1);
        // Safe because self.avail is properly aligned, dereferenceable and initialised.
        unsafe {
            (*self.avail.as_ptr()).ring[avail_slot as usize] = head;
        }

        // Write barrier so that device sees changes to descriptor table and available ring before
        // change to available index.
        fence(Ordering::SeqCst);

        // increase head of avail ring
        self.avail_idx = self.avail_idx.wrapping_add(1);
        // Safe because self.avail is properly aligned, dereferenceable and initialised.
        unsafe {
            (*self.avail.as_ptr()).idx = self.avail_idx;
        }

        // Write barrier so that device can see change to available index after this method returns.
        fence(Ordering::SeqCst);

        Ok(head)
    }

    /// Returns a non-null pointer to the descriptor at the given index.
    fn desc_ptr(&mut self, index: u16) -> *mut Descriptor {
        // Safe because self.desc is properly aligned and dereferenceable.
        unsafe { addr_of_mut!((*self.desc.as_ptr())[index as usize]) }
    }

    /// Returns whether there is a used element that can be popped.
    pub fn can_pop(&self) -> bool {
        // Read barrier, so we read a fresh value from the device.
        fence(Ordering::SeqCst);

        // Safe because self.used points to a valid, aligned, initialised, dereferenceable, readable
        // instance of UsedRing.
        self.last_used_idx != unsafe { (*self.used.as_ptr()).idx }
    }

    /// Returns the number of free descriptors.
    pub fn available_desc(&self) -> usize {
        (self.queue_size - self.num_used) as usize
    }

    /// Recycle descriptors in the list specified by head.
    ///
    /// This will push all linked descriptors at the front of the free list.
    fn recycle_descriptors(&mut self, mut head: u16) {
        let original_free_head = self.free_head;
        self.free_head = head;
        loop {
            let desc = self.desc_ptr(head);
            // Safe because self.desc is properly aligned, dereferenceable and initialised, and
            // nothing else reads or writes the descriptor during this block.
            unsafe {
                let flags = (*desc).flags;
                self.num_used -= 1;
                if flags.contains(DescFlags::NEXT) {
                    head = (*desc).next;
                } else {
                    (*desc).next = original_free_head;
                    return;
                }
            }
        }
    }

    /// Get a token from device used buffers, return (token, len).
    ///
    /// Ref: linux virtio_ring.c virtqueue_get_buf_ctx
    pub fn pop_used(&mut self) -> Result<(u16, u32)> {
        if !self.can_pop() {
            return Err(Error::NotReady);
        }
        // read barrier
        fence(Ordering::SeqCst);

        let last_used_slot = self.last_used_idx & (self.queue_size - 1);
        let index;
        let len;
        // Safe because self.used points to a valid, aligned, initialised, dereferenceable, readable
        // instance of UsedRing.
        unsafe {
            index = (*self.used.as_ptr()).ring[last_used_slot as usize].id as u16;
            len = (*self.used.as_ptr()).ring[last_used_slot as usize].len;
        }

        self.recycle_descriptors(index);
        self.last_used_idx = self.last_used_idx.wrapping_add(1);

        Ok((index, len))
    }

    /// Return size of the queue.
    pub fn size(&self) -> u16 {
        self.queue_size
    }
}

/// The inner layout of a VirtQueue.
///
/// Ref: 2.6.2 Legacy Interfaces: A Note on Virtqueue Layout
struct VirtQueueLayout {
    avail_offset: usize,
    used_offset: usize,
    size: usize,
}

impl VirtQueueLayout {
    fn new(queue_size: u16) -> Self {
        assert!(
            queue_size.is_power_of_two(),
            "queue size should be a power of 2"
        );
        let queue_size = queue_size as usize;
        let desc = size_of::<Descriptor>() * queue_size;
        let avail = size_of::<u16>() * (3 + queue_size);
        let used = size_of::<u16>() * 3 + size_of::<UsedElem>() * queue_size;
        VirtQueueLayout {
            avail_offset: desc,
            used_offset: align_up(desc + avail),
            size: align_up(desc + avail) + align_up(used),
        }
    }
}

#[repr(C, align(16))]
#[derive(Debug)]
pub(crate) struct Descriptor {
    addr: u64,
    len: u32,
    flags: DescFlags,
    next: u16,
}

impl Descriptor {
    fn set_buf<H: Hal>(&mut self, buf: &[u8]) {
        self.addr = H::virt_to_phys(buf.as_ptr() as usize) as u64;
        self.len = buf.len() as u32;
    }
}

bitflags! {
    /// Descriptor flags
    struct DescFlags: u16 {
        const NEXT = 1;
        const WRITE = 2;
        const INDIRECT = 4;
    }
}

/// The driver uses the available ring to offer buffers to the device:
/// each ring entry refers to the head of a descriptor chain.
/// It is only written by the driver and read by the device.
#[repr(C)]
#[derive(Debug)]
struct AvailRing {
    flags: u16,
    /// A driver MUST NOT decrement the idx.
    idx: u16,
    ring: [u16; 32], // actual size: queue_size
    used_event: u16, // unused
}

/// The used ring is where the device returns buffers once it is done with them:
/// it is only written to by the device, and read by the driver.
#[repr(C)]
#[derive(Debug)]
struct UsedRing {
    flags: u16,
    idx: u16,
    ring: [UsedElem; 32], // actual size: queue_size
    avail_event: u16,     // unused
}

#[repr(C)]
#[derive(Debug)]
struct UsedElem {
    id: u32,
    len: u32,
}

/// Simulates the device writing to a VirtIO queue, for use in tests.
///
/// The fake device always uses descriptors in order.
#[cfg(test)]
pub(crate) fn fake_write_to_queue(
    queue_size: u16,
    receive_queue_descriptors: *const Descriptor,
    receive_queue_driver_area: VirtAddr,
    receive_queue_device_area: VirtAddr,
    data: &[u8],
) {
    let descriptors = ptr::slice_from_raw_parts(receive_queue_descriptors, queue_size as usize);
    let available_ring = receive_queue_driver_area as *const AvailRing;
    let used_ring = receive_queue_device_area as *mut UsedRing;
    // Safe because the various pointers are properly aligned, dereferenceable, initialised, and
    // nothing else accesses them during this block.
    unsafe {
        // Make sure there is actually at least one descriptor available to write to.
        assert_ne!((*available_ring).idx, (*used_ring).idx);
        // The fake device always uses descriptors in order, like VIRTIO_F_IN_ORDER, so
        // `used_ring.idx` marks the next descriptor we should take from the available ring.
        let next_slot = (*used_ring).idx & (queue_size - 1);
        let head_descriptor_index = (*available_ring).ring[next_slot as usize];
        let mut descriptor = &(*descriptors)[head_descriptor_index as usize];

        // Loop through all descriptors in the chain, writing data to them.
        let mut remaining_data = data;
        loop {
            // Check the buffer and write to it.
            let flags = descriptor.flags;
            assert!(flags.contains(DescFlags::WRITE));
            let buffer_length = descriptor.len as usize;
            let length_to_write = min(remaining_data.len(), buffer_length);
            ptr::copy(
                remaining_data.as_ptr(),
                descriptor.addr as *mut u8,
                length_to_write,
            );
            remaining_data = &remaining_data[length_to_write..];

            if flags.contains(DescFlags::NEXT) {
                let next = descriptor.next as usize;
                descriptor = &(*descriptors)[next];
            } else {
                assert_eq!(remaining_data.len(), 0);
                break;
            }
        }

        // Mark the buffer as used.
        (*used_ring).ring[next_slot as usize].id = head_descriptor_index as u32;
        (*used_ring).ring[next_slot as usize].len = data.len() as u32;
        (*used_ring).idx += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{hal::fake::FakeHal, transport::mmio::MODERN_VERSION};
    use core::ptr::NonNull;

    #[test]
    fn invalid_queue_size() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        // Size not a power of 2.
        assert_eq!(
            VirtQueue::<FakeHal>::new(&mut transport, 0, 3).unwrap_err(),
            Error::InvalidParam
        );
    }

    #[test]
    fn queue_too_big() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        assert_eq!(
            VirtQueue::<FakeHal>::new(&mut transport, 0, 5).unwrap_err(),
            Error::InvalidParam
        );
    }

    #[test]
    fn queue_already_used() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        VirtQueue::<FakeHal>::new(&mut transport, 0, 4).unwrap();
        assert_eq!(
            VirtQueue::<FakeHal>::new(&mut transport, 0, 4).unwrap_err(),
            Error::AlreadyUsed
        );
    }

    #[test]
    fn add_empty() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        let mut queue = VirtQueue::<FakeHal>::new(&mut transport, 0, 4).unwrap();
        assert_eq!(queue.add(&[], &[]).unwrap_err(), Error::InvalidParam);
    }

    #[test]
    fn add_too_big() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        let mut queue = VirtQueue::<FakeHal>::new(&mut transport, 0, 4).unwrap();
        assert_eq!(queue.available_desc(), 4);
        assert_eq!(
            queue
                .add(&[&[], &[], &[]], &[&mut [], &mut []])
                .unwrap_err(),
            Error::BufferTooSmall
        );
    }

    #[test]
    fn add_buffers() {
        let mut header = VirtIOHeader::make_fake_header(MODERN_VERSION, 1, 0, 0, 4);
        let mut transport = unsafe { MmioTransport::new(NonNull::from(&mut header)) }.unwrap();
        let mut queue = VirtQueue::<FakeHal>::new(&mut transport, 0, 4).unwrap();
        assert_eq!(queue.size(), 4);
        assert_eq!(queue.available_desc(), 4);

        // Add a buffer chain consisting of two device-readable parts followed by two
        // device-writable parts.
        let token = queue
            .add(&[&[1, 2], &[3]], &[&mut [0, 0], &mut [0]])
            .unwrap();

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
