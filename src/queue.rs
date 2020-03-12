use core::mem::size_of;
use core::slice;
use core::sync::atomic::{fence, Ordering};

use super::*;
use crate::header::VirtIOHeader;
use bitflags::*;

use volatile::Volatile;

/// The mechanism for bulk data transport on virtio devices.
///
/// Each device can have zero or more virtqueues.
#[repr(C)]
pub struct VirtQueue<'a> {
    /// Descriptor table
    desc: &'a mut [Descriptor],
    /// Available ring
    avail: &'a mut AvailRing,
    /// Used ring
    used: &'a mut UsedRing,
    /// Pages of DMA region
    pages: usize,

    /// The index of queue
    queue_idx: u32,
    /// The size of queue
    queue_size: u16,
    /// The number of used queues.
    num_used: u16,
    /// The head desc index of the free list.
    free_head: u16,
    avail_idx: u16,
    last_used_idx: u16,
}

impl VirtQueue<'_> {
    /// Create a new VirtQueue.
    pub fn new(header: &mut VirtIOHeader, idx: usize, size: u16) -> Result<Self> {
        if header.queue_used(idx as u32) {
            return Err(Error::AlreadyUsed);
        }
        if !size.is_power_of_two() || header.max_queue_size() < size as u32 {
            return Err(Error::InvalidParam);
        }
        let layout = VirtQueueLayout::new(size);
        let pages = layout.size / PAGE_SIZE;
        // alloc continuous pages
        let (vaddr, paddr) = alloc_dma(pages)?;

        header.queue_set(
            idx as u32,
            size as u32,
            PAGE_SIZE as u32,
            (paddr as u32) >> 12,
        );

        let desc = unsafe { slice::from_raw_parts_mut(vaddr as *mut Descriptor, size as usize) };
        let avail = unsafe { &mut *((vaddr + layout.avail_offset) as *mut AvailRing) };
        let used = unsafe { &mut *((vaddr + layout.used_offset) as *mut UsedRing) };

        // link descriptors together
        for i in 0..(size - 1) {
            desc[i as usize].next.write(i + 1);
        }

        Ok(VirtQueue {
            desc,
            avail,
            used,
            pages,
            queue_size: size,
            queue_idx: idx as u32,
            num_used: 0,
            free_head: 0,
            avail_idx: 0,
            last_used_idx: 0,
        })
    }

    /// Add buffers to the virtqueue.
    ///
    /// Ref: linux virtio_ring.c virtqueue_add
    pub fn add(&mut self, inputs: &[&[u8]], outputs: &[&mut [u8]]) -> Result {
        if inputs.is_empty() && outputs.is_empty() {
            return Ok(());
        }
        if inputs.len() + outputs.len() + self.num_used as usize > self.queue_size as usize {
            return Err(Error::BufferTooSmall);
        }

        // allocate descriptors from free list
        let head = self.free_head;
        let mut last = self.free_head;
        for input in inputs.iter() {
            let desc = &mut self.desc[self.free_head as usize];
            desc.set_buf(input);
            desc.flags.write(DescFlags::NEXT);
            last = self.free_head;
            self.free_head = desc.next.read();
        }
        for output in outputs.iter() {
            let desc = &mut self.desc[self.free_head as usize];
            desc.set_buf(output);
            desc.flags.write(DescFlags::NEXT | DescFlags::WRITE);
            last = self.free_head;
            self.free_head = desc.next.read();
        }
        // set last_elem.next = NULL
        {
            let desc = &mut self.desc[last as usize];
            let mut flags = desc.flags.read();
            flags.remove(DescFlags::NEXT);
            desc.flags.write(flags);
        }
        self.num_used += (inputs.len() + outputs.len()) as u16;

        let avail_slot = self.avail_idx & (self.queue_size - 1);
        self.avail.ring[avail_slot as usize].write(head);

        // write barrier
        fence(Ordering::SeqCst);

        // increase head of avail ring
        self.avail_idx = self.avail_idx.wrapping_add(1);
        self.avail.idx.write(self.avail_idx);
        Ok(())
    }

    ///
    pub fn can_get(&self) -> bool {
        self.last_used_idx != self.used.idx.read()
    }

    /// Recycle descriptors in the list specified by head.
    ///
    /// This will push all linked descriptors at the front of the free list.
    fn recycle_descriptors(&mut self, mut head: u16) {
        let origin_free_head = self.free_head;
        self.free_head = head;
        loop {
            let desc = &mut self.desc[head as usize];
            let flags = desc.flags.read();
            self.num_used -= 1;
            if flags.contains(DescFlags::NEXT) {
                head = desc.next.read();
            } else {
                desc.next.write(origin_free_head);
                return;
            }
        }
    }

    /// Get device used buffers.
    ///
    /// Ref: linux virtio_ring.c virtqueue_get_buf_ctx
    pub fn get(&mut self) -> Result<usize> {
        if !self.can_get() {
            return Err(Error::NotReady);
        }
        // read barrier
        fence(Ordering::SeqCst);

        let last_used_slot = self.last_used_idx & (self.queue_size - 1);
        let index = self.used.ring[last_used_slot as usize].id.read();
        let len = self.used.ring[last_used_slot as usize].len.read();

        self.recycle_descriptors(index as u16);
        self.last_used_idx = self.last_used_idx.wrapping_add(1);

        Ok(len as usize)
    }
}

impl Drop for VirtQueue<'_> {
    fn drop(&mut self) {
        dealloc_dma(virt_to_phys(self.desc.as_ptr() as _), self.pages).unwrap()
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
struct Descriptor {
    addr: Volatile<u64>,
    len: Volatile<u32>,
    flags: Volatile<DescFlags>,
    next: Volatile<u16>,
}

impl Descriptor {
    fn set_buf(&mut self, buf: &[u8]) {
        self.addr.write(virt_to_phys(buf.as_ptr() as usize) as u64);
        self.len.write(buf.len() as u32);
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
    flags: Volatile<u16>,
    /// A driver MUST NOT decrement the idx.
    idx: Volatile<u16>,
    ring: [Volatile<u16>; 32], // actual size: queue_size
    used_event: Volatile<u16>, // unused
}

/// The used ring is where the device returns buffers once it is done with them:
/// it is only written to by the device, and read by the driver.
#[repr(C)]
#[derive(Debug)]
struct UsedRing {
    flags: Volatile<u16>,
    idx: Volatile<u16>,
    ring: [UsedElem; 32],       // actual size: queue_size
    avail_event: Volatile<u16>, // unused
}

#[repr(C)]
#[derive(Debug)]
struct UsedElem {
    id: Volatile<u32>,
    len: Volatile<u32>,
}

/// Align `size` up to a page.
fn align_up(size: usize) -> usize {
    (size + PAGE_SIZE) & !(PAGE_SIZE - 1)
}
