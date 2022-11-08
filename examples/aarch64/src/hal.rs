use core::{
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};
use lazy_static::lazy_static;
use log::trace;
use virtio_drivers::{BufferDirection, Hal, PhysAddr, VirtAddr, PAGE_SIZE};

extern "C" {
    static dma_region: u8;
}

lazy_static! {
    static ref DMA_PADDR: AtomicUsize =
        AtomicUsize::new(unsafe { &dma_region as *const u8 as usize });
}

pub struct HalImpl;

impl Hal for HalImpl {
    fn dma_alloc(pages: usize, _direction: BufferDirection) -> PhysAddr {
        let paddr = DMA_PADDR.fetch_add(PAGE_SIZE * pages, Ordering::SeqCst);
        trace!("alloc DMA: paddr={:#x}, pages={}", paddr, pages);
        paddr
    }

    fn dma_dealloc(paddr: PhysAddr, pages: usize) -> i32 {
        trace!("dealloc DMA: paddr={:#x}, pages={}", paddr, pages);
        0
    }

    fn phys_to_virt(paddr: PhysAddr) -> VirtAddr {
        paddr
    }

    fn share(buffer: NonNull<[u8]>, _direction: BufferDirection) -> PhysAddr {
        let vaddr = buffer.as_ptr() as *mut u8 as usize;
        // Nothing to do, as the host already has access to all memory.
        virt_to_phys(vaddr)
    }

    fn unshare(_paddr: PhysAddr, _buffer: NonNull<[u8]>, _direction: BufferDirection) {
        // Nothing to do, as the host already has access to all memory and we didn't copy the buffer
        // anywhere else.
    }
}

fn virt_to_phys(vaddr: VirtAddr) -> PhysAddr {
    vaddr
}
