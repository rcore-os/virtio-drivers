use core::sync::atomic::*;
use lazy_static::lazy_static;
use log::trace;
use virtio_drivers::{Hal, PhysAddr, VirtAddr};

extern "C" {
    fn end();
}

lazy_static! {
    static ref DMA_PADDR: AtomicUsize = AtomicUsize::new(end as usize);
}

pub struct HalImpl;

impl Hal for HalImpl {
    fn dma_alloc(pages: usize) -> PhysAddr {
        let paddr = DMA_PADDR.fetch_add(0x1000 * pages, Ordering::SeqCst);
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

    fn virt_to_phys(vaddr: VirtAddr) -> PhysAddr {
        vaddr
    }
}
