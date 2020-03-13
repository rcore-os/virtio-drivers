use core::sync::atomic::*;

static DMA_PADDR: AtomicUsize = AtomicUsize::new(0x80300000);

#[no_mangle]
extern "C" fn virtio_dma_alloc(pages: usize) -> PhysAddr {
    let paddr = DMA_PADDR.fetch_add(0x1000 * pages, Ordering::SeqCst);
    trace!("alloc DMA: paddr={:#x}, pages={}", paddr, pages);
    paddr
}

#[no_mangle]
extern "C" fn virtio_dma_dealloc(paddr: PhysAddr, pages: usize) -> i32 {
    trace!("dealloc DMA: paddr={:#x}, pages={}", paddr, pages);
    0
}

#[no_mangle]
extern "C" fn virtio_phys_to_virt(paddr: PhysAddr) -> VirtAddr {
    paddr
}

#[no_mangle]
extern "C" fn virtio_virt_to_phys(vaddr: VirtAddr) -> PhysAddr {
    vaddr
}

type VirtAddr = usize;
type PhysAddr = usize;
