use core::sync::atomic::*;

static DMA_PADDR: AtomicUsize = AtomicUsize::new(0x80300000);

#[no_mangle]
extern "C" fn virtio_alloc_dma(pages: usize) -> (VirtAddr, PhysAddr) {
    let paddr = DMA_PADDR.fetch_add(0x1000 * pages, Ordering::SeqCst);
    trace!(
        "alloc DMA: vaddr={:#x}, paddr={:#x}, pages={}",
        paddr,
        paddr,
        pages
    );
    (paddr, paddr)
}

#[no_mangle]
extern "C" fn virtio_dealloc_dma(paddr: PhysAddr, pages: usize) -> bool {
    trace!("dealloc DMA: paddr={:#x}, pages={}", paddr, pages);
    true
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
