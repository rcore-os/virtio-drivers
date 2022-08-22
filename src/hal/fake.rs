//! Fake HAL implementation for tests.

use crate::{Hal, PhysAddr, VirtAddr, PAGE_SIZE};
use alloc::alloc::{alloc_zeroed, dealloc, handle_alloc_error};
use core::alloc::Layout;

#[derive(Debug)]
pub struct FakeHal;

/// Fake HAL implementation for use in unit tests.
impl Hal for FakeHal {
    fn dma_alloc(pages: usize) -> PhysAddr {
        assert_ne!(pages, 0);
        let layout = Layout::from_size_align(pages * PAGE_SIZE, PAGE_SIZE).unwrap();
        // Safe because the size and alignment of the layout are non-zero.
        let ptr = unsafe { alloc_zeroed(layout) };
        if ptr.is_null() {
            handle_alloc_error(layout);
        }
        ptr as PhysAddr
    }

    fn dma_dealloc(paddr: PhysAddr, pages: usize) -> i32 {
        assert_ne!(pages, 0);
        let layout = Layout::from_size_align(pages * PAGE_SIZE, PAGE_SIZE).unwrap();
        // Safe because the layout is the same as was used when the memory was allocated by
        // `dma_alloc` above.
        unsafe {
            dealloc(paddr as *mut u8, layout);
        }
        0
    }

    fn phys_to_virt(paddr: PhysAddr) -> VirtAddr {
        paddr
    }

    fn virt_to_phys(vaddr: VirtAddr) -> PhysAddr {
        vaddr
    }
}
