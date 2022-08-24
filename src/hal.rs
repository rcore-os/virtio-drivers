#[cfg(test)]
pub mod fake;

use super::*;
use core::marker::PhantomData;

/// A virtual memory address in the address space of the program.
pub type VirtAddr = usize;

/// A physical address as used for virtio.
pub type PhysAddr = usize;

/// A region of contiguous physical memory used for DMA.
#[derive(Debug)]
pub struct DMA<H: Hal> {
    paddr: usize,
    pages: usize,
    _phantom: PhantomData<H>,
}

impl<H: Hal> DMA<H> {
    pub fn new(pages: usize) -> Result<Self> {
        let paddr = H::dma_alloc(pages);
        if paddr == 0 {
            return Err(Error::DmaError);
        }
        Ok(DMA {
            paddr,
            pages,
            _phantom: PhantomData::default(),
        })
    }

    pub fn paddr(&self) -> usize {
        self.paddr
    }

    pub fn vaddr(&self) -> usize {
        H::phys_to_virt(self.paddr)
    }

    /// Convert to a buffer
    pub unsafe fn as_buf(&self) -> &'static mut [u8] {
        core::slice::from_raw_parts_mut(self.vaddr() as _, PAGE_SIZE * self.pages as usize)
    }
}

impl<H: Hal> Drop for DMA<H> {
    fn drop(&mut self) {
        let err = H::dma_dealloc(self.paddr as usize, self.pages as usize);
        assert_eq!(err, 0, "failed to deallocate DMA");
    }
}

/// The interface which a particular hardware implementation must implement.
pub trait Hal {
    /// Allocates the given number of contiguous physical pages of DMA memory for virtio use.
    fn dma_alloc(pages: usize) -> PhysAddr;
    /// Deallocates the given contiguous physical DMA memory pages.
    fn dma_dealloc(paddr: PhysAddr, pages: usize) -> i32;
    /// Converts a physical address used for virtio to a virtual address which the program can
    /// access.
    fn phys_to_virt(paddr: PhysAddr) -> VirtAddr;
    /// Converts a virtual address which the program can access to the corresponding physical
    /// address to use for virtio.
    fn virt_to_phys(vaddr: VirtAddr) -> PhysAddr;
}
