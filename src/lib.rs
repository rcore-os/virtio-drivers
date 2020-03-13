//! VirtIO guest drivers.

#![no_std]
#![deny(unused_must_use, missing_docs)]

#[macro_use]
extern crate log;

mod blk;
mod gpu;
mod header;
mod queue;

pub use self::blk::VirtIOBlk;
pub use self::gpu::VirtIOGpu;
pub use self::header::*;

const PAGE_SIZE: usize = 0x1000;

type VirtAddr = usize;
type PhysAddr = usize;

fn alloc_dma(pages: usize) -> Result<(VirtAddr, PhysAddr)> {
    let (vaddr, paddr) = unsafe { virtio_alloc_dma(pages) };
    if vaddr == 0 {
        Err(Error::DmaError)
    } else {
        Ok((vaddr, paddr))
    }
}

fn dealloc_dma(paddr: PhysAddr, pages: usize) -> Result {
    let ok = unsafe { virtio_dealloc_dma(paddr, pages) };
    if ok {
        Ok(())
    } else {
        Err(Error::DmaError)
    }
}

fn phys_to_virt(paddr: PhysAddr) -> VirtAddr {
    unsafe { virtio_phys_to_virt(paddr) }
}

fn virt_to_phys(vaddr: VirtAddr) -> PhysAddr {
    unsafe { virtio_virt_to_phys(vaddr) }
}

extern "C" {
    fn virtio_alloc_dma(pages: usize) -> (VirtAddr, PhysAddr);
    fn virtio_dealloc_dma(paddr: PhysAddr, pages: usize) -> bool;
    fn virtio_phys_to_virt(paddr: PhysAddr) -> VirtAddr;
    fn virtio_virt_to_phys(vaddr: VirtAddr) -> PhysAddr;
}

/// The type returned by driver methods.
pub type Result<T = ()> = core::result::Result<T, Error>;

// pub struct Error {
//     kind: ErrorKind,
//     reason: &'static str,
// }

/// The error type of VirtIO drivers.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    /// The buffer is too small.
    BufferTooSmall,
    /// The device is not ready.
    NotReady,
    /// The queue is already in use.
    AlreadyUsed,
    /// Invalid parameter.
    InvalidParam,
    /// Failed to alloc DMA memory.
    DmaError,
    /// I/O Error
    IoError,
}

/// Align `size` up to a page.
fn align_up(size: usize) -> usize {
    (size + PAGE_SIZE) & !(PAGE_SIZE - 1)
}

/// Pages of `size`.
fn pages(size: usize) -> usize {
    (size + PAGE_SIZE - 1) / PAGE_SIZE
}
