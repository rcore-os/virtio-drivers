//! VirtIO guest drivers.

#![no_std]
#![deny(unused_must_use, missing_docs)]

#[macro_use]
extern crate log;

mod blk;
mod gpu;
mod hal;
mod header;
mod queue;

pub use self::blk::VirtIOBlk;
pub use self::gpu::VirtIOGpu;
pub use self::header::*;
use hal::*;

const PAGE_SIZE: usize = 0x1000;

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
