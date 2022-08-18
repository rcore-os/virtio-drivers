//! VirtIO guest drivers.

#![no_std]
#![deny(unused_must_use, missing_docs)]
#![allow(clippy::identity_op)]
#![allow(dead_code)]

extern crate alloc;

mod blk;
mod console;
mod gpu;
mod hal;
mod header;
mod input;
mod net;
mod queue;

pub use self::blk::{BlkResp, RespStatus, VirtIOBlk};
pub use self::console::VirtIOConsole;
pub use self::gpu::VirtIOGpu;
pub use self::hal::{Hal, PhysAddr, VirtAddr};
pub use self::header::*;
pub use self::input::{InputConfigSelect, InputEvent, VirtIOInput};
pub use self::net::VirtIONet;
use self::queue::VirtQueue;
use core::mem::size_of;
use hal::*;

/// The page size in bytes supported by the library (4 KiB).
const PAGE_SIZE: usize = 0x1000;

/// The type returned by driver methods.
pub type Result<T = ()> = core::result::Result<T, Error>;

/// The error type of VirtIO drivers.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
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

/// The number of pages required to store `size` bytes, rounded up to a whole number of pages.
fn pages(size: usize) -> usize {
    (size + PAGE_SIZE - 1) / PAGE_SIZE
}

/// Convert a struct into a byte buffer.
unsafe trait AsBuf: Sized {
    fn as_buf(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self as *const _ as _, size_of::<Self>()) }
    }
    fn as_buf_mut(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self as *mut _ as _, size_of::<Self>()) }
    }
}
