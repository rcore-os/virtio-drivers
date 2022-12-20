//! VirtIO guest drivers.

#![cfg_attr(not(test), no_std)]
#![deny(unused_must_use, missing_docs)]
#![allow(clippy::identity_op)]
#![allow(dead_code)]

#[cfg(any(feature = "alloc", test))]
extern crate alloc;

mod device;
mod hal;
mod queue;
mod transport;
mod volatile;

pub use self::device::blk::{BlkReq, BlkResp, RespStatus, VirtIOBlk, SECTOR_SIZE};
pub use self::device::console::VirtIOConsole;
pub use self::device::gpu::VirtIOGpu;
#[cfg(feature = "alloc")]
pub use self::device::input::{InputConfigSelect, InputEvent, VirtIOInput};
pub use self::device::net::VirtIONet;
pub use self::hal::{Hal, PhysAddr, VirtAddr};
pub use self::transport::mmio::{MmioError, MmioTransport, MmioVersion, VirtIOHeader};
pub use self::transport::pci;
pub use self::transport::{DeviceStatus, DeviceType, Transport};

/// The page size in bytes supported by the library (4 KiB).
pub const PAGE_SIZE: usize = 0x1000;

/// The type returned by driver methods.
pub type Result<T = ()> = core::result::Result<T, Error>;

/// The error type of VirtIO drivers.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// There are not enough descriptors available in the virtqueue, try again later.
    QueueFull,
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
    /// The config space advertised by the device is smaller than the driver expected.
    ConfigSpaceTooSmall,
    /// The device doesn't have any config space, but the driver expects some.
    ConfigSpaceMissing,
}

/// Align `size` up to a page.
fn align_up(size: usize) -> usize {
    (size + PAGE_SIZE) & !(PAGE_SIZE - 1)
}

/// The number of pages required to store `size` bytes, rounded up to a whole number of pages.
fn pages(size: usize) -> usize {
    (size + PAGE_SIZE - 1) / PAGE_SIZE
}
