//! Drivers for specific VirtIO devices.

pub mod blk;
pub mod console;
pub mod gpu;
#[cfg(feature = "alloc")]
pub mod input;
pub mod net;
