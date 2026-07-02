//! Drivers for specific VirtIO devices.

#[cfg(feature = "blk")]
pub mod blk;
#[cfg(all(feature = "alloc", feature = "console"))]
pub mod console;
#[cfg(all(feature = "alloc", feature = "gpu"))]
pub mod gpu;
#[cfg(all(feature = "alloc", feature = "input"))]
pub mod input;

#[cfg(feature = "net")]
pub mod net;

#[cfg(feature = "rng")]
pub mod rng;

#[cfg(feature = "rtc")]
pub mod rtc;

#[cfg(feature = "socket")]
pub mod socket;
#[cfg(all(feature = "alloc", feature = "sound"))]
pub mod sound;
#[cfg(all(feature = "alloc", feature = "virtio_9p"))]
pub mod virtio_9p;

pub mod common;
