//! Drivers for specific VirtIO devices.

pub mod blk;
#[cfg(feature = "alloc")]
pub mod console;
#[cfg(feature = "alloc")]
pub mod gpu;
#[cfg(feature = "alloc")]
pub mod input;

pub mod net;

pub mod rng;

pub mod socket;
#[cfg(feature = "alloc")]
pub mod sound;
#[cfg(feature = "alloc")]
pub mod virtio_9p;

pub(crate) mod common;
