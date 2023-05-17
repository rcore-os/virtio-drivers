//! This module implements the virtio vsock device.

mod error;
mod protocol;
#[cfg(feature = "alloc")]
mod vsock;

pub use error::SocketError;
#[cfg(feature = "alloc")]
pub use vsock::{DisconnectReason, VirtIOSocket, VsockEvent, VsockEventType};
