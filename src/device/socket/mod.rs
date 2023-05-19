//! This module implements the virtio vsock device.

mod error;
mod protocol;
#[cfg(feature = "alloc")]
mod vsock;

pub use error::SocketError;
pub use protocol::VsockAddr;
#[cfg(feature = "alloc")]
pub use vsock::{DisconnectReason, VirtIOSocket, VsockEvent, VsockEventType};
