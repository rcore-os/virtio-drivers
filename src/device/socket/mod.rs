//! This module implements the virtio vsock device.

mod error;
#[cfg(feature = "alloc")]
mod multiconnectionmanager;
mod protocol;
#[cfg(feature = "alloc")]
mod singleconnectionmanager;
#[cfg(feature = "alloc")]
mod vsock;

pub use error::SocketError;
#[cfg(feature = "alloc")]
pub use multiconnectionmanager::VsockConnectionManager;
pub use protocol::VsockAddr;
#[cfg(feature = "alloc")]
pub use singleconnectionmanager::SingleConnectionManager;
#[cfg(feature = "alloc")]
pub use vsock::{DisconnectReason, VirtIOSocket, VsockEvent, VsockEventType};
