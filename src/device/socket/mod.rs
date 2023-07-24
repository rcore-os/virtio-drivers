//! Driver for VirtIO socket devices.
//!
//! To use the driver, you should first create a [`VirtIOSocket`] instance with your VirtIO
//! transport, and then create a [`VsockConnectionManager`] wrapping it to keep track of
//! connections. If you only want to have a single outgoing vsock connection at once, you can use
//! [`SingleConnectionManager`] for a slightly simpler interface.
//!
//! See [`VsockConnectionManager`] for a usage example.

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
pub use protocol::{VsockAddr, VMADDR_CID_HOST};
#[cfg(feature = "alloc")]
pub use singleconnectionmanager::SingleConnectionManager;
#[cfg(feature = "alloc")]
pub use vsock::{DisconnectReason, VirtIOSocket, VsockEvent, VsockEventType};
