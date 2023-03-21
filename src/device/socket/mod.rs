//! This module implements the virtio vsock device.

mod error;
mod protocol;
mod vsock;

use super::common;

pub use error::SocketError;
pub use vsock::VirtIOSocket;
