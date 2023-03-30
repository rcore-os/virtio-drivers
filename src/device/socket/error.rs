//! This module contain the error from the VirtIO socket driver.

use core::{fmt, result};

/// The error type of VirtIO socket driver.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SocketError {
    /// There is an existing connection.
    ConnectionExists,
    /// Failed to establish the connection.
    ConnectionFailed,
    /// The device is not connected to any peer.
    NotConnected,
    /// No response received.
    NoResponseReceived,
    /// The given buffer is shorter than expected.
    BufferTooShort,
    /// Unknown operation.
    UnknownOperation(u16),
    /// Invalid operation,
    InvalidOperation,
    /// Invalid number.
    InvalidNumber,
}

impl fmt::Display for SocketError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ConnectionExists => write!(
                f,
                "There is an existing connection. Please close the current connection before attempting to connect again."),
            Self::ConnectionFailed => write!(f, "Failed to establish the connection"),
            Self::NotConnected => write!(f, "The device is not connected to any peer. Please connect it to a peer first."),
            Self::NoResponseReceived => write!(f, "No response received"),
            Self::BufferTooShort => write!(f, "The given buffer is shorter than expected"),
            Self::UnknownOperation(op) => {
                write!(f, "The operation code '{op}' is unknown")
            }
            Self::InvalidOperation => write!(f, "Invalid operation"),
            Self::InvalidNumber => write!(f, "Invalid number"),
        }
    }
}

pub type Result<T> = result::Result<T, SocketError>;
