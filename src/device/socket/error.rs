//! This module contain the error from the VirtIO socket driver.

use core::{fmt, result};

/// The error type of VirtIO socket driver.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SocketError {
    /// Failed to establish the connection.
    ConnectionFailed,
    /// No response received.
    NoResponseReceived,
    /// The given buffer is shorter than expected.
    BufferTooShort,
    /// Failed to parse the VirtioVsockPacket from buffer.
    PacketParsingFailed,
    /// Unknown operation.
    UnknownOperation(u16),
    /// Invalid opration,
    InvalidOperation,
}

impl fmt::Display for SocketError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ConnectionFailed => write!(f, "Failed to establish the connection"),
            Self::NoResponseReceived => write!(f, "No response received"),
            Self::BufferTooShort => write!(f, "The given buffer is shorter than expected"),
            Self::PacketParsingFailed => {
                write!(f, "Failed to parse the VirtioVsockPacket from buffer")
            }
            Self::UnknownOperation(op) => {
                write!(f, "The operation code '{op}' is unknown")
            }
            Self::InvalidOperation => write!(f, "Invalid operation"),
        }
    }
}

pub type Result<T> = result::Result<T, SocketError>;
