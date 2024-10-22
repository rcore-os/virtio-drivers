//! This module contain the error from the VirtIO socket driver.

use core::{fmt, result};

/// The error type of VirtIO socket driver.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SocketError {
    /// There is an existing connection.
    ConnectionExists,
    /// The device is not connected to any peer.
    NotConnected,
    /// Peer socket is shutdown.
    PeerSocketShutdown,
    /// The given buffer is shorter than expected.
    BufferTooShort,
    /// The given buffer for output is shorter than expected.
    OutputBufferTooShort(usize),
    /// The given buffer has exceeded the maximum buffer size.
    BufferTooLong(usize, usize),
    /// Unknown operation.
    UnknownOperation(u16),
    /// Invalid operation,
    InvalidOperation,
    /// Invalid number.
    InvalidNumber,
    /// Unexpected data in packet.
    UnexpectedDataInPacket,
    /// Peer has insufficient buffer space, try again later.
    InsufficientBufferSpaceInPeer,
    /// Recycled a wrong buffer.
    RecycledWrongBuffer,
}

impl fmt::Display for SocketError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::ConnectionExists => write!(
                f,
                "There is an existing connection. Please close the current connection before attempting to connect again."),
            Self::NotConnected => write!(f, "The device is not connected to any peer. Please connect it to a peer first."),
            Self::PeerSocketShutdown => write!(f, "The peer socket is shutdown."),
            Self::BufferTooShort => write!(f, "The given buffer is shorter than expected"),
            Self::BufferTooLong(actual, max) => {
                write!(f, "The given buffer length '{actual}' has exceeded the maximum allowed buffer length '{max}'")
            }
            Self::OutputBufferTooShort(expected) => {
                write!(f, "The given output buffer is too short. '{expected}' bytes is needed for the output buffer.")
            }
            Self::UnknownOperation(op) => {
                write!(f, "The operation code '{op}' is unknown")
            }
            Self::InvalidOperation => write!(f, "Invalid operation"),
            Self::InvalidNumber => write!(f, "Invalid number"),
            Self::UnexpectedDataInPacket => write!(f, "No data is expected in the packet"),
            Self::InsufficientBufferSpaceInPeer => write!(f, "Peer has insufficient buffer space, try again later"),
            Self::RecycledWrongBuffer => write!(f, "Recycled a wrong buffer"),
        }
    }
}

pub type Result<T> = result::Result<T, SocketError>;
