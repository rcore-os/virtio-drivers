//! This module defines the socket device protocol according to the virtio spec 5.10 Socket Device

use super::error::{self, SocketError};
use crate::endian::{Le16, Le32, Le64};
use crate::volatile::ReadOnly;
use core::convert::TryInto;
<<<<<<< HEAD
use core::{convert::TryFrom, fmt, mem::size_of};
=======
use core::{convert::TryFrom, mem::size_of};
>>>>>>> c9a375f (Add protocols to support virtio socket device)
use zerocopy::{AsBytes, FromBytes};

pub const TYPE_STREAM_SOCKET: u16 = 1;

/// VirtioVsockConfig is the vsock device configuration space.
#[repr(C)]
pub struct VirtioVsockConfig {
    /// The guest_cid field contains the guest’s context ID, which uniquely identifies
    /// the device for its lifetime. The upper 32 bits of the CID are reserved and zeroed.
    ///
    /// We need to split the guest_cid into two parts because VirtIO only guarantees 4 bytes alignment.
    pub guest_cid_low: ReadOnly<u32>,
    pub _guest_cid_high: ReadOnly<u32>,
}

/// The message header for data packets sent on the tx/rx queues
#[repr(packed)]
#[derive(AsBytes, Clone, Copy, Debug, FromBytes)]
pub struct VirtioVsockHdr {
    pub src_cid: Le64,
    pub dst_cid: Le64,
    pub src_port: Le32,
    pub dst_port: Le32,
    pub len: Le32,
    pub r#type: Le16,
    pub op: Le16,
    pub flags: Le32,
    pub buf_alloc: Le32,
    pub fwd_cnt: Le32,
}

impl Default for VirtioVsockHdr {
    fn default() -> Self {
        Self {
            src_cid: Le64::default(),
            dst_cid: Le64::default(),
            src_port: Le32::default(),
            dst_port: Le32::default(),
            len: Le32::default(),
            r#type: TYPE_STREAM_SOCKET.into(),
            op: Le16::default(),
            flags: Le32::default(),
            buf_alloc: Le32::default(),
            fwd_cnt: Le32::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct VirtioVsockPacket<'a> {
    pub hdr: VirtioVsockHdr,
    pub data: &'a [u8],
}

impl<'a> VirtioVsockPacket<'a> {
    pub fn read_from(buffer: &'a [u8]) -> Result<Self, SocketError> {
        let hdr = buffer
            .get(0..size_of::<VirtioVsockHdr>())
            .ok_or(SocketError::BufferTooShort)?;
        let hdr = VirtioVsockHdr::read_from(hdr).ok_or(SocketError::PacketParsingFailed)?;
        let data_end = size_of::<VirtioVsockHdr>() + (hdr.len.to_native() as usize);
        let data = buffer
            .get(size_of::<VirtioVsockHdr>()..data_end)
            .ok_or(SocketError::BufferTooShort)?;
        Ok(Self { hdr, data })
    }

    pub fn op(&self) -> error::Result<Op> {
        self.hdr.op.try_into()
    }
}

/// An event sent to the event queue
#[derive(Copy, Clone, Debug, Default, AsBytes, FromBytes)]
#[repr(C)]
pub struct VirtioVsockEvent {
    // ID from the virtio_vsock_event_id struct in the virtio spec
    pub id: Le32,
}

#[allow(non_camel_case_types)]
<<<<<<< HEAD
#[derive(Copy, Clone, Eq, PartialEq)]
=======
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
>>>>>>> c9a375f (Add protocols to support virtio socket device)
#[repr(u16)]
pub enum Op {
    VIRTIO_VSOCK_OP_INVALID = 0,

    /* Connect operations */
    VIRTIO_VSOCK_OP_REQUEST = 1,
    VIRTIO_VSOCK_OP_RESPONSE = 2,
    VIRTIO_VSOCK_OP_RST = 3,
    VIRTIO_VSOCK_OP_SHUTDOWN = 4,

    /* To send payload */
    VIRTIO_VSOCK_OP_RW = 5,

    /* Tell the peer our credit info */
    VIRTIO_VSOCK_OP_CREDIT_UPDATE = 6,
    /* Request the peer to send the credit info to us */
    VIRTIO_VSOCK_OP_CREDIT_REQUEST = 7,
}

impl Into<Le16> for Op {
    fn into(self) -> Le16 {
        Le16::from(self as u16)
    }
}

impl TryFrom<Le16> for Op {
    type Error = SocketError;

    fn try_from(v: Le16) -> Result<Self, Self::Error> {
        let op = match u16::from(v) {
            0 => Self::VIRTIO_VSOCK_OP_INVALID,
            1 => Self::VIRTIO_VSOCK_OP_REQUEST,
            2 => Self::VIRTIO_VSOCK_OP_RESPONSE,
            3 => Self::VIRTIO_VSOCK_OP_RST,
            4 => Self::VIRTIO_VSOCK_OP_SHUTDOWN,
            5 => Self::VIRTIO_VSOCK_OP_RW,
            6 => Self::VIRTIO_VSOCK_OP_CREDIT_UPDATE,
            7 => Self::VIRTIO_VSOCK_OP_CREDIT_REQUEST,
            _ => return Err(SocketError::UnknownOperation(v.into())),
        };
        Ok(op)
    }
}
<<<<<<< HEAD

impl fmt::Debug for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::VIRTIO_VSOCK_OP_INVALID => write!(f, "VIRTIO_VSOCK_OP_INVALID"),
            Self::VIRTIO_VSOCK_OP_REQUEST => write!(f, "VIRTIO_VSOCK_OP_REQUEST"),
            Self::VIRTIO_VSOCK_OP_RESPONSE => write!(f, "VIRTIO_VSOCK_OP_RESPONSE"),
            Self::VIRTIO_VSOCK_OP_RST => write!(f, "VIRTIO_VSOCK_OP_RST"),
            Self::VIRTIO_VSOCK_OP_SHUTDOWN => write!(f, "VIRTIO_VSOCK_OP_SHUTDOWN"),
            Self::VIRTIO_VSOCK_OP_RW => write!(f, "VIRTIO_VSOCK_OP_RW"),
            Self::VIRTIO_VSOCK_OP_CREDIT_UPDATE => write!(f, "VIRTIO_VSOCK_OP_CREDIT_UPDATE"),
            Self::VIRTIO_VSOCK_OP_CREDIT_REQUEST => write!(f, "VIRTIO_VSOCK_OP_CREDIT_REQUEST"),
        }
    }
}
=======
>>>>>>> c9a375f (Add protocols to support virtio socket device)
