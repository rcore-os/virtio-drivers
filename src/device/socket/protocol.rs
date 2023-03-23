//! This module defines the socket device protocol according to the virtio spec 5.10 Socket Device

use super::error::{self, SocketError};
use crate::volatile::ReadOnly;
use core::convert::TryInto;
use core::{convert::TryFrom, mem::size_of};
use zerocopy::{
    byteorder::{LittleEndian, U16, U32, U64},
    AsBytes, FromBytes,
};

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
    pub src_cid: U64<LittleEndian>,
    pub dst_cid: U64<LittleEndian>,
    pub src_port: U32<LittleEndian>,
    pub dst_port: U32<LittleEndian>,
    pub len: U32<LittleEndian>,
    pub r#type: U16<LittleEndian>,
    pub op: U16<LittleEndian>,
    pub flags: U32<LittleEndian>,
    pub buf_alloc: U32<LittleEndian>,
    pub fwd_cnt: U32<LittleEndian>,
}

impl Default for VirtioVsockHdr {
    fn default() -> Self {
        Self {
            src_cid: 0.into(),
            dst_cid: 0.into(),
            src_port: 0.into(),
            dst_port: 0.into(),
            len: 0.into(),
            r#type: TYPE_STREAM_SOCKET.into(),
            op: 0.into(),
            flags: 0.into(),
            buf_alloc: 0.into(),
            fwd_cnt: 0.into(),
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
        let data_end = size_of::<VirtioVsockHdr>() + (hdr.len.get() as usize);
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
    pub id: U32<LittleEndian>,
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
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

impl Into<U16<LittleEndian>> for Op {
    fn into(self) -> U16<LittleEndian> {
        (self as u16).into()
    }
}

impl TryFrom<U16<LittleEndian>> for Op {
    type Error = SocketError;

    fn try_from(v: U16<LittleEndian>) -> Result<Self, Self::Error> {
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
