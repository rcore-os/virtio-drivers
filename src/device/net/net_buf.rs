use super::{VirtioNetHdr, VirtioNetHdrLegacy};
use alloc::{vec, vec::Vec};
use core::{convert::TryInto, mem::size_of};
use zerocopy::{FromBytes, IntoBytes};

/// A buffer used for transmitting.
pub struct TxBuffer(pub(crate) Vec<u8>);

/// A buffer used for receiving.
pub struct RxBuffer {
    pub(crate) buf: Vec<usize>, // for alignment
    pub(crate) packet_len: usize,
    pub(crate) idx: u16,
    /// Whether `num_buffers` is missing in the `virtio_net_hdr` struct.
    legacy_header: bool,
}

impl TxBuffer {
    /// Constructs the buffer from the given slice.
    pub fn from(buf: &[u8]) -> Self {
        Self(Vec::from(buf))
    }

    /// Returns the network packet length.
    pub fn packet_len(&self) -> usize {
        self.0.len()
    }

    /// Returns the network packet as a slice.
    pub fn packet(&self) -> &[u8] {
        self.0.as_slice()
    }

    /// Returns the network packet as a mutable slice.
    pub fn packet_mut(&mut self) -> &mut [u8] {
        self.0.as_mut_slice()
    }
}

impl RxBuffer {
    /// Allocates a new buffer with length `buf_len`.
    pub(crate) fn new(idx: usize, buf_len: usize, legacy_header: bool) -> Self {
        Self {
            buf: vec![0; buf_len / size_of::<usize>()],
            packet_len: 0,
            idx: idx.try_into().unwrap(),
            legacy_header,
        }
    }

    /// Set the network packet length.
    pub(crate) fn set_packet_len(&mut self, packet_len: usize) {
        self.packet_len = packet_len
    }

    /// Returns the network packet length (without header).
    pub const fn packet_len(&self) -> usize {
        self.packet_len
    }

    /// Returns all data in the buffer, including both the header and the packet.
    pub fn as_bytes(&self) -> &[u8] {
        self.buf.as_bytes()
    }

    /// Returns all data in the buffer with the mutable reference,
    /// including both the header and the packet.
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        self.buf.as_mut_bytes()
    }

    /// Returns a copy of the header.
    pub fn header(&self) -> VirtioNetHdr {
        if self.legacy_header {
            VirtioNetHdrLegacy::ref_from_prefix(self.as_bytes())
                .unwrap()
                .0
                .into()
        } else {
            *VirtioNetHdr::ref_from_prefix(self.as_bytes()).unwrap().0
        }
    }

    /// Returns the network packet as a slice.
    pub fn packet(&self) -> &[u8] {
        let hdr_size = if self.legacy_header {
            size_of::<VirtioNetHdrLegacy>()
        } else {
            size_of::<VirtioNetHdr>()
        };

        &self.buf.as_bytes()[hdr_size..hdr_size + self.packet_len]
    }

    /// Returns the network packet as a mutable slice.
    pub fn packet_mut(&mut self) -> &mut [u8] {
        let hdr_size = if self.legacy_header {
            size_of::<VirtioNetHdrLegacy>()
        } else {
            size_of::<VirtioNetHdr>()
        };
        &mut self.buf.as_mut_bytes()[hdr_size..hdr_size + self.packet_len]
    }
}
