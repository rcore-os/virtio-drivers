//! Driver for VirtIO network devices.

use crate::hal::Hal;
use crate::queue::VirtQueue;
use crate::transport::Transport;
use crate::volatile::{volread, ReadOnly};
use crate::{Error, Result};
use alloc::{vec, vec::Vec};
use bitflags::bitflags;
use core::{convert::TryInto, mem::size_of};
use log::{debug, warn};
use zerocopy::{AsBytes, FromBytes};

const MAX_BUFFER_LEN: usize = 65535;
const MIN_BUFFER_LEN: usize = 1526;
const NET_HDR_SIZE: usize = size_of::<VirtioNetHdr>();

/// A buffer used for transmitting.
pub struct TxBuffer(Vec<u8>);

/// A buffer used for receiving.
pub struct RxBuffer {
    buf: Vec<usize>, // for alignment
    packet_len: usize,
    idx: u16,
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
    fn new(idx: usize, buf_len: usize) -> Self {
        Self {
            buf: vec![0; buf_len / size_of::<usize>()],
            packet_len: 0,
            idx: idx.try_into().unwrap(),
        }
    }

    /// Set the network packet length.
    fn set_packet_len(&mut self, packet_len: usize) {
        self.packet_len = packet_len
    }

    /// Returns the network packet length (witout header).
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
        self.buf.as_bytes_mut()
    }

    /// Returns the reference of the header.
    pub fn header(&self) -> &VirtioNetHdr {
        unsafe { &*(self.buf.as_ptr() as *const VirtioNetHdr) }
    }

    /// Returns the network packet as a slice.
    pub fn packet(&self) -> &[u8] {
        &self.buf.as_bytes()[NET_HDR_SIZE..NET_HDR_SIZE + self.packet_len]
    }

    /// Returns the network packet as a mutable slice.
    pub fn packet_mut(&mut self) -> &mut [u8] {
        &mut self.buf.as_bytes_mut()[NET_HDR_SIZE..NET_HDR_SIZE + self.packet_len]
    }
}

/// The virtio network device is a virtual ethernet card.
///
/// It has enhanced rapidly and demonstrates clearly how support for new
/// features are added to an existing device.
/// Empty buffers are placed in one virtqueue for receiving packets, and
/// outgoing packets are enqueued into another for transmission in that order.
/// A third command queue is used to control advanced filtering features.
pub struct VirtIONet<H: Hal, T: Transport, const QUEUE_SIZE: usize> {
    transport: T,
    mac: EthernetAddress,
    recv_queue: VirtQueue<H, QUEUE_SIZE>,
    send_queue: VirtQueue<H, QUEUE_SIZE>,
    rx_buffers: [Option<RxBuffer>; QUEUE_SIZE],
}

impl<H: Hal, T: Transport, const QUEUE_SIZE: usize> VirtIONet<H, T, QUEUE_SIZE> {
    /// Create a new VirtIO-Net driver.
    pub fn new(mut transport: T, buf_len: usize) -> Result<Self> {
        let negotiated_features = transport.begin_init(SUPPORTED_FEATURES);
        // read configuration space
        let config = transport.config_space::<Config>()?;
        let mac;
        // Safe because config points to a valid MMIO region for the config space.
        unsafe {
            mac = volread!(config, mac);
            debug!(
                "Got MAC={:02x?}, status={:?}",
                mac,
                volread!(config, status)
            );
        }

        if !(MIN_BUFFER_LEN..=MAX_BUFFER_LEN).contains(&buf_len) {
            warn!(
                "Receive buffer len {} is not in range [{}, {}]",
                buf_len, MIN_BUFFER_LEN, MAX_BUFFER_LEN
            );
            return Err(Error::InvalidParam);
        }

        let send_queue = VirtQueue::new(
            &mut transport,
            QUEUE_TRANSMIT,
            false,
            negotiated_features.contains(Features::RING_EVENT_IDX),
        )?;
        let mut recv_queue = VirtQueue::new(
            &mut transport,
            QUEUE_RECEIVE,
            false,
            negotiated_features.contains(Features::RING_EVENT_IDX),
        )?;

        const NONE_BUF: Option<RxBuffer> = None;
        let mut rx_buffers = [NONE_BUF; QUEUE_SIZE];
        for (i, rx_buf_place) in rx_buffers.iter_mut().enumerate() {
            let mut rx_buf = RxBuffer::new(i, buf_len);
            // Safe because the buffer lives as long as the queue.
            let token = unsafe { recv_queue.add(&[], &mut [rx_buf.as_bytes_mut()])? };
            assert_eq!(token, i as u16);
            *rx_buf_place = Some(rx_buf);
        }

        if recv_queue.should_notify() {
            transport.notify(QUEUE_RECEIVE);
        }

        transport.finish_init();

        Ok(VirtIONet {
            transport,
            mac,
            recv_queue,
            send_queue,
            rx_buffers,
        })
    }

    /// Acknowledge interrupt.
    pub fn ack_interrupt(&mut self) -> bool {
        self.transport.ack_interrupt()
    }

    /// Get MAC address.
    pub fn mac_address(&self) -> EthernetAddress {
        self.mac
    }

    /// Whether can send packet.
    pub fn can_send(&self) -> bool {
        self.send_queue.available_desc() >= 2
    }

    /// Whether can receive packet.
    pub fn can_recv(&self) -> bool {
        self.recv_queue.can_pop()
    }

    /// Receives a [`RxBuffer`] from network. If currently no data, returns an
    /// error with type [`Error::NotReady`].
    ///
    /// It will try to pop a buffer that completed data reception in the
    /// NIC queue.
    pub fn receive(&mut self) -> Result<RxBuffer> {
        if let Some(token) = self.recv_queue.peek_used() {
            let mut rx_buf = self.rx_buffers[token as usize]
                .take()
                .ok_or(Error::WrongToken)?;
            if token != rx_buf.idx {
                return Err(Error::WrongToken);
            }

            // Safe because `token` == `rx_buf.idx`, we are passing the same
            // buffer as we passed to `VirtQueue::add` and it is still valid.
            let len = unsafe {
                self.recv_queue
                    .pop_used(token, &[], &mut [rx_buf.as_bytes_mut()])?
            } as usize;
            rx_buf.set_packet_len(len.checked_sub(NET_HDR_SIZE).ok_or(Error::IoError)?);
            Ok(rx_buf)
        } else {
            Err(Error::NotReady)
        }
    }

    /// Gives back the ownership of `rx_buf`, and recycles it for next use.
    ///
    /// It will add the buffer back to the NIC queue.
    pub fn recycle_rx_buffer(&mut self, mut rx_buf: RxBuffer) -> Result {
        // Safe because we take the ownership of `rx_buf` back to `rx_buffers`,
        // it lives as long as the queue.
        let new_token = unsafe { self.recv_queue.add(&[], &mut [rx_buf.as_bytes_mut()]) }?;
        // `rx_buffers[new_token]` is expected to be `None` since it was taken
        // away at `Self::receive()` and has not been added back.
        if self.rx_buffers[new_token as usize].is_some() {
            return Err(Error::WrongToken);
        }
        rx_buf.idx = new_token;
        self.rx_buffers[new_token as usize] = Some(rx_buf);
        if self.recv_queue.should_notify() {
            self.transport.notify(QUEUE_RECEIVE);
        }
        Ok(())
    }

    /// Allocate a new buffer for transmitting.
    pub fn new_tx_buffer(&self, buf_len: usize) -> TxBuffer {
        TxBuffer(vec![0; buf_len])
    }

    /// Sends a [`TxBuffer`] to the network, and blocks until the request
    /// completed.
    pub fn send(&mut self, tx_buf: TxBuffer) -> Result {
        let header = VirtioNetHdr::default();
        if tx_buf.packet_len() == 0 {
            // Special case sending an empty packet, to avoid adding an empty buffer to the
            // virtqueue.
            self.send_queue.add_notify_wait_pop(
                &[header.as_bytes()],
                &mut [],
                &mut self.transport,
            )?;
        } else {
            self.send_queue.add_notify_wait_pop(
                &[header.as_bytes(), tx_buf.packet()],
                &mut [],
                &mut self.transport,
            )?;
        }
        Ok(())
    }
}

impl<H: Hal, T: Transport, const QUEUE_SIZE: usize> Drop for VirtIONet<H, T, QUEUE_SIZE> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(QUEUE_RECEIVE);
        self.transport.queue_unset(QUEUE_TRANSMIT);
    }
}

bitflags! {
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct Features: u64 {
        /// Device handles packets with partial checksum.
        /// This "checksum offload" is a common feature on modern network cards.
        const CSUM = 1 << 0;
        /// Driver handles packets with partial checksum.
        const GUEST_CSUM = 1 << 1;
        /// Control channel offloads reconfiguration support.
        const CTRL_GUEST_OFFLOADS = 1 << 2;
        /// Device maximum MTU reporting is supported.
        ///
        /// If offered by the device, device advises driver about the value of
        /// its maximum MTU. If negotiated, the driver uses mtu as the maximum
        /// MTU value.
        const MTU = 1 << 3;
        /// Device has given MAC address.
        const MAC = 1 << 5;
        /// Device handles packets with any GSO type. (legacy)
        const GSO = 1 << 6;
        /// Driver can receive TSOv4.
        const GUEST_TSO4 = 1 << 7;
        /// Driver can receive TSOv6.
        const GUEST_TSO6 = 1 << 8;
        /// Driver can receive TSO with ECN.
        const GUEST_ECN = 1 << 9;
        /// Driver can receive UFO.
        const GUEST_UFO = 1 << 10;
        /// Device can receive TSOv4.
        const HOST_TSO4 = 1 << 11;
        /// Device can receive TSOv6.
        const HOST_TSO6 = 1 << 12;
        /// Device can receive TSO with ECN.
        const HOST_ECN = 1 << 13;
        /// Device can receive UFO.
        const HOST_UFO = 1 << 14;
        /// Driver can merge receive buffers.
        const MRG_RXBUF = 1 << 15;
        /// Configuration status field is available.
        const STATUS = 1 << 16;
        /// Control channel is available.
        const CTRL_VQ = 1 << 17;
        /// Control channel RX mode support.
        const CTRL_RX = 1 << 18;
        /// Control channel VLAN filtering.
        const CTRL_VLAN = 1 << 19;
        ///
        const CTRL_RX_EXTRA = 1 << 20;
        /// Driver can send gratuitous packets.
        const GUEST_ANNOUNCE = 1 << 21;
        /// Device supports multiqueue with automatic receive steering.
        const MQ = 1 << 22;
        /// Set MAC address through control channel.
        const CTL_MAC_ADDR = 1 << 23;

        // device independent
        const RING_INDIRECT_DESC = 1 << 28;
        const RING_EVENT_IDX = 1 << 29;
        const VERSION_1 = 1 << 32; // legacy
    }
}

bitflags! {
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct Status: u16 {
        const LINK_UP = 1;
        const ANNOUNCE = 2;
    }
}

bitflags! {
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct InterruptStatus : u32 {
        const USED_RING_UPDATE = 1 << 0;
        const CONFIGURATION_CHANGE = 1 << 1;
    }
}

#[repr(C)]
struct Config {
    mac: ReadOnly<EthernetAddress>,
    status: ReadOnly<Status>,
    max_virtqueue_pairs: ReadOnly<u16>,
    mtu: ReadOnly<u16>,
}

type EthernetAddress = [u8; 6];

/// VirtIO 5.1.6 Device Operation:
///
/// Packets are transmitted by placing them in the transmitq1. . .transmitqN,
/// and buffers for incoming packets are placed in the receiveq1. . .receiveqN.
/// In each case, the packet itself is preceded by a header.
#[repr(C)]
#[derive(AsBytes, Debug, Default, FromBytes)]
pub struct VirtioNetHdr {
    flags: Flags,
    gso_type: GsoType,
    hdr_len: u16, // cannot rely on this
    gso_size: u16,
    csum_start: u16,
    csum_offset: u16,
    // num_buffers: u16, // only available when the feature MRG_RXBUF is negotiated.
    // payload starts from here
}

#[derive(AsBytes, Copy, Clone, Debug, Default, Eq, FromBytes, PartialEq)]
#[repr(transparent)]
struct Flags(u8);

bitflags! {
    impl Flags: u8 {
        const NEEDS_CSUM = 1;
        const DATA_VALID = 2;
        const RSC_INFO   = 4;
    }
}

#[repr(transparent)]
#[derive(AsBytes, Debug, Copy, Clone, Default, Eq, FromBytes, PartialEq)]
struct GsoType(u8);

impl GsoType {
    const NONE: GsoType = GsoType(0);
    const TCPV4: GsoType = GsoType(1);
    const UDP: GsoType = GsoType(3);
    const TCPV6: GsoType = GsoType(4);
    const ECN: GsoType = GsoType(0x80);
}

const QUEUE_RECEIVE: u16 = 0;
const QUEUE_TRANSMIT: u16 = 1;
const SUPPORTED_FEATURES: Features = Features::MAC
    .union(Features::STATUS)
    .union(Features::RING_EVENT_IDX);
