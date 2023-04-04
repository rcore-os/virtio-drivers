//! Driver for VirtIO socket devices.
#![deny(unsafe_op_in_unsafe_fn)]

use super::error::SocketError;
use super::protocol::{
    VirtioVsockConfig, VirtioVsockHdr, VirtioVsockOp, VirtioVsockPacket, VsockAddr,
};
use crate::device::common::Feature;
use crate::hal::{BufferDirection, Dma, Hal};
use crate::queue::VirtQueue;
use crate::transport::Transport;
use crate::volatile::volread;
use crate::Result;
use core::{convert::TryFrom, mem::size_of, ops::Range};
use log::{debug, info};
use zerocopy::{
    byteorder::{LittleEndian, U32},
    AsBytes,
};

const RX_QUEUE_IDX: u16 = 0;
const TX_QUEUE_IDX: u16 = 1;
const EVENT_QUEUE_IDX: u16 = 2;

const QUEUE_SIZE: usize = 8;

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
struct ConnectionInfo {
    dst: VsockAddr,
    src_port: u32,
    peer_buf_alloc: u32,
    peer_fwd_cnt: u32,
}

/// Driver for a VirtIO socket device.
pub struct VirtIOSocket<'a, H: Hal, T: Transport> {
    transport: T,
    /// Virtqueue to receive packets.
    rx: VirtQueue<H, { QUEUE_SIZE }>,
    tx: VirtQueue<H, { QUEUE_SIZE }>,
    /// Virtqueue to receive events from the device.
    event: VirtQueue<H, { QUEUE_SIZE }>,
    /// The guest_cid field contains the guest’s context ID, which uniquely identifies
    /// the device for its lifetime. The upper 32 bits of the CID are reserved and zeroed.
    guest_cid: u64,
    rx_buf_dma: Dma<H>,
    rx_buf: &'a mut [u8],

    /// Currently the device is only allowed to be connected to one destination at a time.
    connection_info: Option<ConnectionInfo>,
}

impl<'a, H: Hal, T: Transport> Drop for VirtIOSocket<'a, H, T> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(RX_QUEUE_IDX);
        self.transport.queue_unset(TX_QUEUE_IDX);
        self.transport.queue_unset(EVENT_QUEUE_IDX);
    }
}

impl<'a, H: Hal, T: Transport> VirtIOSocket<'a, H, T> {
    /// Create a new VirtIO Vsock driver that uses (`rx_buf_pages` * 4 KiB) memory as the rx buffer.
    pub fn new(mut transport: T, rx_buf_pages: usize) -> Result<Self> {
        transport.begin_init(|features| {
            let features = Feature::from_bits_truncate(features);
            info!("Device features: {:?}", features);
            // negotiate these flags only
            let supported_features = Feature::empty();
            (features & supported_features).bits()
        });

        let config = transport.config_space::<VirtioVsockConfig>()?;
        info!("config: {:?}", config);
        // Safe because config is a valid pointer to the device configuration space.
        let guest_cid = unsafe {
            volread!(config, guest_cid_low) as u64 | (volread!(config, guest_cid_high) as u64) << 32
        };
        info!("guest cid: {guest_cid:?}");

        let mut rx = VirtQueue::new(&mut transport, RX_QUEUE_IDX)?;
        let tx = VirtQueue::new(&mut transport, TX_QUEUE_IDX)?;
        let event = VirtQueue::new(&mut transport, EVENT_QUEUE_IDX)?;

        // Allocates memory as the rx buffer.
        let rx_buf_dma = Dma::new(
            rx_buf_pages, // pages
            BufferDirection::DeviceToDriver,
        )?;
        // Safe because no alignment or initialisation is required for [u8], the DMA buffer is
        // dereferenceable, and the lifetime of the reference matches the lifetime of the DMA buffer
        // (which we don't otherwise access).
        let rx_buf = unsafe { rx_buf_dma.raw_slice().as_mut() };
        // Safe because `rx_buf` lives as long as the `rx` queue.
        unsafe {
            Self::fill_rx_queue(&mut rx, rx_buf, &mut transport)?;
        }
        transport.finish_init();

        Ok(Self {
            transport,
            rx,
            tx,
            event,
            guest_cid,
            rx_buf_dma,
            rx_buf,
            connection_info: None,
        })
    }

    /// Fills the `rx` queue with the buffer `rx_buf`.
    ///
    /// # Safety
    /// Behavior is undefined if any of the following condition is violated:
    /// * `rx_buf` must live at least as long as the `rx` queue.
    unsafe fn fill_rx_queue(
        rx: &mut VirtQueue<H, { QUEUE_SIZE }>,
        rx_buf: &mut [u8],
        transport: &mut T,
    ) -> Result {
        if rx_buf.len() < size_of::<VirtioVsockHdr>() * QUEUE_SIZE {
            return Err(SocketError::BufferTooShort.into());
        }
        for i in 0..QUEUE_SIZE {
            let buffer_range = Self::rx_buffer_range(rx_buf, i)?;
            // Safe because the buffer lives as long as the queue as specified in the function
            // safety requirement.
            let token = unsafe { rx.add(&[], &mut [&mut rx_buf[buffer_range]])? };
            assert_eq!(token as usize, i);
        }

        if rx.should_notify() {
            transport.notify(RX_QUEUE_IDX);
        }
        Ok(())
    }

    /// Connects to the destination.
    pub fn connect(&mut self, dst_cid: u64, src_port: u32, dst_port: u32) -> Result {
        if self.connection_info.is_some() {
            return Err(SocketError::ConnectionExists.into());
        }
        let header = VirtioVsockHdr {
            src_cid: self.guest_cid.into(),
            dst_cid: dst_cid.into(),
            src_port: src_port.into(),
            dst_port: dst_port.into(),
            op: VirtioVsockOp::Request.into(),
            ..Default::default()
        };
        // Sends a header only packet to the tx queue to connect the device to the listening
        // socket at the given destination.
        self.send_packet_to_tx_queue(&header, &[])?;
        self.poll_and_filter_packet_from_rx_queue(&[VirtioVsockOp::Response], |packet| {
            packet.check_data_is_empty().map_err(|e| e.into())
        })?;
        let dst = VsockAddr {
            cid: dst_cid,
            port: dst_port,
        };
        self.connection_info.replace(ConnectionInfo {
            dst,
            src_port,
            ..Default::default()
        });
        debug!("Connection established: {:?}", self.connection_info);
        self.update_credit()
    }

    /// Requests the credit and updates the peer credit in the current connection info.
    fn request_credit(&mut self) -> Result {
        let connection_info = self.connection_info()?;
        let header = VirtioVsockHdr {
            src_cid: self.guest_cid.into(),
            dst_cid: connection_info.dst.cid.into(),
            src_port: connection_info.src_port.into(),
            dst_port: connection_info.dst.port.into(),
            op: VirtioVsockOp::CreditRequest.into(),
            ..Default::default()
        };
        self.send_packet_to_tx_queue(&header, &[])?;
        self.poll_and_filter_packet_from_rx_queue(&[VirtioVsockOp::CreditUpdate], |_| Ok(()))
    }

    /// Sends the socket's credit information to the peer.
    pub fn update_credit(&mut self) -> Result {
        let connection_info = self.connection_info()?;
        let header = VirtioVsockHdr {
            src_cid: self.guest_cid.into(),
            dst_cid: connection_info.dst.cid.into(),
            src_port: connection_info.src_port.into(),
            dst_port: connection_info.dst.port.into(),
            op: VirtioVsockOp::CreditUpdate.into(),
            buf_alloc: usize_to_le32(self.total_rx_buf_alloc())?,
            ..Default::default()
        };
        self.send_packet_to_tx_queue(&header, &[])
    }

    /// Sends the buffer to the destination.
    pub fn send(&mut self, buffer: &[u8]) -> Result {
        self.check_peer_buffer_is_sufficient(buffer.len())?;

        let connection_info = self.connection_info()?;
        // TODO: Send the correct fwd_cnt.
        let header = VirtioVsockHdr {
            src_cid: self.guest_cid.into(),
            dst_cid: connection_info.dst.cid.into(),
            src_port: connection_info.src_port.into(),
            dst_port: connection_info.dst.port.into(),
            op: VirtioVsockOp::Rw.into(),
            len: usize_to_le32(buffer.len())?,
            buf_alloc: usize_to_le32(self.total_rx_buf_alloc())?,
            ..Default::default()
        };
        self.send_packet_to_tx_queue(&header, buffer)
    }

    fn check_peer_buffer_is_sufficient(&mut self, buffer_len: usize) -> Result {
        // Updates the cached peer credit info before comparison.
        self.request_credit()?;
        let peer_buf_alloc = usize::try_from(self.connection_info()?.peer_buf_alloc)
            .map_err(|_| SocketError::InvalidNumber)?;
        if peer_buf_alloc >= buffer_len {
            Ok(())
        } else {
            Err(SocketError::InsufficientBufferSpaceInPeer.into())
        }
    }

    /// Receives the buffer from the destination.
    /// Returns the actual size of the message.
    pub fn recv(&mut self, buffer: &mut [u8]) -> Result<usize> {
        let mut len: usize = 0;
        self.poll_and_filter_packet_from_rx_queue(&[VirtioVsockOp::Rw], |packet| {
            buffer
                .get_mut(0..packet.hdr.len())
                .ok_or(SocketError::OutputBufferTooShort(packet.hdr.len()))?
                .copy_from_slice(packet.data);
            len = packet.hdr.len();
            Ok(())
        })?;
        Ok(len)
    }

    /// Shuts down the connection.
    pub fn shutdown(&mut self) -> Result {
        let connection_info = self.connection_info()?;
        let header = VirtioVsockHdr {
            src_cid: self.guest_cid.into(),
            dst_cid: connection_info.dst.cid.into(),
            src_port: connection_info.src_port.into(),
            dst_port: connection_info.dst.port.into(),
            op: VirtioVsockOp::Shutdown.into(),
            ..Default::default()
        };
        self.send_packet_to_tx_queue(&header, &[])?;
        self.poll_and_filter_packet_from_rx_queue(
            &[VirtioVsockOp::Rst, VirtioVsockOp::Shutdown],
            |_| Ok(()),
        )?;
        Ok(())
    }

    fn send_packet_to_tx_queue(&mut self, header: &VirtioVsockHdr, buffer: &[u8]) -> Result {
        // TODO: Virtio v1.1 5.10.6.1.1 The rx virtqueue MUST be processed even when the tx virtqueue is full.
        let _len = self.tx.add_notify_wait_pop(
            &[header.as_bytes(), buffer],
            &mut [],
            &mut self.transport,
        )?;
        Ok(())
    }

    fn poll_and_filter_packet_from_rx_queue<F>(
        &mut self,
        accepted_ops: &[VirtioVsockOp],
        f: F,
    ) -> Result
    where
        F: FnOnce(&VirtioVsockPacket) -> Result,
    {
        loop {
            self.wait_one_in_rx_queue();
            let mut connection_info = self.connection_info.unwrap_or_default();
            let packet = self.pop_packet_from_rx_queue()?;
            let op = packet.hdr.op()?;
            match op {
                VirtioVsockOp::CreditUpdate => {
                    packet.check_data_is_empty()?;

                    connection_info.peer_buf_alloc = packet.hdr.buf_alloc.into();
                    connection_info.peer_fwd_cnt = packet.hdr.fwd_cnt.into();
                    self.connection_info.replace(connection_info);
                    debug!("Connection info updated: {:?}", self.connection_info);

                    if accepted_ops.contains(&op) {
                        break;
                    } else {
                        // Virtio v1.1 5.10.6.3 It is also valid to send a VIRTIO_VSOCK_OP_CREDIT_UPDATE packet without
                        // previously receiving a VIRTIO_VSOCK_OP_CREDIT_REQUEST packet. This allows communicating updates
                        // any time a change in buffer space occurs.
                        continue;
                    }
                }
                VirtioVsockOp::Rst | VirtioVsockOp::Shutdown => {
                    packet.check_data_is_empty()?;

                    self.connection_info.take();
                    info!("Disconnected from the peer");
                    if accepted_ops.contains(&op) {
                        break;
                    } else if op == VirtioVsockOp::Rst {
                        return Err(SocketError::ConnectionFailed.into());
                    } else if op == VirtioVsockOp::Shutdown {
                        return Err(SocketError::PeerSocketShutdown.into());
                    }
                }
                x if accepted_ops.contains(&x) => {
                    f(&packet)?;
                    break;
                }
                _ => return Err(SocketError::InvalidOperation.into()),
            };
        }
        Ok(())
    }

    /// Waits until there is at least one element to pop in rx queue.
    fn wait_one_in_rx_queue(&mut self) {
        const TIMEOUT_N: usize = 1000000;
        for _ in 0..TIMEOUT_N {
            if self.rx.can_pop() {
                break;
            } else {
                core::hint::spin_loop();
            }
        }
    }

    fn pop_packet_from_rx_queue(&mut self) -> Result<VirtioVsockPacket> {
        let Some(token) = self.rx.peek_used() else {
            return Err(SocketError::NoResponseReceived.into());
        };
        let buffer_range = self.get_rx_buffer_range(token as usize)?;
        let buffer = &mut self.rx_buf[buffer_range];
        // Safe because we are passing the same buffer as we passed to `VirtQueue::add`.
        let _len = unsafe { self.rx.pop_used(token, &[], &mut [buffer])? };
        let packet = VirtioVsockPacket::read_from(buffer)?;
        debug!("Received packet {:?}. Op {:?}", packet, packet.hdr.op());
        Ok(packet)
    }

    fn get_rx_buffer_range(&self, i: usize) -> Result<Range<usize>> {
        Self::rx_buffer_range(self.rx_buf, i)
    }

    fn connection_info(&self) -> Result<ConnectionInfo> {
        self.connection_info.ok_or(SocketError::NotConnected.into())
    }

    /// Returns the total receive buffer space, in bytes, for this socket.
    /// Only payload bytes are counted and header bytes are not included.
    fn total_rx_buf_alloc(&self) -> usize {
        self.rx_buf.len() - size_of::<VirtioVsockHdr>() * QUEUE_SIZE
    }

    fn rx_buffer_range(rx_buf: &[u8], i: usize) -> Result<Range<usize>> {
        let buffer_size = rx_buf.len() / QUEUE_SIZE;
        let start = buffer_size
            .checked_mul(i)
            .ok_or(SocketError::InvalidNumber)?;
        let end = start
            .checked_add(buffer_size)
            .ok_or(SocketError::InvalidNumber)?;
        if end > rx_buf.len() {
            Err(SocketError::BufferTooShort.into())
        } else {
            Ok(start..end)
        }
    }
}

fn usize_to_le32(x: usize) -> Result<U32<LittleEndian>> {
    Ok(u32::try_from(x)
        .map_err(|_| SocketError::InvalidNumber)?
        .into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::volatile::ReadOnly;
    use crate::{
        hal::fake::FakeHal,
        transport::{
            fake::{FakeTransport, QueueStatus, State},
            DeviceStatus, DeviceType,
        },
    };
    use alloc::{sync::Arc, vec};
    use core::ptr::NonNull;
    use std::sync::Mutex;

    #[test]
    fn config() {
        let mut config_space = VirtioVsockConfig {
            guest_cid_low: ReadOnly::new(66),
            guest_cid_high: ReadOnly::new(0),
        };
        let state = Arc::new(Mutex::new(State {
            status: DeviceStatus::empty(),
            driver_features: 0,
            guest_page_size: 0,
            interrupt_pending: false,
            queues: vec![QueueStatus::default(); 3],
        }));
        let transport = FakeTransport {
            device_type: DeviceType::Socket,
            max_queue_size: 32,
            device_features: 0,
            config_space: NonNull::from(&mut config_space),
            state: state.clone(),
        };
        let socket = VirtIOSocket::<FakeHal, FakeTransport<VirtioVsockConfig>>::new(
            transport, 1, // rx_buf_pages
        )
        .unwrap();
        assert_eq!(socket.guest_cid, 0x00_0000_0042);
    }
}
