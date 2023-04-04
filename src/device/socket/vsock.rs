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
use core::{convert::TryFrom, mem::size_of};
use log::{debug, info, trace};
use tinyvec::ArrayVec;
use zerocopy::AsBytes;

const RX_QUEUE_IDX: u16 = 0;
const TX_QUEUE_IDX: u16 = 1;
const EVENT_QUEUE_IDX: u16 = 2;

const QUEUE_SIZE: usize = 8;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ConnectionInfo {
    dst: VsockAddr,
    src_port: u32,
    /// The last `buf_alloc` value the peer sent to us, indicating how much receive buffer space in
    /// bytes it has allocated for packet bodies.
    peer_buf_alloc: u32,
    /// The last `fwd_cnt` value the peer sent to us, indicating how many bytes of packet bodies it
    /// has finished processing.
    peer_fwd_cnt: u32,
    /// The number of bytes of packet bodies which we have sent to the peer.
    tx_cnt: u32,
    /// The number of bytes of packet bodies which we have received from the peer and handled.
    fwd_cnt: u32,
}

impl ConnectionInfo {
    fn peer_free(&self) -> u32 {
        self.peer_buf_alloc - (self.tx_cnt - self.peer_fwd_cnt)
    }

    fn new_header(&self, src_cid: u64) -> VirtioVsockHdr {
        VirtioVsockHdr {
            src_cid: src_cid.into(),
            dst_cid: self.dst.cid.into(),
            src_port: self.src_port.into(),
            dst_port: self.dst.port.into(),
            fwd_cnt: self.fwd_cnt.into(),
            ..Default::default()
        }
    }
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
    /// Create a new VirtIO Vsock driver.
    pub fn new(mut transport: T) -> Result<Self> {
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

        // Allocates 4 KiB memory as the rx buffer.
        let rx_buf_dma = Dma::new(
            1, // pages
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
            let buffer = Self::as_mut_sub_rx_buffer(rx_buf, i)?;
            // Safe because the buffer lives as long as the queue as specified in the function
            // safety requirement.
            let token = unsafe { rx.add(&[], &mut [buffer])? };
            assert_eq!(i, token.into());
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

        let dst = VsockAddr {
            cid: dst_cid,
            port: dst_port,
        };
        self.connection_info.replace(ConnectionInfo {
            dst,
            src_port,
            ..Default::default()
        });
        self.poll_and_filter_packet_from_rx_queue(&[VirtioVsockOp::Response], |packet| {
            packet.check_data_is_empty().map_err(|e| e.into())
        })?;
        debug!("Connection established: {:?}", self.connection_info);
        Ok(())
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

    /// Sends the buffer to the destination.
    pub fn send(&mut self, buffer: &[u8]) -> Result {
        self.check_peer_buffer_is_sufficient(buffer.len())?;

        let connection_info = self.connection_info()?;
        let len = buffer.len() as u32;
        let header = VirtioVsockHdr {
            op: VirtioVsockOp::Rw.into(),
            len: len.into(),
            buf_alloc: 0.into(),
            ..connection_info.new_header(self.guest_cid)
        };
        self.connection_info.as_mut().unwrap().tx_cnt += len;
        self.send_packet_to_tx_queue(&header, buffer)
    }

    fn check_peer_buffer_is_sufficient(&mut self, buffer_len: usize) -> Result {
        if usize::try_from(self.connection_info()?.peer_free())
            .map_err(|_| SocketError::InvalidNumber)?
            >= buffer_len
        {
            Ok(())
        } else {
            // Update cached peer credit and try again.
            self.request_credit()?;
            if usize::try_from(self.connection_info()?.peer_free())
                .map_err(|_| SocketError::InvalidNumber)?
                >= buffer_len
            {
                Ok(())
            } else {
                Err(SocketError::InsufficientBufferSpaceInPeer.into())
            }
        }
    }

    /// Receives the buffer from the destination.
    /// Returns the actual size of the message.
    pub fn recv(&mut self, buffer: &mut [u8]) -> Result<usize> {
        let connection_info = self.connection_info()?;

        // Tell the peer that we have space to recieve some data.
        let header = VirtioVsockHdr {
            op: VirtioVsockOp::CreditUpdate.into(),
            buf_alloc: (buffer.len() as u32).into(),
            ..connection_info.new_header(self.guest_cid)
        };
        self.send_packet_to_tx_queue(&header, &[])?;

        // Wait to receive some data.
        let mut len: u32 = 0;
        self.poll_and_filter_packet_from_rx_queue(&[VirtioVsockOp::Rw], |packet| {
            buffer
                .get_mut(0..packet.hdr.len() as usize)
                .ok_or(SocketError::OutputBufferTooShort(packet.hdr.len() as usize))?
                .copy_from_slice(packet.data);
            len = packet.hdr.len();
            Ok(())
        })?;
        self.connection_info.as_mut().unwrap().fwd_cnt += len;
        Ok(len as usize)
    }

    /// Shuts down the connection.
    pub fn shutdown(&mut self) -> Result {
        let connection_info = self.connection_info()?;
        let header = VirtioVsockHdr {
            op: VirtioVsockOp::Shutdown.into(),
            ..connection_info.new_header(self.guest_cid)
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
        let our_cid = self.guest_cid;
        let mut tokens_to_recycle = ArrayVec::<[usize; QUEUE_SIZE]>::new();
        let mut err = None::<SocketError>;
        loop {
            self.wait_one_in_rx_queue();
            let mut connection_info = self.connection_info.clone().unwrap_or_default();
            let (packet, token) = self.pop_packet_from_rx_queue()?;

            // Skip packets which don't match our current connection.
            if packet.hdr.source() != connection_info.dst
                || packet.hdr.dst_cid.get() != our_cid
                || packet.hdr.dst_port.get() != connection_info.src_port
            {
                trace!(
                    "Skipping {:?} as connection is {:?}",
                    packet.hdr,
                    connection_info
                );
                continue;
            }
            tokens_to_recycle.push(token);
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
                        // Virtio v1.1 5.10.6.3
                        // The driver can also receive a VIRTIO_VSOCK_OP_CREDIT_UPDATE packet without previously
                        // sending a VIRTIO_VSOCK_OP_CREDIT_REQUEST packet. This allows communicating updates
                        // any time a change in buffer space occurs.
                        continue;
                    }
                }
                VirtioVsockOp::Rst | VirtioVsockOp::Shutdown => {
                    packet.check_data_is_empty()?;

                    self.connection_info.take();
                    info!("Disconnected from the peer");
                    if accepted_ops.contains(&op) {
                    } else if op == VirtioVsockOp::Rst {
                        err.replace(SocketError::ConnectionFailed);
                    } else {
                        assert_eq!(VirtioVsockOp::Shutdown, op);
                        err.replace(SocketError::PeerSocketShutdown);
                    }
                    break;
                }
                x if accepted_ops.contains(&x) => {
                    f(&packet)?;
                    break;
                }
                _ => {
                    err.replace(SocketError::InvalidOperation.into());
                    break;
                }
            };
        }

        for token in tokens_to_recycle {
            self.recycle_rx_buffer(token)?;
        }
        if self.rx.should_notify() {
            self.transport.notify(RX_QUEUE_IDX);
        }
        if let Some(e) = err {
            Err(e.into())
        } else {
            Ok(())
        }
    }

    fn recycle_rx_buffer(&mut self, token: usize) -> Result {
        let buffer = Self::as_mut_sub_rx_buffer(self.rx_buf, token.into())?;
        // Safe because the buffer lasts at least as long as the rx queue.
        let new_token = unsafe { self.rx.add(&[], &mut [buffer])? };
        if token == new_token.into() {
            Ok(())
        } else {
            Err(SocketError::RecycledWrongBuffer.into())
        }
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

    fn pop_packet_from_rx_queue(&mut self) -> Result<(VirtioVsockPacket, usize)> {
        let Some(token) = self.rx.peek_used() else {
            return Err(SocketError::NoResponseReceived.into());
        };
        let buffer = Self::as_mut_sub_rx_buffer(self.rx_buf, token.into())?;
        // Safe because we are passing the same buffer as we passed to `VirtQueue::add`.
        let _len = unsafe { self.rx.pop_used(token, &[], &mut [buffer])? };
        let packet = VirtioVsockPacket::read_from(buffer)?;
        debug!("Received packet {:?}. Op {:?}", packet, packet.hdr.op());
        Ok((packet, token.into()))
    }

    fn connection_info(&self) -> Result<ConnectionInfo> {
        self.connection_info
            .clone()
            .ok_or(SocketError::NotConnected.into())
    }

    fn as_mut_sub_rx_buffer(rx_buf: &mut [u8], i: usize) -> Result<&mut [u8]> {
        let buffer_size = rx_buf.len() / QUEUE_SIZE;
        let start = buffer_size
            .checked_mul(i)
            .ok_or(SocketError::InvalidNumber)?;
        let end = start
            .checked_add(buffer_size)
            .ok_or(SocketError::InvalidNumber)?;
        rx_buf
            .get_mut(start..end)
            .ok_or(SocketError::BufferTooShort.into())
    }
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
        let socket =
            VirtIOSocket::<FakeHal, FakeTransport<VirtioVsockConfig>>::new(transport).unwrap();
        assert_eq!(socket.guest_cid, 0x00_0000_0042);
    }
}
