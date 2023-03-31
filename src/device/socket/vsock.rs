//! Driver for VirtIO socket devices.

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
use core::{mem::size_of, ops::Range};
use log::{debug, info};
use zerocopy::AsBytes;

const RX_QUEUE_IDX: u16 = 0;
const TX_QUEUE_IDX: u16 = 1;
const EVENT_QUEUE_IDX: u16 = 2;

const QUEUE_SIZE: usize = 8;

#[derive(Copy, Clone, Debug, Default)]
struct ConnectionInfo {
    dst: VsockAddr,
    src_port: u32,
    buf_alloc: u32,
    fwd_cnt: u32,
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

        // Use 1 page (4 KiB) memory as the rx buffer.
        let rx_buf_dma = Dma::new(
            1, // pages
            BufferDirection::DeviceToDriver,
        )?;
        // Safe because no alignment or initialisation is required for [u8], the DMA buffer is
        // dereferenceable, and the lifetime of the reference matches the lifetime of the DMA buffer
        // (which we don't otherwise access).
        let rx_buf = unsafe { rx_buf_dma.raw_slice().as_mut() };
        Self::fill_rx_queue(&mut rx, rx_buf, &mut transport)?;
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

    fn fill_rx_queue(
        rx: &mut VirtQueue<H, { QUEUE_SIZE }>,
        rx_buf: &mut [u8],
        transport: &mut T,
    ) -> Result {
        let buffer_size = rx_buf.len() / QUEUE_SIZE;
        if buffer_size < size_of::<VirtioVsockHdr>() {
            return Err(SocketError::BufferTooShort.into());
        }
        for i in 0..QUEUE_SIZE {
            let start = i * buffer_size;
            let end = start + buffer_size;
            // Safe because the buffer lives as long as the queue.
            let token = unsafe { rx.add(&[], &mut [&mut rx_buf[start..end]])? };
            assert_eq!(token as usize, i);
        }

        if rx.should_notify() {
            transport.notify(RX_QUEUE_IDX);
        }
        Ok(())
    }

    /// Connect to the destination.
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
        self.send_packet_to_tx_queue(&header, &[])?;
        let received_header = self.pop_header_only_packet_from_rx_queue()?;
        match received_header.op()? {
            VirtioVsockOp::Response => {
                let dst = VsockAddr {
                    cid: dst_cid,
                    port: dst_port,
                };
                self.connection_info = Some(ConnectionInfo {
                    dst,
                    src_port,
                    ..Default::default()
                });
                Ok(())
            }
            VirtioVsockOp::Rst => Err(SocketError::ConnectionFailed.into()),
            VirtioVsockOp::Shutdown => Err(SocketError::PeerSocketShutdown.into()),
            _ => Err(SocketError::InvalidOperation.into()),
        }
    }

    /// Requests the credit.
    pub fn request_credit(&mut self) -> Result {
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
        let received_header = self.pop_header_only_packet_from_rx_queue()?;
        match received_header.op()? {
            VirtioVsockOp::CreditUpdate => {
                if let Some(connection_info) = self.connection_info.as_mut() {
                    connection_info.buf_alloc = received_header.buf_alloc.into();
                    connection_info.fwd_cnt = received_header.fwd_cnt.into();
                }
                debug!("Connection info {:?}", self.connection_info);
                Ok(())
            }
            VirtioVsockOp::Rst => Err(SocketError::ConnectionFailed.into()),
            _ => Err(SocketError::InvalidOperation.into()),
        }
    }

    /// Sends the buffer to the destination.
    /// TODO: send doesn't work yet.
    pub fn send(&mut self, buffer: &[u8]) -> Result {
        let connection_info = self.connection_info()?;
        let header = VirtioVsockHdr {
            src_cid: self.guest_cid.into(),
            dst_cid: connection_info.dst.cid.into(),
            src_port: connection_info.src_port.into(),
            dst_port: connection_info.dst.port.into(),
            op: VirtioVsockOp::Rw.into(),
            len: (buffer.len() as u32).into(),
            buf_alloc: connection_info.buf_alloc.into(),
            fwd_cnt: connection_info.fwd_cnt.into(),
            ..Default::default()
        };
        self.send_packet_to_tx_queue(&header, buffer)
    }

    /// Receives the buffer from the destination.
    /// Returns the actual size of the message.
    pub fn recv(&mut self, buffer: &mut [u8]) -> Result<usize> {
        let connection_info = self.connection_info()?;
        let header = VirtioVsockHdr {
            src_cid: self.guest_cid.into(),
            dst_cid: connection_info.dst.cid.into(),
            src_port: connection_info.src_port.into(),
            dst_port: connection_info.dst.port.into(),
            op: VirtioVsockOp::Rw.into(),
            buf_alloc: connection_info.buf_alloc.into(),
            fwd_cnt: connection_info.fwd_cnt.into(),
            ..Default::default()
        };
        self.send_packet_to_tx_queue(&header, &[])?;
        // Wait until there is at least one element can pop.
        for _ in 0..10000000 {
            if self.rx.can_pop() {
                break;
            }
        }
        let packet = self.pop_packet_from_rx_queue()?;
        match packet.hdr.op()? {
            VirtioVsockOp::Rw => {
                buffer
                    .get_mut(0..packet.hdr.len())
                    .ok_or(SocketError::BufferTooShort)?
                    .copy_from_slice(packet.data);
                Ok(packet.hdr.len())
            }
            VirtioVsockOp::Rst => Err(SocketError::ConnectionFailed.into()),
            _ => Err(SocketError::InvalidOperation.into()),
        }
    }

    /// Shuts down the connection.
    /// TODO: Add a timeout for shutdown.
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
        let received_header = self.pop_header_only_packet_from_rx_queue()?;
        match received_header.op()? {
            VirtioVsockOp::Rst => {
                info!("Disconnected from the peer");
                self.connection_info = None;
                Ok(())
            }
            _ => Err(SocketError::InvalidOperation.into()),
        }
    }

    fn send_packet_to_tx_queue(&mut self, header: &VirtioVsockHdr, buffer: &[u8]) -> Result {
        let _len = self.tx.add_notify_wait_pop(
            &[header.as_bytes(), &buffer],
            &mut [],
            &mut self.transport,
        )?;
        Ok(())
    }

    fn pop_packet_from_rx_queue(&mut self) -> Result<VirtioVsockPacket> {
        let token = if let Some(token) = self.rx.peek_used() {
            token // TODO: Use let else after updating Rust
        } else {
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

    fn pop_header_only_packet_from_rx_queue(&mut self) -> Result<VirtioVsockHdr> {
        let packet = self.pop_packet_from_rx_queue()?;
        assert_eq!(packet.data.len(), 0);
        Ok(packet.hdr)
    }

    fn get_rx_buffer_range(&self, i: usize) -> Result<Range<usize>> {
        let buffer_size = self.rx_buf.len() / QUEUE_SIZE;
        let start = buffer_size
            .checked_mul(i)
            .ok_or(SocketError::InvalidNumber)?;
        let end = start
            .checked_add(buffer_size)
            .ok_or(SocketError::InvalidNumber)?;
        if end > self.rx_buf.len() {
            Err(SocketError::BufferTooShort.into())
        } else {
            Ok(start..end)
        }
    }

    fn connection_info(&self) -> Result<ConnectionInfo> {
        self.connection_info.ok_or(SocketError::NotConnected.into())
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
