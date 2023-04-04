//! Driver for VirtIO socket devices.
#![deny(unsafe_op_in_unsafe_fn)]

use super::error::SocketError;
use super::protocol::{VirtioVsockConfig, VirtioVsockHdr, VirtioVsockOp, VsockAddr};
use crate::device::common::Feature;
use crate::hal::{BufferDirection, Dma, Hal};
use crate::queue::VirtQueue;
use crate::transport::Transport;
use crate::volatile::volread;
use crate::Result;
use core::ptr::NonNull;
use core::{convert::TryFrom, mem::size_of};
use log::{debug, info, trace};
use zerocopy::{AsBytes, FromBytes};

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
pub struct VirtIOSocket<H: Hal, T: Transport> {
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

    /// Currently the device is only allowed to be connected to one destination at a time.
    connection_info: Option<ConnectionInfo>,
}

impl<H: Hal, T: Transport> Drop for VirtIOSocket<H, T> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(RX_QUEUE_IDX);
        self.transport.queue_unset(TX_QUEUE_IDX);
        self.transport.queue_unset(EVENT_QUEUE_IDX);
    }
}

impl<H: Hal, T: Transport> VirtIOSocket<H, T> {
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
        let rx_buf = rx_buf_dma.raw_slice();
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
            connection_info: None,
        })
    }

    /// Fills the `rx` queue with the buffer `rx_buf`.
    ///
    /// # Safety
    ///
    /// `rx_buf` must live at least as long as the `rx` queue, and the parts of the buffer which are
    /// in the queue must not be used anywhere else at the same time.
    unsafe fn fill_rx_queue(
        rx: &mut VirtQueue<H, { QUEUE_SIZE }>,
        rx_buf: NonNull<[u8]>,
        transport: &mut T,
    ) -> Result {
        if rx_buf.len() < size_of::<VirtioVsockHdr>() * QUEUE_SIZE {
            return Err(SocketError::BufferTooShort.into());
        }
        for i in 0..QUEUE_SIZE {
            // Safe because the buffer lives as long as the queue, as specified in the function
            // safety requirement, and we don't access it until it is popped.
            unsafe {
                let buffer = Self::as_mut_sub_rx_buffer(rx_buf, i)?;
                let token = rx.add(&[], &mut [buffer])?;
                assert_eq!(i, token.into());
            }
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
        self.poll_and_filter_packet_from_rx_queue(&[VirtioVsockOp::Response], &mut [], |header| {
            header.check_data_is_empty().map_err(|e| e.into())
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
        self.poll_and_filter_packet_from_rx_queue(&[VirtioVsockOp::CreditUpdate], &mut [], |_| {
            Ok(())
        })
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
        self.poll_and_filter_packet_from_rx_queue(&[VirtioVsockOp::Rw], buffer, |header| {
            len = header.len();
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
            &mut [],
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
        body: &mut [u8],
        f: F,
    ) -> Result
    where
        F: FnOnce(&VirtioVsockHdr) -> Result,
    {
        let our_cid = self.guest_cid;
        let mut err = None::<SocketError>;
        loop {
            self.wait_one_in_rx_queue();
            let mut connection_info = self.connection_info.clone().unwrap_or_default();
            let header = self.pop_packet_from_rx_queue(body)?;
            let op = header.op()?;

            // Skip packets which don't match our current connection.
            if header.source() != connection_info.dst
                || header.dst_cid.get() != our_cid
                || header.dst_port.get() != connection_info.src_port
            {
                trace!(
                    "Skipping {:?} as connection is {:?}",
                    header,
                    connection_info
                );
                continue;
            }

            match op {
                VirtioVsockOp::CreditUpdate => {
                    header.check_data_is_empty()?;

                    connection_info.peer_buf_alloc = header.buf_alloc.into();
                    connection_info.peer_fwd_cnt = header.fwd_cnt.into();
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
                    header.check_data_is_empty()?;

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
                    f(&header)?;
                    break;
                }
                _ => {
                    err.replace(SocketError::InvalidOperation);
                    break;
                }
            };
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

    /// Pops one packet from the RX queue, if there is one pending. Returns the header, and copies
    /// the body into the given buffer.
    ///
    /// Returns an error if there is no pending packet, or the body is bigger than the buffer
    /// supplied.
    fn pop_packet_from_rx_queue(&mut self, body: &mut [u8]) -> Result<VirtioVsockHdr> {
        let Some(token) = self.rx.peek_used() else {
            return Err(SocketError::NoResponseReceived.into());
        };

        // Safe because we maintain a consistent mapping of tokens to buffers, so we pass the same
        // buffer to `pop_used` as we previously passed to `add` for the token. Once we add the
        // buffer back to the RX queue then we don't access it again until next time it is popped.
        let header = unsafe {
            let buffer = Self::as_mut_sub_rx_buffer(self.rx_buf_dma.raw_slice(), token.into())?;
            let _len = self.rx.pop_used(token, &[], &mut [buffer])?;

            // Read the header and body from the buffer. Don't check the result yet, because we need
            // to add the buffer back to the queue either way.
            let header_result = read_header_and_body(buffer, body);

            // Add the buffer back to the RX queue.
            let new_token = self.rx.add(&[], &mut [buffer])?;
            // If the RX buffer somehow gets assigned a different token, then our safety assumptions
            // are broken and we can't safely continue to do anything with the device.
            assert_eq!(new_token, token);

            header_result
        }?;

        debug!("Received packet {:?}. Op {:?}", header, header.op());
        Ok(header)
    }

    fn connection_info(&self) -> Result<ConnectionInfo> {
        self.connection_info
            .clone()
            .ok_or(SocketError::NotConnected.into())
    }

    /// Gets a reference to a subslice of the RX buffer to be used for the given entry in the RX
    /// virtqueue.
    ///
    /// # Safety
    ///
    /// `rx_buf` must be a valid dereferenceable pointer.
    /// The returned reference has an arbitrary lifetime `'a`. This lifetime must not overlap with
    /// any other references to the same subslice of the RX buffer or outlive the buffer.
    unsafe fn as_mut_sub_rx_buffer<'a>(
        mut rx_buf: NonNull<[u8]>,
        i: usize,
    ) -> Result<&'a mut [u8]> {
        let buffer_size = rx_buf.len() / QUEUE_SIZE;
        let start = buffer_size
            .checked_mul(i)
            .ok_or(SocketError::InvalidNumber)?;
        let end = start
            .checked_add(buffer_size)
            .ok_or(SocketError::InvalidNumber)?;
        // Safe because no alignment or initialisation is required for [u8], and our caller assures
        // us that `rx_buf` is dereferenceable and that the lifetime of the slice we are creating
        // won't overlap with any other references to the same slice or outlive it.
        unsafe {
            rx_buf
                .as_mut()
                .get_mut(start..end)
                .ok_or(SocketError::BufferTooShort.into())
        }
    }
}

fn read_header_and_body(buffer: &[u8], body: &mut [u8]) -> Result<VirtioVsockHdr> {
    let header = VirtioVsockHdr::read_from_prefix(buffer).ok_or(SocketError::BufferTooShort)?;
    let body_length = header.len() as usize;
    let data_end = size_of::<VirtioVsockHdr>()
        .checked_add(body_length)
        .ok_or(SocketError::InvalidNumber)?;
    let data = buffer
        .get(size_of::<VirtioVsockHdr>()..data_end)
        .ok_or(SocketError::BufferTooShort)?;
    body.get_mut(0..body_length)
        .ok_or(SocketError::OutputBufferTooShort(body_length))?
        .copy_from_slice(data);
    Ok(header)
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
