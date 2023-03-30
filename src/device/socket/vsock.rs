//! Driver for VirtIO socket devices.

use super::error::SocketError;
use super::protocol::{VirtioVsockConfig, VirtioVsockHdr, VirtioVsockOp, VirtioVsockPacket};
use crate::device::common::Feature;
use crate::hal::{BufferDirection, Dma, Hal};
use crate::queue::VirtQueue;
use crate::transport::Transport;
use crate::volatile::volread;
use crate::Result;
use log::{info, trace};
use zerocopy::AsBytes;

const RX_QUEUE_IDX: u16 = 0;
const TX_QUEUE_IDX: u16 = 1;
const EVENT_QUEUE_IDX: u16 = 2;

const QUEUE_SIZE: usize = 2;

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
    queue_buf_dma: Dma<H>,
    queue_buf_rx: &'a mut [u8],
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

        let queue_buf_dma = Dma::new(1, BufferDirection::DeviceToDriver)?;

        // Safe because no alignment or initialisation is required for [u8], the DMA buffer is
        // dereferenceable, and the lifetime of the reference matches the lifetime of the DMA buffer
        // (which we don't otherwise access).
        let queue_buf_rx = unsafe { queue_buf_dma.raw_slice().as_mut() };

        // Safe because the buffer lives as long as the queue.
        let _token = unsafe { rx.add(&[], &mut [queue_buf_rx])? };

        if rx.should_notify() {
            transport.notify(RX_QUEUE_IDX);
        }
        transport.finish_init();

        Ok(Self {
            transport,
            rx,
            tx,
            event,
            guest_cid,
            queue_buf_dma,
            queue_buf_rx,
        })
    }

    /// Connect to the destination.
    pub fn connect(&mut self, dst_cid: u64, src_port: u32, dst_port: u32) -> Result {
        let header = VirtioVsockHdr {
            src_cid: self.guest_cid.into(),
            dst_cid: dst_cid.into(),
            src_port: src_port.into(),
            dst_port: dst_port.into(),
            op: VirtioVsockOp::Request.into(),
            ..Default::default()
        };
        self.tx
            .add_notify_wait_pop(&[header.as_bytes(), &[]], &mut [], &mut self.transport)?;
        let token = if let Some(token) = self.rx.peek_used() {
            token // TODO: Use let else after updating Rust
        } else {
            return Err(SocketError::NoResponseReceived.into());
        };
        // Safe because we are passing the same buffer as we passed to `VirtQueue::add`.
        let _len = unsafe { self.rx.pop_used(token, &[], &mut [self.queue_buf_rx])? };
        let packet_rx = VirtioVsockPacket::read_from(self.queue_buf_rx)?;
        trace!("Received packet {:?}. Op {:?}", packet_rx, packet_rx.op());
        match packet_rx.op()? {
            VirtioVsockOp::Response => Ok(()),
            VirtioVsockOp::Rst => Err(SocketError::ConnectionFailed.into()),
            VirtioVsockOp::Invalid => Err(SocketError::InvalidOperation.into()),
            _ => todo!(),
        }
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
