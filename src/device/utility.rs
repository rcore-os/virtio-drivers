//! Driver for generic VirtIO devices.
use super::common::Feature;
use crate::{queue::VirtQueue, transport::Transport, Hal, Result};

// VirtioUtility only uses one queue
const QUEUE_IDX: u16 = 0;
const SUPPORTED_FEATURES: Feature = Feature::RING_INDIRECT_DESC.union(Feature::RING_EVENT_IDX);

/// Driver for generic VirtIO device.
pub struct VirtIOUtility<H: Hal, T: Transport, const SIZE: usize> {
    transport: T,
    queue: VirtQueue<H, SIZE>,
}

impl<H: Hal, T: Transport, const SIZE: usize> VirtIOUtility<H, T, SIZE> {
    /// Create a new driver with the given transport.
    pub fn new(mut transport: T, features: Feature) -> Result<Self> {
        let feat = transport.begin_init(features);
        let queue = VirtQueue::new(
            &mut transport,
            QUEUE_IDX,
            feat.contains(Feature::RING_INDIRECT_DESC),
            feat.contains(Feature::RING_EVENT_IDX),
        )?;
        transport.finish_init();
        Ok(Self { transport, queue })
    }

    /// Request from the device to be read from `dst`,and to be written into `src`.
    pub fn request(&mut self, src: &[u8], dst: &mut [u8]) -> Result<usize> {
        let num = self
            .queue
            .add_notify_wait_pop(&[src], &mut [dst], &mut self.transport)?;
        Ok(num as usize)
    }

    /// Enable interrupts.
    pub fn enable_interrupts(&mut self) {
        self.queue.set_dev_notify(true);
    }

    /// Disable interrupts.
    pub fn disable_interrupts(&mut self) {
        self.queue.set_dev_notify(false);
    }

    /// Acknowledge interrupt.
    pub fn ack_interrupt(&mut self) -> bool {
        self.transport.ack_interrupt()
    }
}

impl<H: Hal, T: Transport, const SIZE: usize> Drop for VirtIOUtility<H, T, SIZE> {
    fn drop(&mut self) {
        self.transport.queue_unset(QUEUE_IDX);
    }
}
