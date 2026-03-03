//! Driver for VirtIO 9p devices.

use alloc::string::String;
use alloc::vec::Vec;
use log::warn;

use super::common::Feature;
use crate::{Error, Hal, Result, queue::VirtQueue, transport::Transport};

const QUEUE: u16 = 0;
const QUEUE_SIZE: usize = 16;
const P9_HEADER_SIZE: usize = 7; // size (4) + type (1) + tag (2)
const SUPPORTED_FEATURES: Feature = Feature::RING_INDIRECT_DESC
    .union(Feature::RING_EVENT_IDX)
    .union(Feature::VERSION_1);

/// Driver for a VirtIO 9p device.
pub struct VirtIO9p<H: Hal, T: Transport> {
    transport: T,
    queue: VirtQueue<H, QUEUE_SIZE>,
    mount_tag: String,
}

impl<H: Hal, T: Transport> VirtIO9p<H, T> {
    /// Create a new VirtIO 9p driver.
    pub fn new(mut transport: T) -> Result<Self> {
        let features = transport.begin_init(SUPPORTED_FEATURES);

        let queue = VirtQueue::new(
            &mut transport,
            QUEUE,
            features.contains(Feature::RING_INDIRECT_DESC),
            features.contains(Feature::RING_EVENT_IDX),
        )?;
        transport.finish_init();

        let mount_tag = read_mount_tag(&transport)?;

        Ok(Self {
            transport,
            queue,
            mount_tag,
        })
    }

    /// Returns the mount tag reported by the device.
    pub fn mount_tag(&self) -> &str {
        &self.mount_tag
    }

    /// Sends a raw 9p request and waits for the response.
    pub fn request(&mut self, req: &[u8], resp: &mut [u8]) -> Result<u32> {
        if req.is_empty() || resp.len() < P9_HEADER_SIZE {
            return Err(Error::InvalidParam);
        }
        let used_len = self
            .queue
            .add_notify_wait_pop(&[req], &mut [resp], &mut self.transport)?;

        let size = u32::from_le_bytes([resp[0], resp[1], resp[2], resp[3]]);
        if size != used_len {
            warn!(
                "virtio-9p response size mismatch: size from header is {size} but used length is {used_len}"
            );
            return Err(Error::IoError);
        }
        Ok(used_len)
    }
}

fn read_mount_tag<T: Transport>(transport: &T) -> Result<String> {
    transport.read_consistent(|| {
        let tag_len: u16 = transport.read_config_space(0)?;
        if tag_len == 0 {
            return Err(Error::InvalidParam);
        }

        let mut bytes = Vec::with_capacity(tag_len as usize);
        for idx in 0..tag_len as usize {
            let b: u8 = transport.read_config_space(2 + idx)?;
            bytes.push(b);
        }

        Ok(String::from_utf8(bytes)?)
    })
}
