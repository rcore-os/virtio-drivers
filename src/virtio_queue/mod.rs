//! VirtIO queues.

pub mod packed_queue;
pub mod split_queue;

use crate::transport::Transport;
use crate::Hal;
use crate::Result;

pub enum VirtQueue<H: Hal, const SIZE: usize> {
    Packedqueue(packed_queue::PackedQueue<H, SIZE>),
    Splitqueue(split_queue::SplitQueue<H, SIZE>),
}

impl<H: Hal, const SIZE: usize> VirtQueue<H, SIZE> {
    pub fn add_notify_wait_pop<'a>(
        &mut self,
        inputs: &'a [&'a [u8]],
        outputs: &'a mut [&'a mut [u8]],
        transport: &mut impl Transport,
        support_event: bool,
    ) -> Result<u32> {
        match self {
            Self::Packedqueue(packedqueue) => {
                packedqueue.add_notify_wait_pop(inputs, outputs, transport, support_event)
            }
            Self::Splitqueue(splitqueue) => {
                splitqueue.add_notify_wait_pop(inputs, outputs, transport, support_event)
            }
        }
    }

    pub unsafe fn add<'a, 'b>(
        &mut self,
        inputs: &'a [&'b [u8]],
        outputs: &'a mut [&'b mut [u8]],
    ) -> Result<u16> {
        match self {
            Self::Packedqueue(packedqueue) => packedqueue.add(inputs, outputs),
            Self::Splitqueue(splitqueue) => splitqueue.add(inputs, outputs),
        }
    }

    pub fn should_notify(&self, support_event: bool) -> bool {
        match self {
            Self::Packedqueue(packedqueue) => packedqueue.should_notify(support_event),
            Self::Splitqueue(splitqueue) => splitqueue.should_notify(support_event),
        }
    }

    /// Returns whether there is a used element that can be popped.
    pub fn can_pop(&self) -> bool {
        match self {
            Self::Packedqueue(packedqueue) => packedqueue.can_pop(),
            Self::Splitqueue(splitqueue) => splitqueue.can_pop(),
        }
    }

    /// pop used
    // TODO: will be deleted in the further
    pub unsafe fn pop_used_async<'a>(&mut self, token: u16) -> Result<u32> {
        match self {
            Self::Packedqueue(packedqueue) => packedqueue.pop_used_async(token),
            Self::Splitqueue(splitqueue) => splitqueue.pop_used_async(token),
        }
    }

    pub unsafe fn pop_used<'a>(
        &mut self,
        token: u16,
        inputs: &'a [&'a [u8]],
        outputs: &'a mut [&'a mut [u8]],
    ) -> Result<u32> {
        match self {
            Self::Packedqueue(packedqueue) => packedqueue.pop_used(token, inputs, outputs),
            Self::Splitqueue(splitqueue) => splitqueue.pop_used(token, inputs, outputs),
        }
    }
}
