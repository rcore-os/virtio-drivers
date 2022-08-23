use super::{DeviceStatus, Transport};
use crate::{
    queue::{AvailRing, DescFlags, Descriptor, UsedRing},
    DeviceType, PhysAddr,
};
use alloc::{sync::Arc, vec::Vec};
use core::{
    cmp::min,
    ptr::{self, NonNull},
    slice,
};
use std::sync::Mutex;

/// A fake implementation of [`Transport`] for unit tests.
#[derive(Debug)]
pub struct FakeTransport {
    pub device_type: DeviceType,
    pub max_queue_size: u32,
    pub device_features: u64,
    pub config_space: NonNull<u64>,
    pub state: Arc<Mutex<State>>,
}

impl Transport for FakeTransport {
    fn device_type(&self) -> DeviceType {
        self.device_type
    }

    fn read_device_features(&mut self) -> u64 {
        self.device_features
    }

    fn write_driver_features(&mut self, driver_features: u64) {
        self.state.lock().unwrap().driver_features = driver_features;
    }

    fn max_queue_size(&self) -> u32 {
        self.max_queue_size
    }

    fn notify(&mut self, queue: u32) {
        self.state.lock().unwrap().queues[queue as usize].notified = true;
    }

    fn set_status(&mut self, status: DeviceStatus) {
        self.state.lock().unwrap().status = status;
    }

    fn set_guest_page_size(&mut self, guest_page_size: u32) {
        self.state.lock().unwrap().guest_page_size = guest_page_size;
    }

    fn queue_set(
        &mut self,
        queue: u32,
        size: u32,
        descriptors: PhysAddr,
        driver_area: PhysAddr,
        device_area: PhysAddr,
    ) {
        let mut state = self.state.lock().unwrap();
        state.queues[queue as usize].size = size;
        state.queues[queue as usize].descriptors = descriptors;
        state.queues[queue as usize].driver_area = driver_area;
        state.queues[queue as usize].device_area = device_area;
    }

    fn queue_used(&mut self, queue: u32) -> bool {
        self.state.lock().unwrap().queues[queue as usize].descriptors != 0
    }

    fn ack_interrupt(&mut self) -> bool {
        let mut state = self.state.lock().unwrap();
        let pending = state.interrupt_pending;
        if pending {
            state.interrupt_pending = false;
        }
        pending
    }

    fn config_space(&self) -> NonNull<u64> {
        self.config_space
    }
}

#[derive(Debug, Default)]
pub struct State {
    pub status: DeviceStatus,
    pub driver_features: u64,
    pub guest_page_size: u32,
    pub interrupt_pending: bool,
    pub queues: Vec<QueueStatus>,
}

impl State {
    /// Simulate the device writing to the given queue.
    ///
    /// The fake device always uses descriptors in order.
    pub fn write_to_queue(&mut self, queue_size: u16, queue_index: usize, data: &[u8]) {
        let receive_queue = &self.queues[queue_index];
        assert_ne!(receive_queue.descriptors, 0);
        let descriptors = unsafe {
            slice::from_raw_parts(
                receive_queue.descriptors as *const Descriptor,
                queue_size as usize,
            )
        };
        let available_ring = receive_queue.driver_area as *const AvailRing;
        let used_ring = receive_queue.device_area as *mut UsedRing;
        unsafe {
            // Make sure there is actually at least one descriptor available to write to.
            assert_ne!((*available_ring).idx.read(), (*used_ring).idx.read());
            // The fake device always uses descriptors in order, like VIRTIO_F_IN_ORDER, so
            // `used_ring.idx` marks the next descriptor we should take from the available ring.
            let next_slot = (*used_ring).idx.read() & (queue_size - 1);
            let head_descriptor_index = (*available_ring).ring[next_slot as usize].read();
            let mut descriptor = &descriptors[head_descriptor_index as usize];

            // Loop through all descriptors in the chain, writing data to them.
            let mut remaining_data = data;
            loop {
                // Check the buffer and write to it.
                let flags = descriptor.flags.read();
                assert!(flags.contains(DescFlags::WRITE));
                let buffer_length = descriptor.len.read() as usize;
                let length_to_write = min(remaining_data.len(), buffer_length);
                ptr::copy(
                    remaining_data.as_ptr(),
                    descriptor.addr.read() as *mut u8,
                    length_to_write,
                );
                remaining_data = &remaining_data[length_to_write..];

                if flags.contains(DescFlags::NEXT) {
                    let next = descriptor.next.read() as usize;
                    descriptor = &descriptors[next];
                } else {
                    assert_eq!(remaining_data.len(), 0);
                    break;
                }
            }

            // Mark the buffer as used.
            (*used_ring).ring[next_slot as usize]
                .id
                .write(head_descriptor_index as u32);
            (*used_ring).ring[next_slot as usize]
                .len
                .write(data.len() as u32);
            (*used_ring).idx.update(|idx| *idx += 1);
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct QueueStatus {
    pub size: u32,
    pub descriptors: PhysAddr,
    pub driver_area: PhysAddr,
    pub device_area: PhysAddr,
    pub notified: bool,
}
