#[cfg(test)]
pub mod fake;
pub mod mmio;

use crate::{PhysAddr, PAGE_SIZE};
use bitflags::bitflags;
use core::ptr::NonNull;

/// A VirtIO transport layer.
pub trait Transport {
    /// Gets the device type.
    fn device_type(&self) -> DeviceType;

    /// Reads device features.
    fn read_device_features(&mut self) -> u64;

    /// Writes device features.
    fn write_driver_features(&mut self, driver_features: u64);

    /// Gets the max size of queue.
    fn max_queue_size(&self) -> u32;

    /// Notifies the given queue on the device.
    fn notify(&mut self, queue: u32);

    /// Sets the device status.
    fn set_status(&mut self, status: DeviceStatus);

    /// Sets the guest page size.
    fn set_guest_page_size(&mut self, guest_page_size: u32);

    /// Sets up the given queue.
    fn queue_set(
        &mut self,
        queue: u32,
        size: u32,
        descriptors: PhysAddr,
        driver_area: PhysAddr,
        device_area: PhysAddr,
    );

    /// Returns whether the queue is in use, i.e. has a nonzero PFN or is marked as ready.
    fn queue_used(&mut self, queue: u32) -> bool;

    /// Acknowledges an interrupt.
    ///
    /// Returns true on success.
    fn ack_interrupt(&mut self) -> bool;

    /// Begins initializing the device.
    ///
    /// Ref: virtio 3.1.1 Device Initialization
    fn begin_init(&mut self, negotiate_features: impl FnOnce(u64) -> u64) {
        self.set_status(DeviceStatus::ACKNOWLEDGE);
        self.set_status(DeviceStatus::DRIVER);

        let features = self.read_device_features();
        self.write_driver_features(negotiate_features(features));
        self.set_status(DeviceStatus::FEATURES_OK);

        self.set_guest_page_size(PAGE_SIZE as u32);
    }

    /// Finishes initializing the device.
    fn finish_init(&mut self) {
        self.set_status(DeviceStatus::DRIVER_OK);
    }

    /// Gets the pointer to the config space.
    fn config_space(&self) -> NonNull<u64>;
}

bitflags! {
    /// The device status field.
    #[derive(Default)]
    pub struct DeviceStatus: u32 {
        /// Indicates that the guest OS has found the device and recognized it
        /// as a valid virtio device.
        const ACKNOWLEDGE = 1;

        /// Indicates that the guest OS knows how to drive the device.
        const DRIVER = 2;

        /// Indicates that something went wrong in the guest, and it has given
        /// up on the device. This could be an internal error, or the driver
        /// didn’t like the device for some reason, or even a fatal error
        /// during device operation.
        const FAILED = 128;

        /// Indicates that the driver has acknowledged all the features it
        /// understands, and feature negotiation is complete.
        const FEATURES_OK = 8;

        /// Indicates that the driver is set up and ready to drive the device.
        const DRIVER_OK = 4;

        /// Indicates that the device has experienced an error from which it
        /// can’t recover.
        const DEVICE_NEEDS_RESET = 64;
    }
}

/// Types of virtio devices.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum DeviceType {
    Invalid = 0,
    Network = 1,
    Block = 2,
    Console = 3,
    EntropySource = 4,
    MemoryBallooning = 5,
    IoMemory = 6,
    Rpmsg = 7,
    ScsiHost = 8,
    _9P = 9,
    Mac80211 = 10,
    RprocSerial = 11,
    VirtioCAIF = 12,
    MemoryBalloon = 13,
    GPU = 16,
    Timer = 17,
    Input = 18,
    Socket = 19,
    Crypto = 20,
    SignalDistributionModule = 21,
    Pstore = 22,
    IOMMU = 23,
    Memory = 24,
}
