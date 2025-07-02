//! Common part shared across all the devices.

use bitflags::bitflags;

bitflags! {
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    /// The features supported by the virtio device.
    pub struct Feature: u64 {
        /// Mount the shared directory using the mount_tag method.
        const VIRTIO_9P_F_MOUNT_TAG = 1 << 0;

        /// device independent: notifies when the queue is empty.
        const NOTIFY_ON_EMPTY       = 1 << 24;
        /// device independent: allows any layout for the queue.
        const ANY_LAYOUT            = 1 << 27;
        /// device independent: Supports indirect descriptors in the virtio ring.
        const RING_INDIRECT_DESC    = 1 << 28;
        /// device independent: Supports event index feature in the virtio ring.
        const RING_EVENT_IDX        = 1 << 29;
        /// device independent: device independent feature: unused feature bit.
        const UNUSED                = 1 << 30;


        /// Detects legacy features for virtio version 1.0.
        const VERSION_1             = 1 << 32;
        /// Since virtio v1.1: allows the device to access the platform.
        const ACCESS_PLATFORM       = 1 << 33;
        /// Since virtio v1.1: supports packed virtio rings.
        const RING_PACKED           = 1 << 34;
        /// Since virtio v1.1: ensures descriptors are processed in order.
        const IN_ORDER              = 1 << 35;
        /// Since virtio v1.1: allows the device to order operations on the platform.
        const ORDER_PLATFORM        = 1 << 36;
        /// Since virtio v1.1: supports single root I/O virtualization.
        const SR_IOV                = 1 << 37;
        /// Since virtio v1.1: supports notification data feature.
        const NOTIFICATION_DATA     = 1 << 38;
    }
}
