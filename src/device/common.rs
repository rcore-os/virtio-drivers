//! Common part shared across all the devices.

#[macro_export]
/// Define device features
macro_rules! feature_bitflag {
    (
       $(#[$meta:meta])*
        $vis:vis struct $feat:ident: u64 {
            $(
                $(#[$inner:ident $($args:tt)*])*
                const $feat_name:ident = 1 << $bit:literal;
            )*
        }
    ) => {
        $(
            #[allow(unused_comparisons, reason = "false positive")]
            // Section 2.2 Feature Bits (OASIS virtio): feature bit allocation for device is:
            // 0 to 23, 41, 42 and 50 to 127
            const _: () = assert!($bit < 24u8 || $bit == 41_u8 || $bit == 42_u8 || ($bit > 49_u8 && $bit < 128_u8), concat!("Invalid feature bit for ", stringify!($feat_name)));
        )*
        ::bitflags::bitflags! {
            $(#[$meta])*
            $vis struct $feat: u64 {
                $(
                    $(#[$inner $($args)*])*
                    const $feat_name = 1 << $bit;
                )*
                /// Legacy: The device must issue a used buffer notification when it runs out of available
                /// descriptors, even if notifications are suppressed.
                const NOTIFY_ON_EMPTY       = 1 << 24;

                /// Legacy: The device accepts arbitrary descriptor layouts.
                const ANY_LAYOUT            = 1 << 27;

                /// The device can use descriptors with the indirect flag set.
                const RING_INDIRECT_DESC    = 1 << 28;

                /// The `used_event` and `avail_event` fields can be used.
                const RING_EVENT_IDX        = 1 << 29;

                /// Legacy: Used by QEMU's implemenation for experimental early versions of VirtIO which
                /// didn't perform correct feature notification.
                const UNUSED                = 1 << 30;

                /// Supports VirtIO version 1 or higher, rather than the legacy version.
                const VERSION_1             = 1 << 32;

                // since virtio v1.1:

                /// The device can be used on a platform where device access to memory is limited or
                /// translated.
                const ACCESS_PLATFORM       = 1 << 33;

                /// Use packed virtqueue layout.
                const RING_PACKED           = 1 << 34;

                /// The device uses buffers in the same order that they were made available.
                const IN_ORDER              = 1 << 35;

                /// Memory access by the driver and device are ordered in a way described by the platform.
                const ORDER_PLATFORM        = 1 << 36;

                /// The device supports Single Root I/O Virtualisation.
                const SR_IOV                = 1 << 37;

                /// The driver passes extra data in its device notifications.
                const NOTIFICATION_DATA     = 1 << 38;

                // since virtio v1.2

                /// The driver uses the data provided by the device as a virtqueue identifier in available buffer notifications.
                const NOTIF_CONFIG_DATA     = 1 << 39;

                /// the driver can reset a queue individually.
                const RING_RESET            = 1 << 40;

                // since virtio v1.3

                /// The device exposes one or more administration virtqueues.
                const ADMIN_VQ              = 1 << 41;

                /// The driver can suspend the device by set the `SUSPEND` bit to `1`.
                const SUSPEND               = 1 << 43;
            }
        }
    }
}

feature_bitflag! {
    /// Common device-independent VirtIO device features.
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    pub struct Feature: u64 {}
}
