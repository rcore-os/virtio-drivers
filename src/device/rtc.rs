//! Driver for VirtIO RTC devices.

use core::num::NonZeroU64;

use crate::hal::Hal;
use crate::queue::VirtQueue;
use crate::transport::Transport;
use crate::{Error, Result};
use bitflags::Flags;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

const QUEUE_REQUEST: u16 = 0;
const QUEUE_ALARM: u16 = 1;
const SUPPORTED_FEATURES: Feature = Feature::RING_EVENT_IDX
    .union(Feature::RING_INDIRECT_DESC)
    .union(Feature::VERSION_1)
    .union(Feature::ACCESS_PLATFORM);

/// Driver for RTC devices based on VIRTIO 1.4.
pub struct VirtIORtc<H: Hal, T: Transport> {
    transport: T,
    negotiated_features: Feature,
    request_queue: VirtQueue<H, 8>,
}

impl<H: Hal, T: Transport> VirtIORtc<H, T> {
    /// Create a new VirtIO-RTC driver.
    pub fn new(mut transport: T) -> Result<Self> {
        let negotiated_features = transport.begin_init(SUPPORTED_FEATURES);

        let request_queue = VirtQueue::new(
            &mut transport,
            QUEUE_REQUEST,
            negotiated_features.contains(Feature::RING_INDIRECT_DESC),
            negotiated_features.contains(Feature::RING_EVENT_IDX),
            negotiated_features.contains(Feature::ACCESS_PLATFORM),
        )?;
        transport.finish_init();

        Ok(Self {
            transport,
            negotiated_features,
            request_queue,
        })
    }

    /// Return any unrecognized feature flag bits.
    ///
    /// Any bits that cannot be converted to a known device feature will be returned.
    pub fn invalid_feature_bits(&mut self) -> Option<NonZeroU64> {
        let device_feature_bits = self.transport.read_device_features();
        let device_features: Feature = Feature::from_bits_retain(device_feature_bits);
        NonZeroU64::new(device_features.unknown_bits())
    }

    /// Discovers the number of clocks.
    pub fn num_clocks(&mut self) -> Result<u16> {
        let req = VirtioRtcReqHead {
            msg_type: VIRTIO_RTC_REQ_CFG,
            ..VirtioRtcReqHead::default()
        };
        let resp: VirtioRtcRespCfg = self.request(req)?;
        Ok(resp.num_clocks)
    }

    /// Returns clock capabilities for a specific `clock_id`.
    pub fn clock_cap(&mut self, clock_id: u16) -> Result<ClockCapabilities> {
        let req = VirtioRtcReqClockCap {
            head: VirtioRtcReqHead {
                msg_type: VIRTIO_RTC_REQ_CLOCK_CAP,
                ..VirtioRtcReqHead::default()
            },
            clock_id,
            ..VirtioRtcReqClockCap::default()
        };
        let resp: VirtioRtcRespClockCap = self.request(req)?;
        let kind = match resp.type_ {
            VIRTIO_RTC_CLOCK_UTC => ClockType::Utc,
            VIRTIO_RTC_CLOCK_TAI => ClockType::Tai,
            VIRTIO_RTC_CLOCK_MONOTONIC => ClockType::Monotonic,
            VIRTIO_RTC_CLOCK_UTC_SMEARED => ClockType::UtcSmeared,
            VIRTIO_RTC_CLOCK_UTC_MAYBE_SMEARED => ClockType::UtcMaybeSmeared,
            _ => return Err(Error::Unsupported),
        };
        let leap_second_smearing = if kind == ClockType::UtcSmeared {
            match resp.leap_second_smearing {
                VIRTIO_RTC_SMEAR_UNSPECIFIED => None,
                VIRTIO_RTC_SMEAR_UTC_SLS => Some(SmearingVariant::UtcSls),
                VIRTIO_RTC_SMEAR_NOON_LINEAR => Some(SmearingVariant::NoonLinear),
                _ => return Err(Error::Unsupported),
            }
        } else {
            None
        };
        Ok(ClockCapabilities {
            kind,
            leap_second_smearing,
            alarm_capability: resp.flags & VIRTIO_RTC_FLAG_ALARM_CAP != 0,
        })
    }

    /// Read a clock's timestamp.
    pub fn read(&mut self, clock_id: u16) -> Result<u64> {
        let req = VirtioRtcReqRead {
            head: VirtioRtcReqHead {
                msg_type: VIRTIO_RTC_REQ_READ,
                ..VirtioRtcReqHead::default()
            },
            clock_id,
            ..VirtioRtcReqRead::default()
        };
        let resp: VirtioRtcRespRead = self.request(req)?;
        Ok(resp.clock_reading)
    }

    /// Helper method to send a request to the device and block for a response.
    fn request<Req: IntoBytes + Immutable, Rsp: FromBytes + Default + Immutable + IntoBytes>(
        &mut self,
        req: Req,
    ) -> Result<Rsp> {
        let mut resp = Rsp::new_zeroed();
        self.request_queue.add_notify_wait_pop(
            &[req.as_bytes()],
            &mut [resp.as_mut_bytes()],
            &mut self.transport,
        )?;
        let head = VirtioRtcRespHead::read_from_prefix(resp.as_bytes())
            .unwrap()
            .0;
        match head.status {
            VIRTIO_RTC_S_OK => Ok(resp),
            VIRTIO_RTC_S_EOPNOTSUPP => Err(Error::Unsupported),
            VIRTIO_RTC_S_ENODEV | VIRTIO_RTC_S_EINVAL => Err(Error::InvalidParam),
            VIRTIO_RTC_S_EIO => Err(Error::IoError),
            other => {
                log::error!("Invalid status response {other:#x}");
                Err(Error::IoError)
            }
        }
    }
}

impl<H: Hal, T: Transport> Drop for VirtIORtc<H, T> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(QUEUE_REQUEST);
    }
}

bitflags::bitflags! {
    /// virtio-rtc specific features
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct Feature: u64 {
        /// Alarm functionality
        const ALARM                 = 1 << 0;

        // device independent
        /// Legacy/Unused.
        const NOTIFY_ON_EMPTY       = 1 << 24; // legacy
        /// Legacy/Unused.
        const ANY_LAYOUT            = 1 << 27; // legacy
        /// Indirect descriptors
        const RING_INDIRECT_DESC    = 1 << 28;
        /// `avail_event` and `used_event` fields
        const RING_EVENT_IDX        = 1 << 29;
        /// Legacy/Unused.
        const UNUSED                = 1 << 30; // legacy
        /// VirtIO version 1 compliance
        const VERSION_1             = 1 << 32; // detect legacy

        // since virtio v1.1
        /// Limited device access to memory
        const ACCESS_PLATFORM       = 1 << 33;
        /// Packed virtqueue layout.
        const RING_PACKED           = 1 << 34;
        /// Optimisations for in-order buffer usage
        const IN_ORDER              = 1 << 35;
        /// Platform ordering for memory access
        const ORDER_PLATFORM        = 1 << 36;
        /// Single root I/O virtualization
        const SR_IOV                = 1 << 37;
        /// Extra data in device notifications
        const NOTIFICATION_DATA     = 1 << 38;

        // since virtio v1.2
        /// Driver uses the data provided by the device as a virtqueue identifier in available
        /// buffer notifications.
        const NOTIF_CONFIG_DATA     = 1 << 39;
        /// Driver can reset a queue individually
        const RING_RESET            = 1 << 40;

        // since virtio v1.3
        /// Device exposes one or more administration virtqueues.
        const ADMIN_VQ              = 1 << 41;

        // since virtio v1.4
        /// the driver can suspend the device by set the `SUSPEND` bit to 1.
        const SUSPEND               = 1 << 43;
    }
}

/// common request header
#[doc(alias = "virtio_rtc_req_head")]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcReqHead {
    msg_type: u16,
    reserved: [u8; 6],
}

/// common response header
#[doc(alias = "virtio_rtc_resp_head")]
#[derive(Copy, Clone, Debug, Default, Immutable, FromBytes, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcRespHead {
    status: u8,
    reserved: [u8; 7],
}

const VIRTIO_RTC_S_OK: u8 = 0;
const VIRTIO_RTC_S_EOPNOTSUPP: u8 = 2;
const VIRTIO_RTC_S_ENODEV: u8 = 3;
const VIRTIO_RTC_S_EINVAL: u8 = 4;
const VIRTIO_RTC_S_EIO: u8 = 5;

// Clock types:

const VIRTIO_RTC_CLOCK_UTC: u8 = 0;
const VIRTIO_RTC_CLOCK_TAI: u8 = 1;
const VIRTIO_RTC_CLOCK_MONOTONIC: u8 = 2;
const VIRTIO_RTC_CLOCK_UTC_SMEARED: u8 = 3;
const VIRTIO_RTC_CLOCK_UTC_MAYBE_SMEARED: u8 = 4;

// Smearing Variants

const VIRTIO_RTC_SMEAR_UNSPECIFIED: u8 = 0;
const VIRTIO_RTC_SMEAR_NOON_LINEAR: u8 = 1;
const VIRTIO_RTC_SMEAR_UTC_SLS: u8 = 2;

// Control Requests

/// Discovers the number of clocks
const VIRTIO_RTC_REQ_CFG: u16 = 0x1000;

#[doc(alias = "virtio_rtc_req_cfg")]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcReqCfg {
    head: VirtioRtcReqHead,
}

#[doc(alias = "virtio_rtc_resp_cfg")]
#[derive(Copy, Clone, Debug, Default, Immutable, FromBytes, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcRespCfg {
    head: VirtioRtcRespHead,
    num_clocks: u16,
    reserved: [u8; 6],
}

/// Discovers the capabilities of the clock identified by the `clock_id` field.
const VIRTIO_RTC_REQ_CLOCK_CAP: u16 = 0x1001;

#[doc(alias = "virtio_rtc_req_clock_cap")]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcReqClockCap {
    head: VirtioRtcReqHead,
    clock_id: u16,
    reserved: [u8; 6],
}

#[doc(alias = "virtio_rtc_resp_clock_cap")]
#[derive(Copy, Clone, Debug, Default, Immutable, FromBytes, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcRespClockCap {
    head: VirtioRtcRespHead,
    type_: u8,
    leap_second_smearing: u8,
    flags: u8,
    reserved: [u8; 5],
}

/// Clock source variant.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum ClockType {
    /// Uses the UTC (Coordinated Universal Time) time standard. This clock uses the time epoch of `January 1, 1970, 00:00 UTC`. This is the same epoch as Unix time. The clock’s seconds since the epoch are related to UTC time as defined by the Unix epoch.
    ///

    /// This clock observes positive and negative leap seconds as announced by standard bodies.
    ///
    /// At the start of leap seconds, the clock steps accordingly.
    Utc = VIRTIO_RTC_CLOCK_UTC,
    /// Uses the TAI (International Atomic Time) time standard.
    ///
    /// This clock uses the time epoch of `January 1, 1970, 00:00 TAI`.
    Tai = VIRTIO_RTC_CLOCK_TAI,
    /// Uses monotonic physical time (SI seconds subdivisions) since some unspecified epoch.
    ///
    /// The epoch is before or during device reset.
    Monotonic = VIRTIO_RTC_CLOCK_MONOTONIC,
    /// Deviates from the UTC standard by smearing time in the vicinity of a leap second.
    ///
    /// This avoids clock steps due to UTC leap seconds. Otherwise, this clock is similar to
    /// [`ClockType::Utc`].
    UtcSmeared = VIRTIO_RTC_CLOCK_UTC_SMEARED,
    /// This clock either deviates from the UTC standard by smearing time in the vicinity of a leap
    /// second (similar to [`ClockType::UtcSmeared`]), or steps at the start of leap seconds like
    /// [`ClockType::Utc`].
    ///
    /// A clock of type [`ClockType::UtcMaybeSmeared`] can change this behavior for every leap second.
    UtcMaybeSmeared = VIRTIO_RTC_CLOCK_UTC_MAYBE_SMEARED,
}

/// Leap second smearing variants describe the deviation from the UTC standard in the vicinity of a leap second.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum SmearingVariant {
    /// Specifies a linear smear from noon prior to the leap second until noon after the leap second.
    NoonLinear = VIRTIO_RTC_SMEAR_NOON_LINEAR,
    /// Specifies a linear smear as per the [`UTC-SLS`](https://www.cl.cam.ac.uk/~mgk25/time/utc-sls/) proposal.
    UtcSls = VIRTIO_RTC_SMEAR_UTC_SLS,
}

/// The capabilities of a specific clock.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ClockCapabilities {
    /// See [`ClockType`].
    pub kind: ClockType,
    /// See [`SmearingVariant`].
    ///
    /// If `None`, it's unspecified.
    pub leap_second_smearing: Option<SmearingVariant>,
    /// If `true`, the clock supports an alarm.
    pub alarm_capability: bool,
}

/// If `VIRTIO_RTC_F_ALARM` has been negotiated, the `VIRTIO_RTC_FLAG_ALARM_CAP`
/// flag indicates that the clock supports an alarm.
const VIRTIO_RTC_FLAG_ALARM_CAP: u8 = 1;

/// Discovers whether the device supports cross-timestamping for a particular
/// pair of clock and hardware counter.
const VIRTIO_RTC_REQ_CROSS_CAP: u16 = 0x1002;

#[doc(alias = "virtio_rtc_req_cross_cap")]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcReqCrossCap {
    head: VirtioRtcReqHead,
    clock_id: u16,
    hw_counter: u8,
    reserved: [u8; 5],
}

#[doc(alias = "virtio_rtc_resp_cross_cap")]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcRespCrossCap {
    head: VirtioRtcRespHead,
    flags: u8,
    reserved: [u8; 7],
}

/// The clock supports cross-timestamping for the particular clock and hardware
/// counter.
const VIRTIO_RTC_FLAG_CROSS_CAP: u8 = 1;

/// Reads the clock identified by the `clock_id` field. The device supports this
/// request for every clock.
const VIRTIO_RTC_REQ_READ: u16 = 0x0001;

#[doc(alias = "virtio_rtc_req_read")]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcReqRead {
    head: VirtioRtcReqHead,
    clock_id: u16,
    reserved: [u8; 6],
}

#[doc(alias = "virtio_rtc_resp_read")]
#[derive(Copy, Clone, Debug, Default, Immutable, FromBytes, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcRespRead {
    head: VirtioRtcRespHead,
    clock_reading: u64,
}

/// Returns a cross-timestamp for the clock identified by the `clock_id` field.
const VIRTIO_RTC_REQ_READ_CROSS: u16 = 0x0002;

#[doc(alias = "virtio_rtc_req_read_cross")]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcReqReadCross {
    head: VirtioRtcReqHead,
    clock_id: u16,
    hw_counter: u8,
    reserved: [u8; 5],
}

#[doc(alias = "virtio_rtc_resp_read_cross")]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioRtcRespReadCross {
    head: VirtioRtcRespHead,
    clock_reading: u64,
    counter_cycles: u64,
}
