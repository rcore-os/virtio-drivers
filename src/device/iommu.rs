//! Driver for VirtIO IOMMU devices.
//!
//! The IOMMU device manages DMA remapping for endpoints. It translates I/O
//! virtual addresses to physical addresses using a request/response protocol
//! on the request virtqueue, and reports translation faults on the event
//! virtqueue.

use crate::config::{ReadOnly, read_config};
use crate::hal::Hal;
use crate::queue::VirtQueue;
use crate::transport::Transport;
use crate::{Error, Result};
use log::info;
use zerocopy::{FromBytes, FromZeros, Immutable, IntoBytes, KnownLayout};

const QUEUE_REQUEST: u16 = 0;
const QUEUE_EVENT: u16 = 1;
const QUEUE_SIZE: u16 = 64;

const SUPPORTED_FEATURES: Feature = Feature::INPUT_RANGE
    .union(Feature::DOMAIN_RANGE)
    .union(Feature::MAP_UNMAP)
    .union(Feature::PROBE)
    .union(Feature::RING_INDIRECT_DESC)
    .union(Feature::RING_EVENT_IDX)
    .union(Feature::VERSION_1)
    .union(Feature::ACCESS_PLATFORM);

// Request types
const VIRTIO_IOMMU_T_ATTACH: u8 = 0x01;
const VIRTIO_IOMMU_T_DETACH: u8 = 0x02;
const VIRTIO_IOMMU_T_MAP: u8 = 0x03;
const VIRTIO_IOMMU_T_UNMAP: u8 = 0x04;
const VIRTIO_IOMMU_T_PROBE: u8 = 0x05;

// Status codes
const VIRTIO_IOMMU_S_OK: u8 = 0x00;
const VIRTIO_IOMMU_S_IOERR: u8 = 0x01;
const VIRTIO_IOMMU_S_UNSUPP: u8 = 0x02;
const VIRTIO_IOMMU_S_DEVERR: u8 = 0x03;
const VIRTIO_IOMMU_S_INVAL: u8 = 0x04;
const VIRTIO_IOMMU_S_RANGE: u8 = 0x05;
const VIRTIO_IOMMU_S_NOENT: u8 = 0x06;
const VIRTIO_IOMMU_S_FAULT: u8 = 0x07;
const VIRTIO_IOMMU_S_NOMEM: u8 = 0x08;

// MAP flags
const VIRTIO_IOMMU_MAP_F_READ: u32 = 1 << 0;
const VIRTIO_IOMMU_MAP_F_WRITE: u32 = 1 << 1;
const VIRTIO_IOMMU_MAP_F_MMIO: u32 = 1 << 2;

// ATTACH flags
const VIRTIO_IOMMU_ATTACH_F_BYPASS: u32 = 1 << 0;

// Fault reason codes
const VIRTIO_IOMMU_FAULT_R_UNKNOWN: u8 = 0;
const VIRTIO_IOMMU_FAULT_R_DOMAIN: u8 = 1;
const VIRTIO_IOMMU_FAULT_R_MAPPING: u8 = 2;

// Fault flags
const VIRTIO_IOMMU_FAULT_F_READ: u32 = 1 << 0;
const VIRTIO_IOMMU_FAULT_F_WRITE: u32 = 1 << 1;
const VIRTIO_IOMMU_FAULT_F_EXEC: u32 = 1 << 2;
const VIRTIO_IOMMU_FAULT_F_ADDRESS: u32 = 1 << 8;

// Probe types
const VIRTIO_IOMMU_PROBE_T_RESV_MEM: u16 = 1;

// Reserved memory subtypes
const VIRTIO_IOMMU_RESV_MEM_T_RESERVED: u8 = 0;
const VIRTIO_IOMMU_RESV_MEM_T_MSI: u8 = 1;

/// Driver for a VirtIO IOMMU device.
pub struct VirtIOIommu<H: Hal, T: Transport> {
    transport: T,
    negotiated_features: Feature,
    request_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    event_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
}

impl<H: Hal, T: Transport> VirtIOIommu<H, T> {
    /// Create a new VirtIO-IOMMU driver.
    pub fn new(mut transport: T) -> Result<Self> {
        let negotiated_features = transport.begin_init(SUPPORTED_FEATURES);

        let page_size_mask = transport.read_consistent(|| {
            Ok(
                (read_config!(transport, IommuConfig, page_size_mask_low)? as u64)
                    | ((read_config!(transport, IommuConfig, page_size_mask_high)? as u64) << 32),
            )
        })?;
        let input_start = transport.read_consistent(|| {
            Ok(
                (read_config!(transport, IommuConfig, input_range_start_low)? as u64)
                    | ((read_config!(transport, IommuConfig, input_range_start_high)? as u64)
                        << 32),
            )
        })?;
        let input_end = transport.read_consistent(|| {
            Ok(
                (read_config!(transport, IommuConfig, input_range_end_low)? as u64)
                    | ((read_config!(transport, IommuConfig, input_range_end_high)? as u64) << 32),
            )
        })?;
        info!(
            "iommu device: page_size_mask=0x{:x}, input_range=0x{:x}-0x{:x}",
            page_size_mask, input_start, input_end
        );

        if negotiated_features.contains(Feature::DOMAIN_RANGE) {
            let domain_start = read_config!(transport, IommuConfig, domain_range_start)?;
            let domain_end = read_config!(transport, IommuConfig, domain_range_end)?;
            info!("iommu device: domain_range={}-{}", domain_start, domain_end);
        }

        let request_queue = VirtQueue::new(
            &mut transport,
            QUEUE_REQUEST,
            negotiated_features.contains(Feature::RING_INDIRECT_DESC),
            negotiated_features.contains(Feature::RING_EVENT_IDX),
            negotiated_features.contains(Feature::ACCESS_PLATFORM),
        )?;
        let event_queue = VirtQueue::new(
            &mut transport,
            QUEUE_EVENT,
            negotiated_features.contains(Feature::RING_INDIRECT_DESC),
            negotiated_features.contains(Feature::RING_EVENT_IDX),
            negotiated_features.contains(Feature::ACCESS_PLATFORM),
        )?;
        transport.finish_init();

        Ok(Self {
            transport,
            negotiated_features,
            request_queue,
            event_queue,
        })
    }

    /// Returns the supported page size mask from the config space.
    pub fn page_size_mask(&mut self) -> Result<u64> {
        self.transport.read_consistent(|| {
            Ok(
                (read_config!(self.transport, IommuConfig, page_size_mask_low)? as u64)
                    | ((read_config!(self.transport, IommuConfig, page_size_mask_high)? as u64)
                        << 32),
            )
        })
    }

    /// Returns the supported IOVA input range from the config space.
    pub fn input_range(&mut self) -> Result<(u64, u64)> {
        let start = self.transport.read_consistent(|| {
            Ok(
                (read_config!(self.transport, IommuConfig, input_range_start_low)? as u64)
                    | ((read_config!(self.transport, IommuConfig, input_range_start_high)? as u64)
                        << 32),
            )
        })?;
        let end = self.transport.read_consistent(|| {
            Ok(
                (read_config!(self.transport, IommuConfig, input_range_end_low)? as u64)
                    | ((read_config!(self.transport, IommuConfig, input_range_end_high)? as u64)
                        << 32),
            )
        })?;
        Ok((start, end))
    }

    /// Returns the domain ID range from the config space.
    pub fn domain_range(&mut self) -> Result<(u32, u32)> {
        let start = read_config!(self.transport, IommuConfig, domain_range_start)?;
        let end = read_config!(self.transport, IommuConfig, domain_range_end)?;
        Ok((start, end))
    }

    /// Returns the probe buffer size from the config space.
    pub fn probe_size(&mut self) -> Result<u32> {
        read_config!(self.transport, IommuConfig, probe_size)
    }

    /// Attaches an endpoint to a domain.
    ///
    /// If `bypass` is true and the BYPASS feature is enabled, the domain
    /// operates in bypass mode.
    pub fn attach(&mut self, domain: u32, endpoint: u32, bypass: bool) -> Result {
        let flags = if bypass {
            VIRTIO_IOMMU_ATTACH_F_BYPASS
        } else {
            0
        };
        let req = VirtioIommuReqAttach {
            head: VirtioIommuReqHead {
                type_: VIRTIO_IOMMU_T_ATTACH,
                reserved: Default::default(),
            },
            domain,
            endpoint,
            flags,
            reserved: [0; 4],
            tail: VirtioIommuReqTail {
                status: 0,
                reserved: Default::default(),
            },
        };
        let resp: VirtioIommuReqAttach = self.request(req)?;
        iommu_status_to_result(resp.tail.status)
    }

    /// Detaches an endpoint from a domain.
    pub fn detach(&mut self, domain: u32, endpoint: u32) -> Result {
        let req = VirtioIommuReqDetach {
            head: VirtioIommuReqHead {
                type_: VIRTIO_IOMMU_T_DETACH,
                reserved: Default::default(),
            },
            domain,
            endpoint,
            reserved: [0; 8],
            tail: VirtioIommuReqTail {
                status: 0,
                reserved: Default::default(),
            },
        };
        let resp: VirtioIommuReqDetach = self.request(req)?;
        iommu_status_to_result(resp.tail.status)
    }

    /// Maps a virtual address range to a physical address range in a domain.
    pub fn map(
        &mut self,
        domain: u32,
        virt_start: u64,
        virt_end: u64,
        phys_start: u64,
        flags: u32,
    ) -> Result {
        let req = VirtioIommuReqMap {
            head: VirtioIommuReqHead {
                type_: VIRTIO_IOMMU_T_MAP,
                reserved: Default::default(),
            },
            domain,
            virt_start,
            virt_end,
            phys_start,
            flags,
            tail: VirtioIommuReqTail {
                status: 0,
                reserved: Default::default(),
            },
        };
        let resp: VirtioIommuReqMap = self.request(req)?;
        iommu_status_to_result(resp.tail.status)
    }

    /// Unmaps a virtual address range from a domain.
    pub fn unmap(&mut self, domain: u32, virt_start: u64, virt_end: u64) -> Result {
        let req = VirtioIommuReqUnmap {
            head: VirtioIommuReqHead {
                type_: VIRTIO_IOMMU_T_UNMAP,
                reserved: Default::default(),
            },
            domain,
            virt_start,
            virt_end,
            reserved: [0; 4],
            tail: VirtioIommuReqTail {
                status: 0,
                reserved: Default::default(),
            },
        };
        let resp: VirtioIommuReqUnmap = self.request(req)?;
        iommu_status_to_result(resp.tail.status)
    }

    /// Probes an endpoint for reserved memory regions.
    ///
    /// The caller provides a buffer large enough to hold the probe response
    /// (header + properties + tail). The buffer must be at least as large as
    /// the value returned by [`probe_size`](Self::probe_size).
    pub fn probe(&mut self, endpoint: u32, buf: &mut [u8]) -> Result<usize> {
        let len = buf.len();
        buf[..4].copy_from_slice(
            VirtioIommuReqHead {
                type_: VIRTIO_IOMMU_T_PROBE,
                reserved: Default::default(),
            }
            .as_bytes(),
        );
        buf[4..8].copy_from_slice(&endpoint.to_le_bytes());

        let (input, output) = buf.split_at_mut(8);
        self.request_queue
            .add_notify_wait_pop(&[input], &mut [output], &mut self.transport)?;

        let tail_offset = buf.len() - 4;
        let status = buf[tail_offset];
        iommu_status_to_result(status)?;
        Ok(len)
    }

    /// Returns true if there is a fault event available on the event queue.
    pub fn fault_available(&self) -> bool {
        self.event_queue.can_pop()
    }

    /// Pops a fault event from the event queue, if one is available.
    pub fn pop_fault(&mut self) -> Result<Option<VirtioIommuFault>> {
        if !self.event_queue.can_pop() {
            return Ok(None);
        }
        let mut fault = VirtioIommuFault::new_zeroed();
        let token = self.event_queue.peek_used().unwrap();
        // SAFETY: fault buffer is valid for the duration of pop_used.
        unsafe {
            self.event_queue
                .pop_used(token, &[], &mut [fault.as_mut_bytes()])?;
        }
        Ok(Some(fault))
    }

    /// Helper method to send a request and block for a response.
    fn request<Req: IntoBytes + Immutable, Rsp: FromBytes + IntoBytes + Immutable>(
        &mut self,
        req: Req,
    ) -> Result<Rsp> {
        let mut resp = Rsp::new_zeroed();
        self.request_queue.add_notify_wait_pop(
            &[req.as_bytes()],
            &mut [resp.as_mut_bytes()],
            &mut self.transport,
        )?;
        Ok(resp)
    }
}

impl<H: Hal, T: Transport> Drop for VirtIOIommu<H, T> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(QUEUE_REQUEST);
        self.transport.queue_unset(QUEUE_EVENT);
    }
}

fn iommu_status_to_result(status: u8) -> Result {
    match status {
        VIRTIO_IOMMU_S_OK => Ok(()),
        VIRTIO_IOMMU_S_IOERR => Err(Error::IoError),
        VIRTIO_IOMMU_S_UNSUPP => Err(Error::Unsupported),
        VIRTIO_IOMMU_S_DEVERR => Err(Error::IoError),
        VIRTIO_IOMMU_S_INVAL => Err(Error::InvalidParam),
        VIRTIO_IOMMU_S_RANGE => Err(Error::InvalidParam),
        VIRTIO_IOMMU_S_NOENT => Err(Error::InvalidParam),
        VIRTIO_IOMMU_S_FAULT => Err(Error::IoError),
        VIRTIO_IOMMU_S_NOMEM => Err(Error::DmaError),
        other => {
            log::error!("Invalid IOMMU status response {other:#x}");
            Err(Error::IoError)
        }
    }
}

/// Common IOMMU request header.
#[derive(Copy, Clone, Debug, Default, FromBytes, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioIommuReqHead {
    type_: u8,
    reserved: [u8; 3],
}

/// Common IOMMU request tail.
#[derive(Copy, Clone, Debug, Default, FromBytes, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioIommuReqTail {
    status: u8,
    reserved: [u8; 3],
}

/// ATTTACH request.
#[derive(Copy, Clone, Debug, Default, FromBytes, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioIommuReqAttach {
    head: VirtioIommuReqHead,
    domain: u32,
    endpoint: u32,
    flags: u32,
    reserved: [u8; 4],
    tail: VirtioIommuReqTail,
}

/// DETACH request.
#[derive(Copy, Clone, Debug, Default, FromBytes, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioIommuReqDetach {
    head: VirtioIommuReqHead,
    domain: u32,
    endpoint: u32,
    reserved: [u8; 8],
    tail: VirtioIommuReqTail,
}

/// MAP request.
#[derive(Copy, Clone, Debug, Default, FromBytes, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioIommuReqMap {
    head: VirtioIommuReqHead,
    domain: u32,
    virt_start: u64,
    virt_end: u64,
    phys_start: u64,
    flags: u32,
    tail: VirtioIommuReqTail,
}

/// UNMAP request.
#[derive(Copy, Clone, Debug, Default, FromBytes, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
struct VirtioIommuReqUnmap {
    head: VirtioIommuReqHead,
    domain: u32,
    virt_start: u64,
    virt_end: u64,
    reserved: [u8; 4],
    tail: VirtioIommuReqTail,
}

/// A probe property header.
#[derive(Copy, Clone, Debug, Default, Immutable, FromBytes, IntoBytes, KnownLayout)]
#[repr(C)]
pub struct VirtioIommuProbeProperty {
    /// Property type.
    pub type_: u16,
    /// Property length in bytes (including this header).
    pub length: u16,
}

/// Reserved memory region probe property.
#[derive(Copy, Clone, Debug, Default, Immutable, FromBytes, IntoBytes, KnownLayout)]
#[repr(C)]
pub struct VirtioIommuProbeResvMem {
    /// Property header.
    pub head: VirtioIommuProbeProperty,
    /// Subtype (VIRTIO_IOMMU_RESV_MEM_T_RESERVED or _MSI).
    pub subtype: u8,
    reserved: [u8; 3],
    /// Start of reserved region.
    pub start: u64,
    /// End of reserved region.
    pub end: u64,
}

/// A fault reported by the IOMMU device on the event virtqueue.
#[derive(Copy, Clone, Debug, Default, Immutable, FromBytes, IntoBytes, KnownLayout)]
#[repr(C)]
pub struct VirtioIommuFault {
    reason: u8,
    reserved: [u8; 3],
    flags: u32,
    endpoint: u32,
    reserved2: [u8; 4],
    address: u64,
}

impl VirtioIommuFault {
    /// Returns the fault reason code.
    pub fn reason(&self) -> u8 {
        self.reason
    }

    /// Returns the endpoint that caused the fault, if known.
    pub fn endpoint(&self) -> u32 {
        self.endpoint
    }

    /// Returns the fault address.
    pub fn address(&self) -> u64 {
        self.address
    }

    /// Returns the fault flags bitmask.
    pub fn flags(&self) -> u32 {
        self.flags
    }
}

/// IOMMU config space.
#[derive(FromBytes, Immutable, IntoBytes)]
#[repr(C)]
struct IommuConfig {
    page_size_mask_low: ReadOnly<u32>,
    page_size_mask_high: ReadOnly<u32>,
    input_range_start_low: ReadOnly<u32>,
    input_range_start_high: ReadOnly<u32>,
    input_range_end_low: ReadOnly<u32>,
    input_range_end_high: ReadOnly<u32>,
    domain_range_start: ReadOnly<u32>,
    domain_range_end: ReadOnly<u32>,
    probe_size: ReadOnly<u32>,
}

bitflags::bitflags! {
    /// virtio-iommu specific features
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct Feature: u64 {
        /// The device provides an input range.
        const INPUT_RANGE     = 1 << 0;
        /// The device provides a domain range.
        const DOMAIN_RANGE    = 1 << 1;
        /// The device supports map/unmap.
        const MAP_UNMAP       = 1 << 2;
        /// The device supports bypass mode.
        const BYPASS          = 1 << 3;
        /// The device supports probing endpoints.
        const PROBE           = 1 << 4;
        /// The device supports MMIO mappings.
        const MMIO            = 1 << 5;
        /// The device exposes bypass config field.
        const BYPASS_CONFIG   = 1 << 6;

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        hal::fake::FakeHal,
        transport::{
            DeviceType,
            fake::{FakeTransport, QueueStatus, State},
        },
    };
    use alloc::{sync::Arc, vec};
    use std::{sync::Mutex, thread};

    fn make_queue_status(count: usize) -> Vec<QueueStatus> {
        (0..count).map(|_| QueueStatus::default()).collect()
    }

    #[test]
    fn config() {
        let config_space = IommuConfig {
            page_size_mask_low: ReadOnly::new(0x1000 as u32),
            page_size_mask_high: ReadOnly::new(0),
            input_range_start_low: ReadOnly::new(0 as u32),
            input_range_start_high: ReadOnly::new(0),
            input_range_end_low: ReadOnly::new(0xFFFF_FFFF as u32),
            input_range_end_high: ReadOnly::new(0),
            domain_range_start: ReadOnly::new(0),
            domain_range_end: ReadOnly::new(65535),
            probe_size: ReadOnly::new(512),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::IOMMU,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: (Feature::INPUT_RANGE
                | Feature::DOMAIN_RANGE
                | Feature::MAP_UNMAP
                | Feature::PROBE)
                .bits(),
            state: state.clone(),
        };
        let mut iommu = VirtIOIommu::<FakeHal, FakeTransport<IommuConfig>>::new(transport).unwrap();

        assert_eq!(iommu.page_size_mask().unwrap(), 0x1000);
        assert_eq!(iommu.input_range().unwrap(), (0, 0xFFFF_FFFF));
        assert_eq!(iommu.domain_range().unwrap(), (0, 65535));
        assert_eq!(iommu.probe_size().unwrap(), 512);
    }

    #[test]
    fn attach() {
        let config_space = IommuConfig {
            page_size_mask_low: ReadOnly::new(0x1000 as u32),
            page_size_mask_high: ReadOnly::new(0),
            input_range_start_low: ReadOnly::new(0 as u32),
            input_range_start_high: ReadOnly::new(0),
            input_range_end_low: ReadOnly::new(0xFFFF_FFFF as u32),
            input_range_end_high: ReadOnly::new(0),
            domain_range_start: ReadOnly::new(0),
            domain_range_end: ReadOnly::new(0),
            probe_size: ReadOnly::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::IOMMU,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: 0,
            state: state.clone(),
        };
        let mut iommu = VirtIOIommu::<FakeHal, FakeTransport<IommuConfig>>::new(transport).unwrap();

        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state, QUEUE_REQUEST);
            assert!(
                state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(QUEUE_REQUEST, |request| {
                        let req: &VirtioIommuReqAttach =
                            VirtioIommuReqAttach::ref_from_bytes(&request).unwrap();
                        assert_eq!(req.head.type_, VIRTIO_IOMMU_T_ATTACH);
                        assert_eq!(req.domain, 1);
                        assert_eq!(req.endpoint, 42);

                        let mut resp = VirtioIommuReqAttach::new_zeroed();
                        resp.tail.status = VIRTIO_IOMMU_S_OK;
                        resp.as_bytes().to_vec()
                    })
            );
        });

        iommu.attach(1, 42, false).unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn map() {
        let config_space = IommuConfig {
            page_size_mask_low: ReadOnly::new(0x1000 as u32),
            page_size_mask_high: ReadOnly::new(0),
            input_range_start_low: ReadOnly::new(0 as u32),
            input_range_start_high: ReadOnly::new(0),
            input_range_end_low: ReadOnly::new(0xFFFF_FFFF as u32),
            input_range_end_high: ReadOnly::new(0),
            domain_range_start: ReadOnly::new(0),
            domain_range_end: ReadOnly::new(0),
            probe_size: ReadOnly::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::IOMMU,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: Feature::MAP_UNMAP.bits(),
            state: state.clone(),
        };
        let mut iommu = VirtIOIommu::<FakeHal, FakeTransport<IommuConfig>>::new(transport).unwrap();

        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state, QUEUE_REQUEST);
            assert!(
                state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(QUEUE_REQUEST, |request| {
                        let req: &VirtioIommuReqMap =
                            VirtioIommuReqMap::ref_from_bytes(&request).unwrap();
                        assert_eq!(req.head.type_, VIRTIO_IOMMU_T_MAP);
                        assert_eq!(req.domain, 1);
                        assert_eq!(req.virt_start, 0x1000);
                        assert_eq!(req.virt_end, 0x1FFF);
                        assert_eq!(req.phys_start, 0xA000);
                        assert_eq!(
                            req.flags,
                            VIRTIO_IOMMU_MAP_F_READ | VIRTIO_IOMMU_MAP_F_WRITE
                        );

                        let mut resp = VirtioIommuReqMap::new_zeroed();
                        resp.tail.status = VIRTIO_IOMMU_S_OK;
                        resp.as_bytes().to_vec()
                    })
            );
        });

        iommu
            .map(
                1,
                0x1000,
                0x1FFF,
                0xA000,
                VIRTIO_IOMMU_MAP_F_READ | VIRTIO_IOMMU_MAP_F_WRITE,
            )
            .unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn unmap() {
        let config_space = IommuConfig {
            page_size_mask_low: ReadOnly::new(0x1000 as u32),
            page_size_mask_high: ReadOnly::new(0),
            input_range_start_low: ReadOnly::new(0 as u32),
            input_range_start_high: ReadOnly::new(0),
            input_range_end_low: ReadOnly::new(0xFFFF_FFFF as u32),
            input_range_end_high: ReadOnly::new(0),
            domain_range_start: ReadOnly::new(0),
            domain_range_end: ReadOnly::new(0),
            probe_size: ReadOnly::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::IOMMU,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: Feature::MAP_UNMAP.bits(),
            state: state.clone(),
        };
        let mut iommu = VirtIOIommu::<FakeHal, FakeTransport<IommuConfig>>::new(transport).unwrap();

        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state, QUEUE_REQUEST);
            assert!(
                state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(QUEUE_REQUEST, |request| {
                        let req: &VirtioIommuReqUnmap =
                            VirtioIommuReqUnmap::ref_from_bytes(&request).unwrap();
                        assert_eq!(req.head.type_, VIRTIO_IOMMU_T_UNMAP);
                        assert_eq!(req.domain, 1);
                        assert_eq!(req.virt_start, 0x1000);
                        assert_eq!(req.virt_end, 0x1FFF);

                        let mut resp = VirtioIommuReqUnmap::new_zeroed();
                        resp.tail.status = VIRTIO_IOMMU_S_OK;
                        resp.as_bytes().to_vec()
                    })
            );
        });

        iommu.unmap(1, 0x1000, 0x1FFF).unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn detach() {
        let config_space = IommuConfig {
            page_size_mask_low: ReadOnly::new(0x1000 as u32),
            page_size_mask_high: ReadOnly::new(0),
            input_range_start_low: ReadOnly::new(0 as u32),
            input_range_start_high: ReadOnly::new(0),
            input_range_end_low: ReadOnly::new(0xFFFF_FFFF as u32),
            input_range_end_high: ReadOnly::new(0),
            domain_range_start: ReadOnly::new(0),
            domain_range_end: ReadOnly::new(0),
            probe_size: ReadOnly::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::IOMMU,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: 0,
            state: state.clone(),
        };
        let mut iommu = VirtIOIommu::<FakeHal, FakeTransport<IommuConfig>>::new(transport).unwrap();

        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state, QUEUE_REQUEST);
            assert!(
                state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(QUEUE_REQUEST, |request| {
                        let req: &VirtioIommuReqDetach =
                            VirtioIommuReqDetach::ref_from_bytes(&request).unwrap();
                        assert_eq!(req.head.type_, VIRTIO_IOMMU_T_DETACH);
                        assert_eq!(req.domain, 1);
                        assert_eq!(req.endpoint, 42);

                        let mut resp = VirtioIommuReqDetach::new_zeroed();
                        resp.tail.status = VIRTIO_IOMMU_S_OK;
                        resp.as_bytes().to_vec()
                    })
            );
        });

        iommu.detach(1, 42).unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn probe_resv_mem() {
        let config_space = IommuConfig {
            page_size_mask_low: ReadOnly::new(0x1000 as u32),
            page_size_mask_high: ReadOnly::new(0),
            input_range_start_low: ReadOnly::new(0 as u32),
            input_range_start_high: ReadOnly::new(0),
            input_range_end_low: ReadOnly::new(0xFFFF_FFFF as u32),
            input_range_end_high: ReadOnly::new(0),
            domain_range_start: ReadOnly::new(0),
            domain_range_end: ReadOnly::new(0),
            probe_size: ReadOnly::new(128),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::IOMMU,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: Feature::PROBE.bits(),
            state: state.clone(),
        };
        let mut iommu = VirtIOIommu::<FakeHal, FakeTransport<IommuConfig>>::new(transport).unwrap();

        assert_eq!(iommu.probe_size().unwrap(), 128);

        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state, QUEUE_REQUEST);
            assert!(
                state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(QUEUE_REQUEST, |request| {
                        assert_eq!(request.len(), 8);
                        assert_eq!(request[0], VIRTIO_IOMMU_T_PROBE);
                        let endpoint = u32::from_le_bytes(request[4..8].try_into().unwrap());
                        assert_eq!(endpoint, 42);

                        let prop = VirtioIommuProbeResvMem {
                            head: VirtioIommuProbeProperty {
                                type_: VIRTIO_IOMMU_PROBE_T_RESV_MEM,
                                length: core::mem::size_of::<VirtioIommuProbeResvMem>() as u16,
                            },
                            subtype: VIRTIO_IOMMU_RESV_MEM_T_MSI,
                            reserved: [0; 3],
                            start: 0xFE00_0000,
                            end: 0xFE00_0FFF,
                        };
                        let mut resp = vec![0u8; 120];
                        resp[..prop.head.length as usize].copy_from_slice(prop.as_bytes());
                        resp[116] = VIRTIO_IOMMU_S_OK;
                        resp
                    })
            );
        });

        let mut buf = vec![0u8; 128];
        iommu.probe(42, &mut buf).unwrap();
        handle.join().unwrap();
    }
}
