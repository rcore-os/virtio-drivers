//! Driver for VirtIO memory balloon devices.
//!
//! The balloon device allows a guest to give memory back to the host (inflate)
//! and reclaim it later (deflate). It also supports reporting memory statistics,
//! free page hinting for live migration, and unused page reporting.

use crate::Result;
use crate::config::{ReadOnly, ReadWrite, read_config, write_config};
use crate::hal::Hal;
use crate::queue::VirtQueue;
use crate::transport::{InterruptStatus, Transport};
use log::info;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

const INFLATEQ: u16 = 0;
const DEFLATEQ: u16 = 1;
const STATSQ: u16 = 2;
const FREE_PAGEQ: u16 = 3;
const REPORTINGQ: u16 = 4;
const QUEUE_SIZE: u16 = 64;

/// Command ID indicating the device wants the driver to stop hinting.
pub const CMD_ID_STOP: u32 = 0;
/// Command ID the driver writes when all free pages have been reported.
pub const CMD_ID_DONE: u32 = 1;

const SUPPORTED_FEATURES: Feature = Feature::MUST_TELL_HOST
    .union(Feature::STATS_VQ)
    .union(Feature::DEFLATE_ON_OOM)
    .union(Feature::FREE_PAGE_HINT)
    .union(Feature::PAGE_POISON)
    .union(Feature::REPORTING)
    .union(Feature::RING_INDIRECT_DESC)
    .union(Feature::RING_EVENT_IDX)
    .union(Feature::VERSION_1)
    .union(Feature::ACCESS_PLATFORM);

/// Driver for a VirtIO memory balloon device.
///
/// # Example
///
/// ```
/// # use virtio_drivers::{Error, Hal};
/// # use virtio_drivers::transport::Transport;
/// use virtio_drivers::device::balloon::VirtIOBalloon;
///
/// # fn example<HalImpl: Hal, T: Transport>(transport: T) -> Result<(), Error> {
/// let mut balloon = VirtIOBalloon::<HalImpl, _>::new(transport)?;
///
/// // Check how many pages the host wants.
/// let target = balloon.num_pages()?;
///
/// // Give 4 pages to the host (inflate).
/// let pfns = [0x10000_u32, 0x10001, 0x10002, 0x10003];
/// balloon.inflate(&pfns)?;
/// balloon.update_actual(4)?;
///
/// // Reclaim 2 pages from the host (deflate).
/// balloon.deflate(&pfns[0..2])?;
/// balloon.update_actual(2)?;
///
/// // Report memory statistics.
/// if balloon.has_stats() {
///     let stats = [
///         virtio_drivers::device::balloon::BalloonStat::new(4, 1024 * 1024),
///         virtio_drivers::device::balloon::BalloonStat::new(5, 256 * 1024 * 1024),
///     ];
///     balloon.report_stats(&stats)?;
/// }
/// # Ok(())
/// # }
/// ```
pub struct VirtIOBalloon<H: Hal, T: Transport> {
    transport: T,
    negotiated_features: Feature,
    inflate_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    deflate_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    stats_queue: Option<VirtQueue<H, { QUEUE_SIZE as usize }>>,
    free_page_queue: Option<VirtQueue<H, { QUEUE_SIZE as usize }>>,
    reporting_queue: Option<VirtQueue<H, { QUEUE_SIZE as usize }>>,
}

impl<H: Hal, T: Transport> VirtIOBalloon<H, T> {
    /// Create a new VirtIO balloon driver.
    pub fn new(mut transport: T) -> Result<Self> {
        let negotiated_features = transport.begin_init(SUPPORTED_FEATURES);

        let actual = read_config!(transport, BalloonConfig, actual)?;
        let num_pages = read_config!(transport, BalloonConfig, num_pages)?;
        info!(
            "balloon device: actual pages = {}, target pages = {}",
            actual, num_pages
        );

        if negotiated_features.contains(Feature::PAGE_POISON) {
            let poison = read_config!(transport, BalloonConfig, poison_val)?;
            info!("balloon device: page poison = 0x{:x}", poison);
        }

        let indirect = negotiated_features.contains(Feature::RING_INDIRECT_DESC);
        let event_idx = negotiated_features.contains(Feature::RING_EVENT_IDX);
        let access_platform = negotiated_features.contains(Feature::ACCESS_PLATFORM);

        let inflate_queue = VirtQueue::new(
            &mut transport,
            INFLATEQ,
            indirect,
            event_idx,
            access_platform,
        )?;
        let deflate_queue = VirtQueue::new(
            &mut transport,
            DEFLATEQ,
            indirect,
            event_idx,
            access_platform,
        )?;

        let stats_queue = if negotiated_features.contains(Feature::STATS_VQ) {
            Some(VirtQueue::new(
                &mut transport,
                STATSQ,
                indirect,
                event_idx,
                access_platform,
            )?)
        } else {
            None
        };

        let free_page_queue = if negotiated_features.contains(Feature::FREE_PAGE_HINT) {
            Some(VirtQueue::new(
                &mut transport,
                FREE_PAGEQ,
                indirect,
                event_idx,
                access_platform,
            )?)
        } else {
            None
        };

        let reporting_queue = if negotiated_features.contains(Feature::REPORTING) {
            Some(VirtQueue::new(
                &mut transport,
                REPORTINGQ,
                indirect,
                event_idx,
                access_platform,
            )?)
        } else {
            None
        };

        transport.finish_init();

        Ok(Self {
            transport,
            inflate_queue,
            deflate_queue,
            stats_queue,
            free_page_queue,
            reporting_queue,
            negotiated_features,
        })
    }

    /// Returns the number of pages the host wants in the balloon.
    ///
    /// If this is greater than the current actual number of pages, the driver
    /// should inflate the balloon. If less, it should deflate.
    pub fn num_pages(&mut self) -> Result<u32> {
        read_config!(self.transport, BalloonConfig, num_pages)
    }

    /// Gives pages to the host (inflates the balloon).
    ///
    /// `pfns` is a slice of page frame numbers (`physical_address >> 12`).
    /// These pages must not be accessed by the guest until the host returns
    /// them via deflation.
    ///
    /// Blocks until the device acknowledges the pages.
    pub fn inflate(&mut self, pfns: &[u32]) -> Result {
        assert!(!pfns.is_empty(), "Must provide at least one PFN to inflate");
        assert!(
            core::mem::size_of_val(pfns) <= QUEUE_SIZE as usize * crate::PAGE_SIZE,
            "Too many PFNs for the virtqueue"
        );

        self.inflate_queue
            .add_notify_wait_pop(&[pfns.as_bytes()], &mut [], &mut self.transport)?;

        Ok(())
    }

    /// Reclaims pages from the host (deflates the balloon).
    ///
    /// `pfns` is a slice of page frame numbers (`physical_address >> 12`)
    /// for pages previously given to the host via `inflate`.
    ///
    /// Blocks until the device acknowledges. If `VIRTIO_BALLOON_F_MUST_TELL_HOST`
    /// was negotiated, the driver must wait for this acknowledgment before
    /// reusing the pages.
    pub fn deflate(&mut self, pfns: &[u32]) -> Result {
        assert!(!pfns.is_empty(), "Must provide at least one PFN to deflate");

        self.deflate_queue
            .add_notify_wait_pop(&[pfns.as_bytes()], &mut [], &mut self.transport)?;

        Ok(())
    }

    /// Returns the current actual number of pages in the balloon from the config
    /// space.
    pub fn actual(&mut self) -> Result<u32> {
        read_config!(self.transport, BalloonConfig, actual)
    }

    /// Updates the `actual` field in the device config space.
    ///
    /// The driver must call this after inflating or deflating to tell the device
    /// the new balloon size.
    pub fn update_actual(&mut self, actual: u32) -> Result {
        write_config!(self.transport, BalloonConfig, actual, actual)?;
        Ok(())
    }

    /// Returns the page poison value, if `VIRTIO_BALLOON_F_PAGE_POISON` was negotiated.
    pub fn poison_val(&mut self) -> Result<u32> {
        read_config!(self.transport, BalloonConfig, poison_val)
    }

    /// Writes the page poison value to config space.
    pub fn set_poison_val(&mut self, poison: u32) -> Result {
        write_config!(self.transport, BalloonConfig, poison_val, poison)?;
        Ok(())
    }

    /// Returns the free page hint command ID from the device config space.
    ///
    /// The device writes this field to signal start/stop of free page hinting.
    /// A non-zero, non-STOP value means the driver should begin reporting.
    /// [`CMD_ID_STOP`] (0) means stop. When the driver finishes reporting, it
    /// writes [`CMD_ID_DONE`] (1) back.
    pub fn free_page_cmd_id(&mut self) -> Result<u32> {
        read_config!(self.transport, BalloonConfig, free_page_hint_cmd_id)
    }

    /// Signals completion of free page hinting to the device by writing
    /// [`CMD_ID_DONE`] to the config space.
    pub fn free_page_send_done(&mut self) -> Result {
        write_config!(
            self.transport,
            BalloonConfig,
            free_page_hint_cmd_id,
            CMD_ID_DONE
        )?;
        Ok(())
    }

    /// Sends a free page hint command ID on the free page hint virtqueue.
    ///
    /// Per the VirtIO spec, the driver echoes the received command ID at the
    /// start of a hinting session, and sends [`CMD_ID_STOP`] at the end.
    ///
    /// Blocks until the device acknowledges.
    pub fn free_page_send_cmd_id(&mut self, cmd_id: u32) -> Result {
        let queue = self
            .free_page_queue
            .as_mut()
            .ok_or(crate::Error::Unsupported)?;
        queue.add_notify_wait_pop(&[cmd_id.as_bytes()], &mut [], &mut self.transport)?;
        Ok(())
    }

    /// Sends free page data on the free page hint virtqueue.
    ///
    /// The `data` buffer should contain the memory contents of free pages.
    /// Blocks until the device acknowledges.
    pub fn free_page_send_pages(&mut self, data: &[u8]) -> Result {
        let queue = self
            .free_page_queue
            .as_mut()
            .ok_or(crate::Error::Unsupported)?;
        queue.add_notify_wait_pop(&[data], &mut [], &mut self.transport)?;
        Ok(())
    }

    /// Reports unused pages to the host for reclamation via the page reporting
    /// virtqueue.
    ///
    /// The `data` buffer should contain page data the host may reclaim.
    /// Blocks until the device acknowledges.
    pub fn report_unused_pages(&mut self, data: &[u8]) -> Result {
        let queue = self
            .reporting_queue
            .as_mut()
            .ok_or(crate::Error::Unsupported)?;
        queue.add_notify_wait_pop(&[data], &mut [], &mut self.transport)?;
        Ok(())
    }

    /// Reports memory statistics to the host via the stats virtqueue.
    ///
    /// `stats` is a slice of [`BalloonStat`] entries describing the guest's
    /// memory state (free memory, swap usage, page faults, etc.).
    ///
    /// Blocks until the device acknowledges receipt.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Unsupported`] if the stats queue was not negotiated.
    pub fn report_stats(&mut self, stats: &[BalloonStat]) -> Result {
        let queue = self.stats_queue.as_mut().ok_or(crate::Error::Unsupported)?;
        queue.add_notify_wait_pop(&[stats.as_bytes()], &mut [], &mut self.transport)?;
        Ok(())
    }

    /// Returns true if `VIRTIO_BALLOON_F_MUST_TELL_HOST` was negotiated.
    pub fn must_tell_host(&self) -> bool {
        self.negotiated_features.contains(Feature::MUST_TELL_HOST)
    }

    /// Returns true if `VIRTIO_BALLOON_F_STATS_VQ` was negotiated and the stats
    /// queue is available.
    pub fn has_stats(&self) -> bool {
        self.stats_queue.is_some()
    }

    /// Returns true if `VIRTIO_BALLOON_F_DEFLATE_ON_OOM` was negotiated.
    ///
    /// When this feature is active, the driver may deflate the balloon in
    /// response to out-of-memory conditions without waiting for the host to
    /// reduce `num_pages`.
    pub fn can_deflate_on_oom(&self) -> bool {
        self.negotiated_features.contains(Feature::DEFLATE_ON_OOM)
    }

    /// Returns true if `VIRTIO_BALLOON_F_FREE_PAGE_HINT` was negotiated.
    pub fn has_free_page_hint(&self) -> bool {
        self.free_page_queue.is_some()
    }

    /// Returns true if `VIRTIO_BALLOON_F_PAGE_POISON` was negotiated.
    pub fn has_page_poison(&self) -> bool {
        self.negotiated_features.contains(Feature::PAGE_POISON)
    }

    /// Returns true if `VIRTIO_BALLOON_F_REPORTING` was negotiated.
    pub fn has_reporting(&self) -> bool {
        self.reporting_queue.is_some()
    }

    /// Acknowledges a pending interrupt, if any.
    pub fn ack_interrupt(&mut self) -> InterruptStatus {
        self.transport.ack_interrupt()
    }

    /// Enables interrupts from the device.
    pub fn enable_interrupts(&mut self) {
        self.inflate_queue.set_dev_notify(true);
    }

    /// Disables interrupts from the device.
    pub fn disable_interrupts(&mut self) {
        self.inflate_queue.set_dev_notify(false);
    }
}

impl<H: Hal, T: Transport> Drop for VirtIOBalloon<H, T> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(INFLATEQ);
        self.transport.queue_unset(DEFLATEQ);
        if self.stats_queue.is_some() {
            self.transport.queue_unset(STATSQ);
        }
        if self.free_page_queue.is_some() {
            self.transport.queue_unset(FREE_PAGEQ);
        }
        if self.reporting_queue.is_some() {
            self.transport.queue_unset(REPORTINGQ);
        }
    }
}

/// A memory statistics entry reported to the host.
///
/// See the VirtIO spec §5.5.6.3 for the meaning of each tag.
///
/// Construct with [`BalloonStat::new`] rather than struct literal syntax.
#[derive(Clone, Debug, Default, FromBytes, Immutable, IntoBytes, KnownLayout)]
#[repr(C)]
pub struct BalloonStat {
    /// The type of statistic.
    pub tag: u16,
    /// Explicit padding to correctly align `val` to 8 bytes.
    _pad: [u8; 6],
    /// The value of the statistic.
    pub val: u64,
}

impl BalloonStat {
    /// Creates a new memory statistic entry.
    pub const fn new(tag: u16, val: u64) -> Self {
        Self {
            tag,
            _pad: [0; 6],
            val,
        }
    }
}

/// Statistic tag: the amount of memory swapped in from disk (bytes).
pub const BALLOON_STAT_SWAP_IN: u16 = 0;
/// Statistic tag: the amount of memory swapped out to disk (bytes).
pub const BALLOON_STAT_SWAP_OUT: u16 = 1;
/// Statistic tag: the number of major page faults.
pub const BALLOON_STAT_MAJFLT: u16 = 2;
/// Statistic tag: the number of minor page faults.
pub const BALLOON_STAT_MINFLT: u16 = 3;
/// Statistic tag: the amount of free memory (bytes).
pub const BALLOON_STAT_MEMFREE: u16 = 4;
/// Statistic tag: the total amount of memory (bytes).
pub const BALLOON_STAT_MEMTOT: u16 = 5;
/// Statistic tag: the available memory estimate (bytes).
pub const BALLOON_STAT_AVAIL: u16 = 6;
/// Statistic tag: the amount of memory used for disk caches (bytes).
pub const BALLOON_STAT_CACHES: u16 = 7;
/// Statistic tag: the number of successful hugetlb page allocations.
pub const BALLOON_STAT_HTLB_PGALLOC: u16 = 8;
/// Statistic tag: the number of failed hugetlb page allocations.
pub const BALLOON_STAT_HTLB_PGFAIL: u16 = 9;
/// Statistic tag: the number of OOM killer invocations.
pub const BALLOON_STAT_OOM_KILL: u16 = 10;
/// Statistic tag: the number of memory allocation stalls.
pub const BALLOON_STAT_ALLOC_STALL: u16 = 11;
/// Statistic tag: the amount of memory scanned asynchronously.
pub const BALLOON_STAT_ASYNC_SCAN: u16 = 12;
/// Statistic tag: the amount of memory scanned directly.
pub const BALLOON_STAT_DIRECT_SCAN: u16 = 13;
/// Statistic tag: the amount of memory reclaimed asynchronously.
pub const BALLOON_STAT_ASYNC_RECLAIM: u16 = 14;
/// Statistic tag: the amount of memory reclaimed directly.
pub const BALLOON_STAT_DIRECT_RECLAIM: u16 = 15;

/// VirtIO balloon config space.
#[derive(FromBytes, Immutable, IntoBytes)]
#[repr(C)]
struct BalloonConfig {
    /// Target number of pages the host wants in the balloon.
    num_pages: ReadOnly<u32>,
    /// Actual number of pages in the balloon (written by driver).
    actual: ReadWrite<u32>,
    /// Command ID for free page hinting / page reporting.
    ///
    /// Read-written by both driver and device: the device writes START/STOP
    /// commands, the driver writes DONE when finished.
    free_page_hint_cmd_id: ReadWrite<u32>,
    /// Page poison value written to deflated pages (VIRTIO_BALLOON_F_PAGE_POISON).
    poison_val: ReadWrite<u32>,
}

bitflags::bitflags! {
    /// virtio-balloon specific features
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct Feature: u64 {
        /// Host must be told before guest reuses a deflated page.
        const MUST_TELL_HOST  = 1 << 0;
        /// Memory statistics virtqueue is present.
        const STATS_VQ        = 1 << 1;
        /// Driver may deflate on OOM even if host doesn't ask.
        const DEFLATE_ON_OOM  = 1 << 2;
        /// VQ to report free pages for live migration.
        const FREE_PAGE_HINT  = 1 << 3;
        /// Guest is using page poisoning.
        const PAGE_POISON     = 1 << 4;
        /// Page reporting virtqueue.
        const REPORTING       = 1 << 5;

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
    use core::mem::size_of;
    use std::{sync::Mutex, thread};

    fn make_queue_status(count: usize) -> Vec<QueueStatus> {
        (0..count).map(|_| QueueStatus::default()).collect()
    }

    #[test]
    fn config() {
        let config_space = BalloonConfig {
            num_pages: ReadOnly::new(0),
            actual: ReadWrite::new(42),
            free_page_hint_cmd_id: ReadWrite::new(0),
            poison_val: ReadWrite::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::MemoryBalloon,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: 0,
            state: state.clone(),
        };
        let mut balloon =
            VirtIOBalloon::<FakeHal, FakeTransport<BalloonConfig>>::new(transport).unwrap();

        assert_eq!(balloon.actual().unwrap(), 42);
        balloon.update_actual(100).unwrap();
        assert_eq!(balloon.actual().unwrap(), 100);
        assert!(!balloon.has_stats());
        assert!(!balloon.can_deflate_on_oom());
        assert!(!balloon.has_free_page_hint());
        assert!(!balloon.has_reporting());
    }

    #[test]
    fn config_with_features() {
        let config_space = BalloonConfig {
            num_pages: ReadOnly::new(0),
            actual: ReadWrite::new(0),
            free_page_hint_cmd_id: ReadWrite::new(0),
            poison_val: ReadWrite::new(0xDEAD),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(5), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::MemoryBalloon,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: (Feature::MUST_TELL_HOST
                | Feature::STATS_VQ
                | Feature::DEFLATE_ON_OOM
                | Feature::FREE_PAGE_HINT
                | Feature::PAGE_POISON
                | Feature::REPORTING)
                .bits(),
            state: state.clone(),
        };
        let mut balloon =
            VirtIOBalloon::<FakeHal, FakeTransport<BalloonConfig>>::new(transport).unwrap();

        assert!(balloon.must_tell_host());
        assert!(balloon.has_stats());
        assert!(balloon.can_deflate_on_oom());
        assert!(balloon.has_free_page_hint());
        assert!(balloon.has_page_poison());
        assert!(balloon.has_reporting());
        assert_eq!(balloon.poison_val().unwrap(), 0xDEAD);
        balloon.set_poison_val(0xBEEF).unwrap();
        assert_eq!(balloon.poison_val().unwrap(), 0xBEEF);
    }

    #[test]
    fn inflate() {
        let config_space = BalloonConfig {
            num_pages: ReadOnly::new(10),
            actual: ReadWrite::new(0),
            free_page_hint_cmd_id: ReadWrite::new(0),
            poison_val: ReadWrite::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::MemoryBalloon,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: Feature::MUST_TELL_HOST.bits(),
            state: state.clone(),
        };
        let mut balloon =
            VirtIOBalloon::<FakeHal, FakeTransport<BalloonConfig>>::new(transport).unwrap();

        assert!(balloon.must_tell_host());
        assert_eq!(balloon.num_pages().unwrap(), 10);

        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state, INFLATEQ);
            assert!(
                state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(INFLATEQ, |request| {
                        assert_eq!(request.len(), 3 * size_of::<u32>());
                        let pfns: &[u32] = <[u32]>::ref_from_bytes(&request).unwrap();
                        assert_eq!(pfns, &[0x1000, 0x2000, 0x3000]);
                        vec![]
                    })
            );
        });

        let pfns = [0x1000_u32, 0x2000, 0x3000];
        balloon.inflate(&pfns).unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn deflate() {
        let config_space = BalloonConfig {
            num_pages: ReadOnly::new(0),
            actual: ReadWrite::new(5),
            free_page_hint_cmd_id: ReadWrite::new(0),
            poison_val: ReadWrite::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::MemoryBalloon,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: Feature::MUST_TELL_HOST.bits(),
            state: state.clone(),
        };
        let mut balloon =
            VirtIOBalloon::<FakeHal, FakeTransport<BalloonConfig>>::new(transport).unwrap();

        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state, DEFLATEQ);
            assert!(
                state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(DEFLATEQ, |request| {
                        let pfns: &[u32] = <[u32]>::ref_from_bytes(&request).unwrap();
                        assert_eq!(pfns, &[0x4000, 0x5000]);
                        vec![]
                    })
            );
        });

        let pfns = [0x4000_u32, 0x5000];
        balloon.deflate(&pfns).unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn report_stats() {
        let config_space = BalloonConfig {
            num_pages: ReadOnly::new(0),
            actual: ReadWrite::new(0),
            free_page_hint_cmd_id: ReadWrite::new(0),
            poison_val: ReadWrite::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(3), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::MemoryBalloon,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: (Feature::STATS_VQ | Feature::MUST_TELL_HOST).bits(),
            state: state.clone(),
        };
        let mut balloon =
            VirtIOBalloon::<FakeHal, FakeTransport<BalloonConfig>>::new(transport).unwrap();

        assert!(balloon.has_stats());
        let stats = [
            BalloonStat::new(BALLOON_STAT_MEMFREE, 64 * 1024 * 1024),
            BalloonStat::new(BALLOON_STAT_MEMTOT, 256 * 1024 * 1024),
        ];

        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state, STATSQ);
            assert!(
                state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(STATSQ, |request| {
                        let received: &[BalloonStat] =
                            <[BalloonStat]>::ref_from_bytes(&request).unwrap();
                        assert_eq!(received.len(), 2);
                        assert_eq!(received[0].tag, BALLOON_STAT_MEMFREE);
                        assert_eq!(received[0].val, 64 * 1024 * 1024);
                        assert_eq!(received[1].tag, BALLOON_STAT_MEMTOT);
                        assert_eq!(received[1].val, 256 * 1024 * 1024);
                        vec![]
                    })
            );
        });

        balloon.report_stats(&stats).unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn stats_not_supported() {
        let config_space = BalloonConfig {
            num_pages: ReadOnly::new(0),
            actual: ReadWrite::new(0),
            free_page_hint_cmd_id: ReadWrite::new(0),
            poison_val: ReadWrite::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::MemoryBalloon,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: 0,
            state: state.clone(),
        };
        let mut balloon =
            VirtIOBalloon::<FakeHal, FakeTransport<BalloonConfig>>::new(transport).unwrap();

        assert!(!balloon.has_stats());
        let stats = [BalloonStat::new(BALLOON_STAT_MEMFREE, 0)];
        assert_eq!(
            balloon.report_stats(&stats).unwrap_err(),
            crate::Error::Unsupported
        );
    }

    #[test]
    fn free_page_hint() {
        let config_space = BalloonConfig {
            num_pages: ReadOnly::new(0),
            actual: ReadWrite::new(0),
            free_page_hint_cmd_id: ReadWrite::new(0xABCD),
            poison_val: ReadWrite::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(4), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::MemoryBalloon,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: Feature::FREE_PAGE_HINT.bits(),
            state: state.clone(),
        };
        let mut balloon =
            VirtIOBalloon::<FakeHal, FakeTransport<BalloonConfig>>::new(transport).unwrap();

        assert!(balloon.has_free_page_hint());
        assert_eq!(balloon.free_page_cmd_id().unwrap(), 0xABCD);

        // Send cmd_id start.
        let state2 = state.clone();
        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state2, FREE_PAGEQ);
            assert!(
                state2
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(FREE_PAGEQ, |request| {
                        let cmd: &[u8; 4] = request[..4].try_into().unwrap();
                        assert_eq!(u32::from_le_bytes(*cmd), 0xABCD);
                        vec![]
                    })
            );
        });

        balloon.free_page_send_cmd_id(0xABCD).unwrap();
        handle.join().unwrap();

        // Send free pages.
        let state2 = state.clone();
        let data = [0x41u8; 4096];
        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state2, FREE_PAGEQ);
            assert!(
                state2
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(FREE_PAGEQ, |request| {
                        assert_eq!(request, vec![0x41u8; 4096]);
                        vec![]
                    })
            );
        });

        balloon.free_page_send_pages(&data).unwrap();
        handle.join().unwrap();

        // Signal done.
        balloon.free_page_send_done().unwrap();
        assert_eq!(balloon.free_page_cmd_id().unwrap(), CMD_ID_DONE);
    }

    #[test]
    fn free_page_not_supported() {
        let config_space = BalloonConfig {
            num_pages: ReadOnly::new(0),
            actual: ReadWrite::new(0),
            free_page_hint_cmd_id: ReadWrite::new(0),
            poison_val: ReadWrite::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::MemoryBalloon,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: 0,
            state: state.clone(),
        };
        let mut balloon =
            VirtIOBalloon::<FakeHal, FakeTransport<BalloonConfig>>::new(transport).unwrap();

        assert!(!balloon.has_free_page_hint());
        assert_eq!(
            balloon.free_page_send_cmd_id(0).unwrap_err(),
            crate::Error::Unsupported
        );
        assert_eq!(
            balloon.free_page_send_pages(&[]).unwrap_err(),
            crate::Error::Unsupported
        );
    }

    #[test]
    fn report_unused_pages() {
        let config_space = BalloonConfig {
            num_pages: ReadOnly::new(0),
            actual: ReadWrite::new(0),
            free_page_hint_cmd_id: ReadWrite::new(0),
            poison_val: ReadWrite::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(5), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::MemoryBalloon,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: Feature::REPORTING.bits(),
            state: state.clone(),
        };
        let mut balloon =
            VirtIOBalloon::<FakeHal, FakeTransport<BalloonConfig>>::new(transport).unwrap();

        assert!(balloon.has_reporting());

        let data = [0xBBu8; 8192];
        let handle = thread::spawn(move || {
            State::wait_until_queue_notified(&state, REPORTINGQ);
            assert!(
                state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(REPORTINGQ, |request| {
                        assert_eq!(request, vec![0xBBu8; 8192]);
                        vec![]
                    })
            );
        });

        balloon.report_unused_pages(&data).unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn reporting_not_supported() {
        let config_space = BalloonConfig {
            num_pages: ReadOnly::new(0),
            actual: ReadWrite::new(0),
            free_page_hint_cmd_id: ReadWrite::new(0),
            poison_val: ReadWrite::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(make_queue_status(2), config_space)));
        let transport = FakeTransport {
            device_type: DeviceType::MemoryBalloon,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: 0,
            state: state.clone(),
        };
        let mut balloon =
            VirtIOBalloon::<FakeHal, FakeTransport<BalloonConfig>>::new(transport).unwrap();

        assert!(!balloon.has_reporting());
        assert_eq!(
            balloon.report_unused_pages(&[]).unwrap_err(),
            crate::Error::Unsupported
        );
    }
}
