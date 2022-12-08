use super::*;
use crate::queue::VirtQueue;
use crate::transport::Transport;
use crate::volatile::{volread, Volatile};
use bitflags::*;
use core::hint::spin_loop;
use log::*;

/// The virtio block device is a simple virtual block device (ie. disk).
///
/// Read and write requests (and other exotic requests) are placed in the queue,
/// and serviced (probably out of order) by the device except where noted.
pub struct VirtIOBlk<H: Hal, T: Transport> {
    transport: T,
    queue: VirtQueue<H>,
    capacity: u64,
    readonly: bool,
}

impl<H: Hal, T: Transport> VirtIOBlk<H, T> {
    /// Create a new VirtIO-Blk driver.
    pub fn new(mut transport: T) -> Result<Self> {
        let mut readonly = false;

        transport.begin_init(|features| {
            let features = BlkFeature::from_bits_truncate(features);
            info!("device features: {:?}", features);
            readonly = features.contains(BlkFeature::RO);
            // negotiate these flags only
            let supported_features = BlkFeature::empty();
            (features & supported_features).bits()
        });

        // read configuration space
        let config = transport.config_space::<BlkConfig>()?;
        info!("config: {:?}", config);
        // Safe because config is a valid pointer to the device configuration space.
        let capacity = unsafe {
            volread!(config, capacity_low) as u64 | (volread!(config, capacity_high) as u64) << 32
        };
        info!("found a block device of size {}KB", capacity / 2);

        let queue = VirtQueue::new(&mut transport, 0, 16)?;
        transport.finish_init();

        Ok(VirtIOBlk {
            transport,
            queue,
            capacity,
            readonly,
        })
    }

    /// Gets the capacity of the block device, in 512 byte sectors.
    pub fn capacity(&self) -> u64 {
        self.capacity
    }

    /// Returns true if the block device is read-only, or false if it allows writes.
    pub fn readonly(&self) -> bool {
        self.readonly
    }

    /// Acknowledge interrupt.
    pub fn ack_interrupt(&mut self) -> bool {
        self.transport.ack_interrupt()
    }

    /// Read a block.
    pub fn read_block(&mut self, block_id: usize, buf: &mut [u8]) -> Result {
        assert_eq!(buf.len(), SECTOR_SIZE);
        let req = BlkReq {
            type_: ReqType::In,
            reserved: 0,
            sector: block_id as u64,
        };
        let mut resp = BlkResp::default();
        self.queue.add(&[req.as_buf()], &[buf, resp.as_buf_mut()])?;
        self.transport.notify(0);
        while !self.queue.can_pop() {
            spin_loop();
        }
        self.queue.pop_used()?;
        match resp.status {
            RespStatus::Ok => Ok(()),
            _ => Err(Error::IoError),
        }
    }

    /// Read a block in a non-blocking way which means that it returns immediately.
    ///
    /// # Arguments
    ///
    /// * `block_id` - The identifier of the block to read.
    /// * `buf` - The buffer in the memory which the block is read into.
    /// * `resp` - A mutable reference to a variable provided by the caller
    ///   which contains the status of the requests. The caller can safely
    ///   read the variable only after the request is ready.
    ///
    /// # Usage
    ///
    /// It will submit request to the virtio block device and return a token identifying
    /// the position of the first Descriptor in the chain. If there are not enough
    /// Descriptors to allocate, then it returns [Error::BufferTooSmall].
    ///
    /// After the request is ready, `resp` will be updated and the caller can get the
    /// status of the request(e.g. succeed or failed) through it. However, the caller
    /// **must not** spin on `resp` to wait for it to change. A safe way is to read it
    /// after the same token as this method returns is fetched through [VirtIOBlk::pop_used()],
    /// which means that the request has been ready.
    ///
    /// # Safety
    ///
    /// `buf` is still borrowed by the underlying virtio block device even if this
    /// method returns. Thus, it is the caller's responsibility to guarantee that
    /// `buf` is not accessed before the request is completed in order to avoid
    /// data races.
    pub unsafe fn read_block_nb(
        &mut self,
        block_id: usize,
        buf: &mut [u8],
        resp: &mut BlkResp,
    ) -> Result<u16> {
        assert_eq!(buf.len(), SECTOR_SIZE);
        let req = BlkReq {
            type_: ReqType::In,
            reserved: 0,
            sector: block_id as u64,
        };
        let token = self.queue.add(&[req.as_buf()], &[buf, resp.as_buf_mut()])?;
        self.transport.notify(0);
        Ok(token)
    }

    /// Write a block.
    pub fn write_block(&mut self, block_id: usize, buf: &[u8]) -> Result {
        assert_eq!(buf.len(), SECTOR_SIZE);
        let req = BlkReq {
            type_: ReqType::Out,
            reserved: 0,
            sector: block_id as u64,
        };
        let mut resp = BlkResp::default();
        self.queue.add(&[req.as_buf(), buf], &[resp.as_buf_mut()])?;
        self.transport.notify(0);
        while !self.queue.can_pop() {
            spin_loop();
        }
        self.queue.pop_used()?;
        match resp.status {
            RespStatus::Ok => Ok(()),
            _ => Err(Error::IoError),
        }
    }

    //// Write a block in a non-blocking way which means that it returns immediately.
    ///
    /// # Arguments
    ///
    /// * `block_id` - The identifier of the block to write.
    /// * `buf` - The buffer in the memory containing the data to write to the block.
    /// * `resp` - A mutable reference to a variable provided by the caller
    ///   which contains the status of the requests. The caller can safely
    ///   read the variable only after the request is ready.
    ///
    /// # Usage
    ///
    /// See also [VirtIOBlk::read_block_nb()].
    ///
    /// # Safety
    ///
    /// See also [VirtIOBlk::read_block_nb()].
    pub unsafe fn write_block_nb(
        &mut self,
        block_id: usize,
        buf: &[u8],
        resp: &mut BlkResp,
    ) -> Result<u16> {
        assert_eq!(buf.len(), SECTOR_SIZE);
        let req = BlkReq {
            type_: ReqType::Out,
            reserved: 0,
            sector: block_id as u64,
        };
        let token = self.queue.add(&[req.as_buf(), buf], &[resp.as_buf_mut()])?;
        self.transport.notify(0);
        Ok(token)
    }

    /// During an interrupt, it fetches a token of a completed request from the used
    /// ring and return it. If all completed requests have already been fetched, return
    /// Err(Error::NotReady).
    pub fn pop_used(&mut self) -> Result<u16> {
        self.queue.pop_used().map(|p| p.0)
    }

    /// Return size of its VirtQueue.
    /// It can be used to tell the caller how many channels he should monitor on.
    pub fn virt_queue_size(&self) -> u16 {
        self.queue.size()
    }
}

#[repr(C)]
struct BlkConfig {
    /// Number of 512 Bytes sectors
    capacity_low: Volatile<u32>,
    capacity_high: Volatile<u32>,
    size_max: Volatile<u32>,
    seg_max: Volatile<u32>,
    cylinders: Volatile<u16>,
    heads: Volatile<u8>,
    sectors: Volatile<u8>,
    blk_size: Volatile<u32>,
    physical_block_exp: Volatile<u8>,
    alignment_offset: Volatile<u8>,
    min_io_size: Volatile<u16>,
    opt_io_size: Volatile<u32>,
    // ... ignored
}

#[repr(C)]
#[derive(Debug)]
struct BlkReq {
    type_: ReqType,
    reserved: u32,
    sector: u64,
}

/// Response of a VirtIOBlk request.
#[repr(C)]
#[derive(Debug)]
pub struct BlkResp {
    status: RespStatus,
}

impl BlkResp {
    /// Return the status of a VirtIOBlk request.
    pub fn status(&self) -> RespStatus {
        self.status
    }
}

#[repr(u32)]
#[derive(Debug)]
enum ReqType {
    In = 0,
    Out = 1,
    Flush = 4,
    Discard = 11,
    WriteZeroes = 13,
}

/// Status of a VirtIOBlk request.
#[repr(u8)]
#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum RespStatus {
    /// Ok.
    Ok = 0,
    /// IoErr.
    IoErr = 1,
    /// Unsupported yet.
    Unsupported = 2,
    /// Not ready.
    _NotReady = 3,
}

impl Default for BlkResp {
    fn default() -> Self {
        BlkResp {
            status: RespStatus::_NotReady,
        }
    }
}

/// The standard sector size of a VirtIO block device. Data is read and written in multiples of this
/// size.
pub const SECTOR_SIZE: usize = 512;

bitflags! {
    struct BlkFeature: u64 {
        /// Device supports request barriers. (legacy)
        const BARRIER       = 1 << 0;
        /// Maximum size of any single segment is in `size_max`.
        const SIZE_MAX      = 1 << 1;
        /// Maximum number of segments in a request is in `seg_max`.
        const SEG_MAX       = 1 << 2;
        /// Disk-style geometry specified in geometry.
        const GEOMETRY      = 1 << 4;
        /// Device is read-only.
        const RO            = 1 << 5;
        /// Block size of disk is in `blk_size`.
        const BLK_SIZE      = 1 << 6;
        /// Device supports scsi packet commands. (legacy)
        const SCSI          = 1 << 7;
        /// Cache flush command support.
        const FLUSH         = 1 << 9;
        /// Device exports information on optimal I/O alignment.
        const TOPOLOGY      = 1 << 10;
        /// Device can toggle its cache between writeback and writethrough modes.
        const CONFIG_WCE    = 1 << 11;
        /// Device can support discard command, maximum discard sectors size in
        /// `max_discard_sectors` and maximum discard segment number in
        /// `max_discard_seg`.
        const DISCARD       = 1 << 13;
        /// Device can support write zeroes command, maximum write zeroes sectors
        /// size in `max_write_zeroes_sectors` and maximum write zeroes segment
        /// number in `max_write_zeroes_seg`.
        const WRITE_ZEROES  = 1 << 14;

        // device independent
        const NOTIFY_ON_EMPTY       = 1 << 24; // legacy
        const ANY_LAYOUT            = 1 << 27; // legacy
        const RING_INDIRECT_DESC    = 1 << 28;
        const RING_EVENT_IDX        = 1 << 29;
        const UNUSED                = 1 << 30; // legacy
        const VERSION_1             = 1 << 32; // detect legacy

        // the following since virtio v1.1
        const ACCESS_PLATFORM       = 1 << 33;
        const RING_PACKED           = 1 << 34;
        const IN_ORDER              = 1 << 35;
        const ORDER_PLATFORM        = 1 << 36;
        const SR_IOV                = 1 << 37;
        const NOTIFICATION_DATA     = 1 << 38;
    }
}

unsafe impl AsBuf for BlkReq {}
unsafe impl AsBuf for BlkResp {}
