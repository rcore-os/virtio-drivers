//! Driver for VirtIO block devices.
extern crate alloc;

use crate::hal::Hal;
use crate::virtio_queue::{packed_queue::PackedQueue, split_queue::SplitQueue, VirtQueue};
use crate::transport::Transport;
use crate::volatile::{volread, Volatile};
use crate::NonNull;
use crate::{Error, Result};
use bitflags::bitflags;
use zerocopy::{AsBytes, FromBytes};

use alloc::{boxed::Box, sync::Arc, vec, vec::Vec};

use core::{
    future::Future,
    pin::Pin,
    task::{Context, Poll, Waker},
};
use spin::Mutex;

use log::{debug};

const QUEUE: u16 = 0;
const QUEUE_SIZE: u16 = 64;

/// Driver for a VirtIO block device.
///
/// This is a simple virtual block device, e.g. disk.
///
/// Read and write requests (and other exotic requests) are placed in the queue and serviced
/// (probably out of order) by the device except where noted.
///
/// # Example
///
/// ```
/// # use virtio_drivers::{Error, Hal};
/// # use virtio_drivers::transport::Transport;
/// use virtio_drivers::device::blk::{VirtIOBlk, SECTOR_SIZE};
///
/// # fn example<HalImpl: Hal, T: Transport>(transport: T) -> Result<(), Error> {
/// let mut disk = VirtIOBlk::<HalImpl, _>::new(transport, true)?;
///
/// println!("VirtIO block device: {} kB", disk.capacity() * SECTOR_SIZE as u64 / 2);
///
/// // Read sector 0 and then copy it to sector 1.
/// let mut buf = [0; SECTOR_SIZE];
/// disk.read_blocks(0, &mut[&mut buf])?;
/// disk.write_blocks(1, &[&buf])?;
/// # Ok(())
/// # }
/// ```
///
///
///
struct VirtIoBlkInner<H: Hal> {
    queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    /// Asynchronous IO
    blkinfos: Box<[BlkInfo]>,
}
/// aaa
pub struct VirtIOBlk<H: Hal, T: Transport> {
    transport: T,
    config: Blkconfiglocal,
    features_neg: BlkFeature,
    inner: Arc<Mutex<VirtIoBlkInner<H>>>,
}

// TODO: The ability of Used Buffer Notification Suppression is not fully exploited (Ref: Section 2.7.7.1)
impl<'a, H: Hal, T: Transport> VirtIOBlk<H, T> {
    /// Create a new VirtIO-Blk driver.
    pub fn new(mut transport: T, notification_supress: bool) -> Result<Self> {
        let mut features_neg = BlkFeature::empty();

        transport.begin_init(|features| {
            // 剔除 device 不支持的feature

            features_neg = BlkFeature::from_bits_truncate(features);

            // negotiate these flags only
            if notification_supress {
                features_neg.remove(BlkFeature::VIRTIO_F_EVENT_IDX);
            }

            features_neg.bits()
        });

        // read configuration space
        let config = transport.config_space::<BlkConfig>()?;
        let config = Self::read_config(&config);
        debug!("found a block device of size {}KB", config.capacity / 2);

        let mut indirect_desc = false;
        if features_neg.contains(BlkFeature::VIRTIO_F_INDIRECT_DESC) {
            indirect_desc = true;
        }
        if features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX) {
            debug!("===__===");
        }

        // let queue = VirtQueue::new(&mut transport, QUEUE)?;
        let queue;
        if features_neg.contains(BlkFeature::VIRTIO_F_RING_PACKED) {
            queue = VirtQueue::Packedqueue(PackedQueue::<H, { QUEUE_SIZE as usize }>::new(
                &mut transport,
                QUEUE,
                indirect_desc,
            )?);
        } else {
            queue = VirtQueue::Splitqueue(SplitQueue::<H, { QUEUE_SIZE as usize }>::new(
                &mut transport,
                QUEUE,
                indirect_desc,
            )?);
        }

        let blkinfos = {
            let mut vec = Vec::<BlkInfo>::with_capacity(QUEUE_SIZE as usize);
            vec.resize_with(QUEUE_SIZE as usize, || NULLINFO);
            vec.into_boxed_slice()
        };

        transport.finish_init();

        Ok(VirtIOBlk {
            config,
            transport,
            features_neg,
            inner: Arc::new(Mutex::new(VirtIoBlkInner { queue, blkinfos })),
        })
    }

    fn read_config(config: &NonNull<BlkConfig>) -> Blkconfiglocal {
        Blkconfiglocal {
            /// The capacity (in 512-byte sectors).
            capacity: unsafe {
                volread!(config, capacity_low) as u64
                    | (volread!(config, capacity_high) as u64) << 32
            },

            /// The maximum segment size (if VIRTIO_BLK_F_SIZE_MAX)
            size_max: unsafe { volread!(config, size_max) },

            /// The maximum number of segments (if VIRTIO_BLK_F_SEG_MAX)
            seg_max: unsafe { volread!(config, seg_max) },

            /// geometry of the device (if VIRTIO_BLK_F_GEOMETRY)
            cylinders: unsafe { volread!(config, cylinders) },
            heads: unsafe { volread!(config, heads) },
            sectors: unsafe { volread!(config, sectors) },

            /// block size of device (if VIRTIO_BLK_F_BLK_SIZE)
            blk_size: unsafe { volread!(config, blk_size) },

            /// the next 4 entries are guarded by VIRTIO_BLK_F_TOPOLOGY
            /// exponent for physical block per logical block.
            physical_block_exp: unsafe { volread!(config, physical_block_exp) },

            /// alignment offset in logical blocks.
            alignment_offset: unsafe { volread!(config, alignment_offset) },

            /// minimum I/O size without performance penalty in logical blocks.
            min_io_size: unsafe { volread!(config, min_io_size) },

            /// optimal sustained I/O size in logical blocks.
            opt_io_size: unsafe { volread!(config, opt_io_size) },

            /// writeback mode (if VIRTIO_BLK_F_CONFIG_WCE)
            wce: unsafe { volread!(config, wce) },

            /// number of vqs, only available when VIRTIO_BLK_F_MQ is set
            num_queues: unsafe { volread!(config, num_queues) },

            /// the next 3 entries are guarded by VIRTIO_BLK_F_DISCARD
            ///
            /// The maximum discard sectors (in 512-byte sectors) for
            /// one segment.
            max_discard_sectors: unsafe { volread!(config, max_discard_sectors) },

            /// The maximum number of discard segments in a discard command.
            max_discard_seg: unsafe { volread!(config, max_discard_seg) },

            /// Discard commands must be aligned to this number of sectors.
            discard_sector_alignment: unsafe { volread!(config, discard_sector_alignment) },

            /// the next 3 entries are guarded by VIRTIO_BLK_F_WRITE_ZEROES.
            /// The maximum number of write zeroes sectors (in 512-byte sectors) in one segment.
            max_write_zeroes_sectors: unsafe { volread!(config, max_write_zeroes_sectors) },

            /// The maximum number of segments in a write zeroes command.
            max_write_zeroes_seg: unsafe { volread!(config, max_write_zeroes_seg) },

            /// Set if a VIRTIO_BLK_T_WRITE_ZEROES request may result in the deallocation of one or more of the sectors.
            write_zeroes_may_unmap: unsafe { volread!(config, write_zeroes_may_unmap) },
        }
    }

    /// Gets the capacity of the block device, in 512 byte ([`SECTOR_SIZE`]) sectors.
    pub fn capacity(&self) -> u64 {
        self.config.capacity
    }

    /// Returns true if the block device is read-only, or false if it allows writes.
    pub fn readonly(&self) -> bool {
        self.features_neg.contains(BlkFeature::VIRTIO_BLK_F_RO)
    }

    /// Return (max_discard_seg, max_discard_sectors)
    pub fn discard_parameters(&self) -> (u32, u32) {
        (self.config.max_discard_seg, self.config.max_discard_sectors)
    }

    /// Return (max_write_zeroes_seg, max_write_zeroes_sectors)
    pub fn writezeros_parameters(&self) -> (u32, u32) {
        (
            self.config.max_write_zeroes_seg,
            self.config.max_write_zeroes_sectors,
        )
    }

    /// Support discard single range?
    pub fn support_discard(&self) -> bool {
        self.features_neg.contains(BlkFeature::VIRTIO_BLK_F_DISCARD)
    }

    /// Support VIRTIO_BLK_F_WRITE_ZEROES ?
    pub fn support_writezeros(&self) -> bool {
        self.features_neg
            .contains(BlkFeature::VIRTIO_BLK_F_WRITE_ZEROES)
    }

    /// Support indirect dictionary
    pub fn support_indirect(&self) -> bool {
        self.features_neg
            .contains(BlkFeature::VIRTIO_F_INDIRECT_DESC)
    }

    /// Support event?
    fn support_event(&self) -> bool {
        self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX)
    }

    /// Acknowledges a pending interrupt, if any.
    ///
    /// Returns true if there was an interrupt to acknowledge.
    pub fn ack_interrupt(&mut self) -> bool {
        self.transport.ack_interrupt()
    }

    /// pop used  
    pub unsafe fn pop_used(
        &mut self,
        token: u16,
        inputs: &'a [&'a [u8]],
        outputs: &'a mut [&'a mut [u8]],
    ) -> Result<u32> {
        self.inner.lock().queue.pop_used(token, inputs, outputs)
    }

    /// pop used  
    // TODO: will be deleted in the further
    pub unsafe fn pop_used_async(&mut self, token: u16) -> Result<u32> {
        self.inner.lock().queue.pop_used_async(token)
    }

    /// Returns the size of the device's VirtQueue.
    ///
    /// This can be used to tell the caller how many channels to monitor on.
    pub fn virt_queue_size(&self) -> u16 {
        QUEUE_SIZE
    }

    /// Flush
    pub fn flush(&mut self) -> Result {
        // assert_eq!(buf.len(), SECTOR_SIZE);
        let req = BlkReq {
            type_: ReqType::Flush,
            reserved: 0,
            sector: 0,
        };
        let mut resp = BlkResp::default();
        let support_event = self.support_event();
        let mut inner = self.inner.lock();
        inner.queue.add_notify_wait_pop(
            &[req.as_bytes()],
            &mut [resp.as_bytes_mut()],
            &mut self.transport,
            support_event,
        )?;

        resp.status.into()
    }

    /// Submits a request to write **multiple** blocks, but returns immediately without waiting for the read to
    /// complete.
    pub fn write_blocks(&mut self, block_id: usize, bufs: &[&[u8]]) -> Result {
        assert_eq!(self.readonly(), false);

        let req = BlkReq {
            type_: ReqType::Out,
            reserved: 0,
            sector: block_id as u64,
        };
        let mut resp = BlkResp::default();

        let mut inputs = vec![req.as_bytes(); 1 + bufs.len()];
        let mut index = 1;
        for x in bufs.iter() {
            inputs[index] = *x;
            index += 1;
        }
        let support_event = self.support_event();
        let mut inner = self.inner.lock();
        inner.queue.add_notify_wait_pop(
            inputs.as_slice(),
            &mut [resp.as_bytes_mut()],
            &mut self.transport,
            support_event,
        )?;
        resp.status.into()
    }

    /// Submits a request to write **multiple** blocks, but returns immediately without waiting for the read to
    /// complete.
    pub fn read_blocks(&mut self, block_id: usize, bufs: &mut [&mut [u8]]) -> Result {
        assert_eq!(self.readonly(), false);

        let req = BlkReq {
            type_: ReqType::In,
            reserved: 0,
            sector: block_id as u64,
        };
        let mut resp = BlkResp::default();

        let mut outputs: Vec<&mut [u8]> = Vec::new();
        for x in bufs.iter_mut() {
            outputs.push(*x);
        }
        outputs.push(resp.as_bytes_mut());

        let support_event = self.support_event();
        let mut inner = self.inner.lock();
        inner.queue.add_notify_wait_pop(
            &[req.as_bytes()],
            &mut outputs.as_mut_slice(),
            &mut self.transport,
            support_event,
        )?;
        resp.status.into()
    }

    /// get the device id
    pub fn get_device_id(&mut self, buf: &mut [u8]) -> Result {
        let req = BlkReq {
            type_: ReqType::GetID,
            reserved: 0,
            sector: 0,
        };

        let mut resp = BlkResp::default();
        let support_event = self.support_event();
        let mut inner = self.inner.lock();
        inner.queue.add_notify_wait_pop(
            &[req.as_bytes()],
            &mut [buf, resp.as_bytes_mut()],
            &mut self.transport,
            support_event,
        )?;
        resp.status.into()
    }

    /// discard nu_block blocks starting from start_block
    pub fn discard_ranges(
        &mut self,
        start_sectors: &[u64],
        nr_sectors: &[u32],
    ) -> Result {
        let req = BlkReq {
            type_: ReqType::Discard,
            reserved: 0,
            sector: 0,
        };
        let unmap = false;
        self.erase_ranges(&req, start_sectors, nr_sectors, unmap, true)
    }

    /// wirtezeros nu_block blocks starting from start_block
    pub fn writezeros_ranges(
        &mut self,
        start_sectors: &[u64],
        nr_sectors: &[u32],
    ) -> Result {
        let req = BlkReq {
            type_: ReqType::WriteZeroes,
            reserved: 0,
            sector: 0,
        };
        let unmap  = false;
        self.erase_ranges(&req, start_sectors, nr_sectors, unmap, false)
    }

    /// erase nu_block blocks starting from start_block without blocking
    fn erase_ranges(
        &mut self,
        req: &BlkReq,
        start_sectors: &[u64],
        nr_sectors: &[u32],
        unmap: bool,
        is_discard: bool,
    ) -> Result {
        assert_eq!(start_sectors.len(), nr_sectors.len());

        let (input, nr_seg_used) =
            self.prepare_erase_ranges(start_sectors, nr_sectors, unmap, is_discard);

        let input_f = unsafe {
            core::slice::from_raw_parts(
                input.as_ptr() as *const u8,
                core::mem::size_of::<Range>() * nr_seg_used,
            )
        };
        let support_event = self.support_event();
        let mut resp = BlkResp::default();
        let mut inner = self.inner.lock();

        inner.queue.add_notify_wait_pop(
            &[req.as_bytes(), input_f],
            &mut [resp.as_bytes_mut()],
            &mut self.transport,
            support_event,
        )?;
        resp.status.into()
    }

    /// prepare for erase
    fn prepare_erase_ranges(
        &mut self,
        start_sectors: &[u64],
        nr_sectors: &[u32],
        unmap: bool,
        is_discard: bool,
    ) -> (Vec<Range>, usize) {
        assert_eq!(start_sectors.len(), nr_sectors.len());

        let discard_sector_alignment = self.config.discard_sector_alignment;
        let num_seg = start_sectors.len();
        let mut input = vec![
            Range {
                sector: 1,
                num_sector: 1,
                flags: 0
            };
            num_seg * 2
        ];

        let mut nr_seg_used = 0;
        let mut start_sectors = start_sectors.iter();
        for nr_sector in nr_sectors.iter() {
            let start_sector = *start_sectors.next().unwrap();
            let flag = match unmap {true => 1, false => 0,};
            if is_discard && *nr_sector % discard_sector_alignment != 0 {
                let nr_first_sector = nr_sector % discard_sector_alignment;
                assert!((nr_sector - nr_first_sector) < self.config.max_discard_sectors);
                input[nr_seg_used].flags = flag;
                input[nr_seg_used].num_sector = nr_first_sector;
                input[nr_seg_used].sector = start_sector;
                nr_seg_used += 1;
                input[nr_seg_used].flags = flag;
                input[nr_seg_used].num_sector = nr_sector - nr_first_sector;
                input[nr_seg_used].sector = start_sector + nr_first_sector as u64;
                nr_seg_used += 1;
            } else {
                if is_discard {
                    assert!(*nr_sector < self.config.max_discard_sectors);
                } else {
                    assert!(*nr_sector < self.config.max_write_zeroes_sectors);
                }
                input[nr_seg_used].flags = flag;
                input[nr_seg_used].num_sector = *nr_sector;
                input[nr_seg_used].sector = start_sector;
                nr_seg_used += 1;
            }
        }
        if is_discard {
            assert!(
                nr_seg_used <= self.config.max_discard_seg as usize,
                "The device does not support two many discarded segments in a single request"
            )
        } else {
            assert!(
                nr_seg_used <= self.config.max_write_zeroes_seg as usize,
                "The device does not support two many writezeros segments in a single request"
            )
        }
        (input, nr_seg_used)
    }
}

impl<H: Hal, T: Transport> VirtIOBlk<H, T> {
    /// Submits a request to write **multiple** blocks, but returns immediately without waiting for the read to
    /// complete.
    pub unsafe fn write_blocks_nb_sync(
        &mut self,
        block_id: usize,
        req: &mut BlkReq,
        bufs: &[&[u8]],
        resp: &mut BlkResp,
    ) -> Result<u16> {
        assert_eq!(self.readonly(), true);
        *req = BlkReq {
            type_: ReqType::Out,
            reserved: 0,
            sector: block_id as u64,
        };

        let mut inputs = vec![req.as_bytes(); 1 + bufs.len()];
        let mut index = 1;
        for x in bufs.iter() {
            inputs[index] = *x;
            index += 1;
        }
        let mut inner = self.inner.lock();
        let token = inner
            .queue
            .add(inputs.as_slice(), &mut [resp.as_bytes_mut()])?;
        if inner
            .queue
            .should_notify(self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX))
        {
            self.transport.notify(QUEUE);
        }
        Ok(token)
    }

    /// Submits a request to write **multiple** blocks, but returns immediately without waiting for the read to
    /// complete.
    pub unsafe fn write_blocks_nb_async(
        &mut self,
        block_id: usize,
        req: &mut BlkReq,
        bufs: &[&[u8]],
    ) -> Pin<Box<BlkFuture<H>>> {
        assert_eq!(self.readonly(), true);
        *req = BlkReq {
            type_: ReqType::Out,
            reserved: 0,
            sector: block_id as u64,
        };

        let mut inputs = vec![req.as_bytes(); 1 + bufs.len()];
        let mut index = 1;
        for x in bufs.iter() {
            inputs[index] = *x;
            index += 1;
        }
        let mut inner = self.inner.lock();
        let mut future = Box::pin(BlkFuture::new(self.inner.clone()));

        match inner
            .queue
            .add(inputs.as_slice(), &mut [future.resp.as_bytes_mut()])
        {
            Ok(n) => {
                future.head = n;
                if inner
                    .queue
                    .should_notify(self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX))
                {
                    self.transport.notify(QUEUE);
                }
            }
            Err(e) => future.err = Some(e),
        }

        future
    }

    /// Submits a request to write **multiple** blocks, but returns immediately without waiting for the read to
    /// complete.
    pub unsafe fn read_blocks_nb_async(
        &mut self,
        block_id: usize,
        bufs: &mut [&mut [u8]],
    ) -> Pin<Box<BlkFuture<H>>> {
        assert_eq!(self.readonly(), false);

        let req = BlkReq {
            type_: ReqType::In,
            reserved: 0,
            sector: block_id as u64,
        };
        let mut future = Box::pin(BlkFuture::new(self.inner.clone()));

        let mut outputs: Vec<&mut [u8]> = Vec::new();
        for x in bufs.iter_mut() {
            outputs.push(*x);
        }
        outputs.push(future.resp.as_bytes_mut());

        let mut inner = self.inner.lock();
        match inner
            .queue
            .add(&[req.as_bytes()], &mut outputs.as_mut_slice())
        {
            Ok(n) => {
                future.head = n;
                if inner
                    .queue
                    .should_notify(self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX))
                {
                    self.transport.notify(QUEUE);
                }
            }
            Err(e) => future.err = Some(e),
        }
        future
    }

    /// Submits a request to write **multiple** blocks, but returns immediately without waiting for the read to
    /// complete.
    pub unsafe fn read_blocks_nb_sync(
        &mut self,
        block_id: usize,
        bufs: &mut [&mut [u8]],
        resp: &mut BlkResp,
    ) -> Result<u16> {
        assert_eq!(self.readonly(), false);

        let req = BlkReq {
            type_: ReqType::In,
            reserved: 0,
            sector: block_id as u64,
        };

        let mut outputs: Vec<&mut [u8]> = Vec::new();
        for x in bufs.iter_mut() {
            outputs.push(*x);
        }
        outputs.push(resp.as_bytes_mut());

        let mut inner = self.inner.lock();
        let token = inner
            .queue
            .add(&[req.as_bytes()], &mut outputs.as_mut_slice())?;
        if inner
            .queue
            .should_notify(self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX))
        {
            self.transport.notify(QUEUE);
        }
        Ok(token)
    }

    /// discard nu_block blocks starting from start_block
    pub unsafe fn discard_ranges_nb_sync(
        &mut self,
        req: &mut BlkReq,
        start_sectors: &[u64],
        nr_sectors: &[u32],
        resp: &mut BlkResp,
    ) -> Result<u16> {
        *req = BlkReq {
            type_: ReqType::Discard,
            reserved: 0,
            sector: 0,
        };
        let unmap = false;
        self.erase_ranges_nb_sync(req, start_sectors, nr_sectors, unmap, resp, true)
    }

    /// discard nu_block blocks starting from start_block
    pub unsafe fn discard_ranges_nb_async(
        &mut self,
        req: &mut BlkReq,
        start_sectors: &[u64],
        nr_sectors: &[u32],
    ) -> Pin<Box<BlkFuture<H>>> {
        *req = BlkReq {
            type_: ReqType::Discard,
            reserved: 0,
            sector: 0,
        };
        let unmap = false;
        self.erase_ranges_nb_async(req, start_sectors, nr_sectors, unmap, true)
    }

    /// discard nu_block blocks starting from start_block
    pub unsafe fn writezeros_ranges_nb_sync(
        &mut self,
        req: &mut BlkReq,
        start_sectors: &[u64],
        nr_sectors: &[u32],
        resp: &mut BlkResp,
    ) -> Result<u16> {
        *req = BlkReq {
            type_: ReqType::WriteZeroes,
            reserved: 0,
            sector: 0,
        };
        let unmap = false;
        self.erase_ranges_nb_sync(req, start_sectors, nr_sectors, unmap, resp, false)
    }
    /// discard nu_block blocks starting from start_block
    pub unsafe fn writezeros_ranges_nb_async(
        &mut self,
        req: &mut BlkReq,
        start_sectors: &[u64],
        nr_sectors: &[u32],
    ) -> Pin<Box<BlkFuture<H>>> {
        *req = BlkReq {
            type_: ReqType::WriteZeroes,
            reserved: 0,
            sector: 0,
        };
        let unmap = false;
        self.erase_ranges_nb_async(req, start_sectors, nr_sectors, unmap, false)
    }

    /// get the device id
    pub unsafe fn get_device_id_nb_sync(
        &mut self,
        req: &mut BlkReq,
        buf: &mut [u8],
        resp: &mut BlkResp,
    ) -> Result<u16> {
        *req = BlkReq {
            type_: ReqType::GetID,
            reserved: 0,
            sector: 0,
        };

        let mut inner = self.inner.lock();
        let token = inner
            .queue
            .add(&[req.as_bytes()], &mut [buf, resp.as_bytes_mut()])?;
        if inner
            .queue
            .should_notify(self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX))
        {
            self.transport.notify(QUEUE);
        }
        Ok(token)
    }

    /// get the device id
    pub unsafe fn get_device_id_nb_async(
        &mut self,
        req: &mut BlkReq,
        buf: &mut [u8],
    ) -> Pin<Box<BlkFuture<H>>> {
        *req = BlkReq {
            type_: ReqType::GetID,
            reserved: 0,
            sector: 0,
        };

        let mut inner = self.inner.lock();
        let mut future = Box::pin(BlkFuture::new(self.inner.clone()));

        match inner
            .queue
            .add(&[req.as_bytes()], &mut [buf, future.resp.as_bytes_mut()])
        {
            Ok(n) => {
                future.head = n;
                if inner
                    .queue
                    .should_notify(self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX))
                {
                    self.transport.notify(QUEUE);
                }
            }
            Err(e) => future.err = Some(e),
        }
        future
    }

    /// Flush
    pub unsafe fn flush_nb_async(&mut self) -> Pin<Box<BlkFuture<H>>> {
        // assert_eq!(buf.len(), SECTOR_SIZE);
        let req = BlkReq {
            type_: ReqType::Flush,
            reserved: 0,
            sector: 0,
        };

        let mut inner = self.inner.lock();
        let mut future = Box::pin(BlkFuture::new(self.inner.clone()));

        match inner
            .queue
            .add(&[req.as_bytes()], &mut [future.resp.as_bytes_mut()])
        {
            Ok(n) => {
                future.head = n;
                if inner
                    .queue
                    .should_notify(self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX))
                {
                    self.transport.notify(QUEUE);
                }
            }
            Err(e) => future.err = Some(e),
        }

        future
    }

    /// Flush
    pub unsafe fn flush_nb_sync(&mut self) -> Result {
        // assert_eq!(buf.len(), SECTOR_SIZE);
        let req = BlkReq {
            type_: ReqType::Flush,
            reserved: 0,
            sector: 0,
        };
        let mut resp = BlkResp::default();
        let mut inner = self.inner.lock();

        inner
            .queue
            .add(&[req.as_bytes()], &mut [resp.as_bytes_mut()])?;

        if inner
            .queue
            .should_notify(self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX))
        {
            self.transport.notify(QUEUE);
        }

        resp.status.into()
    }

    /// erase nu_block blocks starting from start_block without blocking
    unsafe fn erase_ranges_nb_sync(
        &mut self,
        req: &BlkReq,
        start_sectors: &[u64],
        nr_sectors: &[u32],
        unmap: bool,
        resp: &mut BlkResp,
        is_discard: bool,
    ) -> Result<u16> {
        assert_eq!(start_sectors.len(), nr_sectors.len());

        let (input, nr_seg_used) =
            self.prepare_erase_ranges(start_sectors, nr_sectors, unmap, is_discard);

        let input_f = unsafe {
            core::slice::from_raw_parts(
                input.as_ptr() as *const u8,
                core::mem::size_of::<Range>() * nr_seg_used,
            )
        };
        let mut inner = self.inner.lock();
        let token = inner
            .queue
            .add(&[req.as_bytes(), input_f], &mut [resp.as_bytes_mut()])?;
        if inner
            .queue
            .should_notify(self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX))
        {
            self.transport.notify(QUEUE);
        }
        Ok(token)
    }

    /// erase nu_block blocks starting from start_block without blocking
    unsafe fn erase_ranges_nb_async(
        &mut self,
        req: &BlkReq,
        start_sectors: &[u64],
        nr_sectors: &[u32],
        unmap: bool,
        is_discard: bool,
    ) -> Pin<Box<BlkFuture<H>>> {
        assert_eq!(start_sectors.len(), nr_sectors.len());

        let (input, nr_seg_used) =
            self.prepare_erase_ranges(start_sectors, nr_sectors, unmap, is_discard);

        let input_f = unsafe {
            core::slice::from_raw_parts(
                input.as_ptr() as *const u8,
                core::mem::size_of::<Range>() * nr_seg_used,
            )
        };
        let mut inner = self.inner.lock();
        let mut future = Box::pin(BlkFuture::new(self.inner.clone()));

        match inner.queue.add(
            &[req.as_bytes(), input_f],
            &mut [future.resp.as_bytes_mut()],
        ) {
            Ok(n) => {
                future.head = n;
                if inner
                    .queue
                    .should_notify(self.features_neg.contains(BlkFeature::VIRTIO_F_EVENT_IDX))
                {
                    self.transport.notify(QUEUE);
                }
            }
            Err(e) => future.err = Some(e),
        }
        future
    }
}

impl<'a, H: Hal, T: Transport> Drop for VirtIOBlk<H, T> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(QUEUE);
    }
}

///
/// Ref: linux kernel (virtio_blk.h: virtio_blk_config)
#[repr(C)]
struct BlkConfig {
    /// The capacity (in 512-byte sectors).
    capacity_low: Volatile<u32>,
    capacity_high: Volatile<u32>,

    /// The maximum segment size (if VIRTIO_BLK_F_SIZE_MAX)
    size_max: Volatile<u32>,

    /// The maximum number of segments (if VIRTIO_BLK_F_SEG_MAX)
    seg_max: Volatile<u32>,

    /// geometry of the device (if VIRTIO_BLK_F_GEOMETRY)
    cylinders: Volatile<u16>,
    heads: Volatile<u8>,
    sectors: Volatile<u8>,

    /// block size of device (if VIRTIO_BLK_F_BLK_SIZE)
    blk_size: Volatile<u32>,

    /// the next 4 entries are guarded by VIRTIO_BLK_F_TOPOLOGY
    /// exponent for physical block per logical block.
    physical_block_exp: Volatile<u8>,

    /// alignment offset in logical blocks.
    alignment_offset: Volatile<u8>,

    /// minimum I/O size without performance penalty in logical blocks.
    min_io_size: Volatile<u16>,

    /// optimal sustained I/O size in logical blocks.
    opt_io_size: Volatile<u32>,

    /// writeback mode (if VIRTIO_BLK_F_CONFIG_WCE)
    wce: Volatile<u8>,
    unused: Volatile<u8>,

    /// number of vqs, only available when VIRTIO_BLK_F_MQ is set
    num_queues: Volatile<u16>,

    /// the next 3 entries are guarded by VIRTIO_BLK_F_DISCARD
    ///
    /// The maximum discard sectors (in 512-byte sectors) for
    /// one segment.
    max_discard_sectors: Volatile<u32>,

    /// The maximum number of discard segments in a discard command.
    max_discard_seg: Volatile<u32>,

    /// Discard commands must be aligned to this number of sectors.
    discard_sector_alignment: Volatile<u32>,

    /// the next 3 entries are guarded by VIRTIO_BLK_F_WRITE_ZEROES.
    /// The maximum number of write zeroes sectors (in 512-byte sectors) in one segment.
    max_write_zeroes_sectors: Volatile<u32>,

    /// The maximum number of segments in a write zeroes command.
    max_write_zeroes_seg: Volatile<u32>,

    /// Set if a VIRTIO_BLK_T_WRITE_ZEROES request may result in the deallocation of one or more of the sectors.
    write_zeroes_may_unmap: Volatile<u8>,

    unused1: [Volatile<u8>; 3],
}
struct Blkconfiglocal {
    /// The capacity (in 512-byte sectors).
    capacity: u64,

    /// The maximum segment size (if VIRTIO_BLK_F_SIZE_MAX)
    size_max: u32,

    /// The maximum number of segments (if VIRTIO_BLK_F_SEG_MAX)
    seg_max: u32,

    /// geometry of the device (if VIRTIO_BLK_F_GEOMETRY)
    cylinders: u16,
    heads: u8,
    sectors: u8,

    /// block size of device (if VIRTIO_BLK_F_BLK_SIZE)
    blk_size: u32,

    /// the next 4 entries are guarded by VIRTIO_BLK_F_TOPOLOGY
    /// exponent for physical block per logical block.
    physical_block_exp: u8,

    /// alignment offset in logical blocks.
    alignment_offset: u8,

    /// minimum I/O size without performance penalty in logical blocks.
    min_io_size: u16,

    /// optimal sustained I/O size in logical blocks.
    opt_io_size: u32,

    /// writeback mode (if VIRTIO_BLK_F_CONFIG_WCE)
    wce: u8,

    /// number of vqs, only available when VIRTIO_BLK_F_MQ is set
    num_queues: u16,

    /// the next 3 entries are guarded by VIRTIO_BLK_F_DISCARD
    ///
    /// The maximum discard sectors (in 512-byte sectors) for
    /// one segment.
    max_discard_sectors: u32,

    /// The maximum number of discard segments in a discard command.
    max_discard_seg: u32,

    /// Discard commands must be aligned to this number of sectors.
    discard_sector_alignment: u32,

    /// the next 3 entries are guarded by VIRTIO_BLK_F_WRITE_ZEROES.
    /// The maximum number of write zeroes sectors (in 512-byte sectors) in one segment.
    max_write_zeroes_sectors: u32,

    /// The maximum number of segments in a write zeroes command.
    max_write_zeroes_seg: u32,

    /// Set if a VIRTIO_BLK_T_WRITE_ZEROES request may result in the deallocation of one or more of the sectors.
    write_zeroes_may_unmap: u8,
}
/// A VirtIO block device request.
///
/// Ref: virtio_blk.c virtio_blk_outhdr
#[repr(C)]
#[derive(AsBytes, Debug)]
pub struct BlkReq {
    /// VIRTIO_BLK_T*
    type_: ReqType,
    /// io priority.
    reserved: u32,
    /// Sector (ie. 512 byte offset)
    sector: u64,
}

impl Default for BlkReq {
    fn default() -> Self {
        Self {
            type_: ReqType::In,
            reserved: 0,
            sector: 0,
        }
    }
}

/// Response of a VirtIOBlk request.
#[repr(C)]
#[derive(AsBytes, Debug, FromBytes)]
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
#[derive(AsBytes, Debug)]
enum ReqType {
    In = 0,
    Out = 1,
    Flush = 4,
    GetID = 8,
    GetLifeTime = 10,
    Discard = 11,
    WriteZeroes = 13,
    SecureErase = 14,
}

/// Status of a VirtIOBlk request.
#[repr(transparent)]
#[derive(AsBytes, Copy, Clone, Debug, Eq, FromBytes, PartialEq)]
pub struct RespStatus(u8);

impl RespStatus {
    /// Ok.
    pub const OK: RespStatus = RespStatus(0);
    /// IoErr.
    pub const IO_ERR: RespStatus = RespStatus(1);
    /// Unsupported yet.
    pub const UNSUPPORTED: RespStatus = RespStatus(2);
    /// Not ready.
    pub const NOT_READY: RespStatus = RespStatus(3);
}

impl From<RespStatus> for Result {
    fn from(status: RespStatus) -> Self {
        match status {
            RespStatus::OK => Ok(()),
            RespStatus::IO_ERR => Err(Error::IoError),
            RespStatus::UNSUPPORTED => Err(Error::Unsupported),
            RespStatus::NOT_READY => Err(Error::NotReady),
            _ => Err(Error::IoError),
        }
    }
}

impl Default for BlkResp {
    fn default() -> Self {
        BlkResp {
            status: RespStatus::NOT_READY,
        }
    }
}

/// The standard sector size of a VirtIO block device. Data is read and written in multiples of this
/// size.
pub const SECTOR_SIZE: usize = 512;

bitflags! {
    struct BlkFeature: u64 {
        /// Device supports request barriers. (legacy)
        const VIRTIO_BLK_F_BARRIER       = 1 << 0;
        /// Maximum size of any single segment is in `size_max`.
        const VIRTIO_BLK_F_SIZE_MAX      = 1 << 1;
        /// Maximum number of segments in a request is in `seg_max`.
        const VIRTIO_BLK_F_SEG_MAX       = 1 << 2;
        /// Disk-style geometry specified in geometry.
        const VIRTIO_BLK_F_GEOMETRY      = 1 << 4;
        /// Device is read-only.
        const VIRTIO_BLK_F_RO            = 1 << 5;
        /// Block size of disk is in `blk_size`.
        const VIRTIO_BLK_F_BLK_SIZE      = 1 << 6;
        /// Device supports scsi packet commands. (legacy)
        const VIRTIO_BLK_F_SCSI          = 1 << 7;
        /// Cache flush command support.
        const VIRTIO_BLK_F_FLUSH         = 1 << 9;
        /// Device exports information on optimal I/O alignment.
        const VIRTIO_BLK_F_TOPOLOGY      = 1 << 10;
        /// Device can toggle its cache between writeback and writethrough modes.
        const VIRTIO_BLK_F_CONFIG_WCE    = 1 << 11;
        /// Device can support discard command, maximum discard sectors size in
        /// `max_discard_sectors` and maximum discard segment number in
        /// `max_discard_seg`.
        const VIRTIO_BLK_F_DISCARD       = 1 << 13;
        /// Device can support write zeroes command, maximum write zeroes sectors
        /// size in `max_write_zeroes_sectors` and maximum write zeroes segment
        /// number in `max_write_zeroes_seg`.
        const VIRTIO_BLK_F_WRITE_ZEROES  = 1 << 14;

        // device independent
        const VIRTIO_F_NOTIFY_ON_EMPTY       = 1 << 24; // legacy
        const VIRTIO_F_ANY_LAYOUT            = 1 << 27; // legacy
        const VIRTIO_F_INDIRECT_DESC         = 1 << 28;
        const VIRTIO_F_EVENT_IDX             = 1 << 29;
        const UNUSED                         = 1 << 30; // legacy
        const VIRTIO_F_VERSION_1             = 1 << 32; // detect legacy

        // the following since virtio v1.1
        const VIRTIO_F_ACCESS_PLATFORM       = 1 << 33;
        const VIRTIO_F_RING_PACKED           = 1 << 34;
        const VIRTIO_F_IN_ORDER              = 1 << 35;
        const VIRTIO_F_ORDER_PLATFORM        = 1 << 36;
        const VIRTIO_F_SR_IOV                = 1 << 37;
        const VIRTIO_F_NOTIFICATION_DATA     = 1 << 38;
    }
}
/// used for discard
pub struct Range {
    /// discard/write zeroes start sector
    sector: u64,
    /// number of discard/write zeroes sectors
    num_sector: u32,
    /// flags for this range
    flags: u32,
}
impl Copy for Range {}

impl Clone for Range {
    fn clone(&self) -> Range {
        Range {
            sector: self.sector,
            num_sector: self.num_sector,
            flags: self.flags,
        }
    }
}

const SECTOR_SHIFT: usize = 9;

// +++++++++++++++++++++++++++++++++++++++
// Async IO
// +++++++++++++++++++++++++++++++++++++++

#[repr(C)]
#[derive(Debug)]
struct BlkInfo {
    waker: Option<Waker>,
}

const NULLINFO: BlkInfo = BlkInfo::new();

impl BlkInfo {
    const fn new() -> Self {
        BlkInfo { waker: None }
    }
}

/// for async IO
pub struct BlkFuture<H: Hal> {
    resp: BlkResp,
    head: u16,
    queue: Arc<Mutex<VirtIoBlkInner<H>>>,
    err: Option<Error>,
}

impl<'a, H: Hal> BlkFuture<H> {
    /// construct a new BlkFuture
    fn new(queue: Arc<Mutex<VirtIoBlkInner<H>>>) -> Self {
        Self {
            resp: BlkResp::default(),
            head: u16::MAX,
            queue: queue,
            err: None,
        }
    }
}

impl<H: Hal> Future for BlkFuture<H> {
    type Output = Result;
    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output> {
        if let Some(e) = self.err {
            return Poll::Ready(Err(e));
        }
        match unsafe { core::ptr::read_volatile(&self.resp.status) } {
            RespStatus::OK => Poll::Ready(Ok(())),
            RespStatus::NOT_READY => {
                self.queue.lock().blkinfos[self.head as usize].waker = Some(cx.waker().clone());
                Poll::Pending
            }
            _ => Poll::Ready(Err(Error::IoError)),
        }
    }
}

// +++++++++++++++++++++++++++++++++++++++
// test
// +++++++++++++++++++++++++++++++++++++++

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        hal::fake::FakeHal,
        transport::{
            fake::{FakeTransport, QueueStatus, State},
            DeviceStatus, DeviceType,
        },
    };
    use alloc::{sync::Arc, vec};
    use core::{mem::size_of, ptr::NonNull};
    use std::{sync::Mutex, thread};

    #[test]
    fn config() {
        let mut config_space = BlkConfig {
            capacity_low: Volatile::new(0x42),
            capacity_high: Volatile::new(0x02),
            size_max: Volatile::new(0),
            seg_max: Volatile::new(0),
            cylinders: Volatile::new(0),
            heads: Volatile::new(0),
            sectors: Volatile::new(0),
            blk_size: Volatile::new(0),
            physical_block_exp: Volatile::new(0),
            alignment_offset: Volatile::new(0),
            min_io_size: Volatile::new(0),
            opt_io_size: Volatile::new(0),
            wce: Volatile::new(0),
            unused: Volatile::new(0),
            max_discard_sectors: Volatile::new(0),
            num_queues: Volatile::new(0),
            max_discard_seg: Volatile::new(0),
            max_write_zeroes_sectors: Volatile::new(0),
            max_write_zeroes_seg: Volatile::new(0),
            write_zeroes_may_unmap: Volatile::new(0),
            discard_sector_alignment: Volatile::new(0),
            unused1: [Volatile::new(0), Volatile::new(0), Volatile::new(0)],
        };
        let state = Arc::new(Mutex::new(State {
            status: DeviceStatus::empty(),
            driver_features: 0,
            guest_page_size: 0,
            interrupt_pending: false,
            queues: vec![QueueStatus::default()],
        }));
        let transport = FakeTransport {
            device_type: DeviceType::Console,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: BlkFeature::VIRTIO_BLK_F_RO.bits(),
            config_space: NonNull::from(&mut config_space),
            state: state.clone(),
        };
        let blk = VirtIOBlk::<FakeHal, FakeTransport<BlkConfig>>::new(transport, false).unwrap();

        assert_eq!(blk.capacity(), 0x02_0000_0042);
        assert_eq!(blk.readonly(), true);
    }

    #[test]
    fn read() {
        let mut config_space = BlkConfig {
            capacity_low: Volatile::new(66),
            capacity_high: Volatile::new(0),
            size_max: Volatile::new(0),
            seg_max: Volatile::new(0),
            cylinders: Volatile::new(0),
            heads: Volatile::new(0),
            sectors: Volatile::new(0),
            blk_size: Volatile::new(0),
            physical_block_exp: Volatile::new(0),
            alignment_offset: Volatile::new(0),
            min_io_size: Volatile::new(0),
            opt_io_size: Volatile::new(0),
            wce: Volatile::new(0),
            unused: Volatile::new(0),
            max_discard_sectors: Volatile::new(0),
            num_queues: Volatile::new(0),
            max_discard_seg: Volatile::new(0),
            max_write_zeroes_sectors: Volatile::new(0),
            max_write_zeroes_seg: Volatile::new(0),
            write_zeroes_may_unmap: Volatile::new(0),
            discard_sector_alignment: Volatile::new(0),
            unused1: [Volatile::new(0), Volatile::new(0), Volatile::new(0)],
        };
        let state = Arc::new(Mutex::new(State {
            status: DeviceStatus::empty(),
            driver_features: 0,
            guest_page_size: 0,
            interrupt_pending: false,
            queues: vec![QueueStatus::default()],
        }));
        let transport = FakeTransport {
            device_type: DeviceType::Console,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: 0,
            config_space: NonNull::from(&mut config_space),
            state: state.clone(),
        };
        let mut blk =
            VirtIOBlk::<FakeHal, FakeTransport<BlkConfig>>::new(transport, false).unwrap();

        // Start a thread to simulate the device waiting for a read request.
        let handle = thread::spawn(move || {
            println!("Device waiting for a request.");
            State::wait_until_queue_notified(&state, QUEUE);
            println!("Transmit queue was notified.");

            state
                .lock()
                .unwrap()
                .read_write_queue::<{ QUEUE_SIZE as usize }>(QUEUE, |request| {
                    assert_eq!(
                        request,
                        BlkReq {
                            type_: ReqType::In,
                            reserved: 0,
                            sector: 42
                        }
                        .as_bytes()
                    );

                    let mut response = vec![0; SECTOR_SIZE];
                    response[0..9].copy_from_slice(b"Test data");
                    response.extend_from_slice(
                        BlkResp {
                            status: RespStatus::OK,
                        }
                        .as_bytes(),
                    );

                    response
                });
        });

        // Read a block from the device.
        let mut buffer = [0; 512];
        blk.read_blocks(42, &mut [&mut buffer]).unwrap();
        assert_eq!(&buffer[0..9], b"Test data");

        handle.join().unwrap();
    }

    #[test]
    fn write() {
        let mut config_space = BlkConfig {
            capacity_low: Volatile::new(66),
            capacity_high: Volatile::new(0),
            size_max: Volatile::new(0),
            seg_max: Volatile::new(0),
            cylinders: Volatile::new(0),
            heads: Volatile::new(0),
            sectors: Volatile::new(0),
            blk_size: Volatile::new(0),
            physical_block_exp: Volatile::new(0),
            alignment_offset: Volatile::new(0),
            min_io_size: Volatile::new(0),
            opt_io_size: Volatile::new(0),
            wce: Volatile::new(0),
            unused: Volatile::new(0),
            max_discard_sectors: Volatile::new(0),
            num_queues: Volatile::new(0),
            max_discard_seg: Volatile::new(0),
            max_write_zeroes_sectors: Volatile::new(0),
            max_write_zeroes_seg: Volatile::new(0),
            write_zeroes_may_unmap: Volatile::new(0),
            discard_sector_alignment: Volatile::new(0),
            unused1: [Volatile::new(0), Volatile::new(0), Volatile::new(0)],
        };
        let state = Arc::new(Mutex::new(State {
            status: DeviceStatus::empty(),
            driver_features: 0,
            guest_page_size: 0,
            interrupt_pending: false,
            queues: vec![QueueStatus::default()],
        }));
        let transport = FakeTransport {
            device_type: DeviceType::Console,
            max_queue_size: QUEUE_SIZE.into(),
            device_features: 0,
            config_space: NonNull::from(&mut config_space),
            state: state.clone(),
        };
        let mut blk =
            VirtIOBlk::<FakeHal, FakeTransport<BlkConfig>>::new(transport, false).unwrap();

        // Start a thread to simulate the device waiting for a write request.
        let handle = thread::spawn(move || {
            println!("Device waiting for a request.");
            State::wait_until_queue_notified(&state, QUEUE);
            println!("Transmit queue was notified.");

            state
                .lock()
                .unwrap()
                .read_write_queue::<{ QUEUE_SIZE as usize }>(QUEUE, |request| {
                    assert_eq!(
                        &request[0..size_of::<BlkReq>()],
                        BlkReq {
                            type_: ReqType::Out,
                            reserved: 0,
                            sector: 42
                        }
                        .as_bytes()
                    );
                    let data = &request[size_of::<BlkReq>()..];
                    assert_eq!(data.len(), SECTOR_SIZE);
                    assert_eq!(&data[0..9], b"Test data");

                    let mut response = Vec::new();
                    response.extend_from_slice(
                        BlkResp {
                            status: RespStatus::OK,
                        }
                        .as_bytes(),
                    );

                    response
                });
        });

        // Write a block to the device.
        let mut buffer = [0; 512];
        buffer[0..9].copy_from_slice(b"Test data");
        blk.write_blocks(42, &[&buffer]).unwrap();

        handle.join().unwrap();
    }
}
