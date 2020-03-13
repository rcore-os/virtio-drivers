use core::slice;

use super::*;
use crate::queue::VirtQueue;
use bitflags::*;
use core::sync::atomic::spin_loop_hint;
use log::*;
use volatile::{ReadOnly, Volatile, WriteOnly};

/// A virtio based graphics adapter.
///
/// It can operate in 2D mode and in 3D (virgl) mode.
/// 3D mode will offload rendering ops to the host gpu and therefore requires
/// a gpu with 3D support on the host machine.
/// In 2D mode the virtio-gpu device provides support for ARGB Hardware cursors
/// and multiple scanouts (aka heads).
pub struct VirtIOGpu<'a> {
    header: &'static mut VirtIOHeader,
    rect: GpuRect,
    frame_buffer: &'a mut [u8],
    /// Queue for sending control commands.
    control_queue: VirtQueue<'a>,
    /// Queue for sending cursor commands.
    cursor_queue: VirtQueue<'a>,
    /// Send buffer for queue.
    queue_buf_send: &'a mut [u8],
    /// Recv buffer for queue.
    queue_buf_recv: &'a mut [u8],
}

impl VirtIOGpu<'_> {
    /// Create a new VirtIO-Gpu driver.
    pub fn new(header: &'static mut VirtIOHeader) -> Result<Self> {
        header.begin_init(|features| {
            let features = GpuFeature::from_bits_truncate(features);
            info!("Device features {:?}", features);
            let supported_features = GpuFeature::empty();
            (features & supported_features).bits()
        });

        // read configuration space
        let config = unsafe { &mut *(header.config_space() as *mut GpuConfig) };
        info!("Config: {:?}", config);

        let control_queue = VirtQueue::new(header, QUEUE_TRANSMIT, 2)?;
        let cursor_queue = VirtQueue::new(header, QUEUE_CURSOR, 2)?;

        let (vaddr, _) = alloc_dma(1)?;
        let queue_buf_send = unsafe { slice::from_raw_parts_mut(vaddr as _, PAGE_SIZE) };
        let (vaddr, _) = alloc_dma(1)?;
        let queue_buf_recv = unsafe { slice::from_raw_parts_mut(vaddr as _, PAGE_SIZE) };

        header.finish_init();

        let mut driver = VirtIOGpu {
            header,
            frame_buffer: &mut [],
            rect: GpuRect::default(),
            control_queue,
            cursor_queue,
            queue_buf_send,
            queue_buf_recv,
        };
        driver.setup_framebuffer()?;
        Ok(driver)
    }

    fn setup_framebuffer(&mut self) -> Result {
        // get display info
        let display_info: GpuRespDisplayInfo =
            self.request(GpuCtrlHdr::with_type(Command::GetDisplayInfo))?;
        info!("get display info => {:?}", display_info);
        self.rect = display_info.rect;

        // create resource 2d
        let rsp: GpuCtrlHdr = self.request(GpuResourceCreate2D {
            header: GpuCtrlHdr::with_type(Command::ResourceCreate2d),
            resource_id: GPU_RESOURCE_ID,
            format: GPU_FORMAT_B8G8R8A8_UNORM,
            width: display_info.rect.width,
            height: display_info.rect.height,
        })?;
        info!("create resource 2d => {:?}", rsp);

        // alloc continuous pages for the frame buffer
        let size = display_info.rect.width * display_info.rect.height * 4;
        let (vaddr, paddr) = alloc_dma(pages(size as usize))?;
        self.frame_buffer = unsafe { slice::from_raw_parts_mut(vaddr as _, size as usize) };

        // resource_attach_backing
        let rsp: GpuCtrlHdr = self.request(GpuResourceAttachBacking {
            header: GpuCtrlHdr::with_type(Command::ResourceAttachBacking),
            resource_id: GPU_RESOURCE_ID,
            nr_entries: 1,
            addr: paddr as u64,
            length: size,
            padding: 0,
        })?;
        info!("resource attach backing => {:?}", rsp);

        // map frame buffer to screen
        let rsp: GpuCtrlHdr = self.request(GpuSetScanout {
            header: GpuCtrlHdr::with_type(Command::SetScanout),
            rect: display_info.rect,
            scanout_id: 0,
            resource_id: GPU_RESOURCE_ID,
        })?;
        info!("set scanout => {:?}", rsp);

        self.flush()?;
        Ok(())
    }

    /// Flush framebuffer to screen.
    pub fn flush(&mut self) -> Result {
        // copy data from guest to host
        let rsp: GpuCtrlHdr = self.request(GpuTransferToHost2D {
            header: GpuCtrlHdr::with_type(Command::TransferToHost2d),
            rect: self.rect,
            offset: 0,
            resource_id: GPU_RESOURCE_ID,
            padding: 0,
        })?;
        info!("transfer to host 2d => {:?}", rsp);

        // flush data to screen
        let rsp: GpuCtrlHdr = self.request(GpuResourceFlush {
            header: GpuCtrlHdr::with_type(Command::ResourceFlush),
            rect: self.rect,
            resource_id: GPU_RESOURCE_ID,
            padding: 0,
        })?;
        info!("resource flush => {:?}", rsp);

        Ok(())
    }

    /// Send a request to the device and block for a response.
    fn request<Req, Rsp>(&mut self, req: Req) -> Result<Rsp> {
        unsafe {
            (self.queue_buf_send.as_mut_ptr() as *mut Req).write(req);
        }
        self.control_queue
            .add(&[self.queue_buf_send], &[self.queue_buf_recv])?;
        self.header.notify(QUEUE_TRANSMIT as u32);
        while !self.control_queue.can_get() {
            spin_loop_hint();
        }
        self.control_queue.get()?;
        Ok(unsafe { (self.queue_buf_recv.as_ptr() as *const Rsp).read() })
    }
}

#[repr(C)]
#[derive(Debug)]
struct GpuConfig {
    /// Signals pending events to the driver。
    events_read: ReadOnly<u32>,

    /// Clears pending events in the device.
    events_clear: WriteOnly<u32>,

    /// Specifies the maximum number of scanouts supported by the device.
    ///
    /// Minimum value is 1, maximum value is 16.
    num_scanouts: Volatile<u32>,
}

/// Display configuration has changed.
const GPU_EVENT_DISPLAY: u32 = 1 << 0;

bitflags! {
    struct GpuFeature: u64 {
        /// virgl 3D mode is supported.
        const VIRGL                 = 1 << 0;
        /// EDID is supported.
        const EDID                  = 1 << 1;

        // device independent
        const NOTIFY_ON_EMPTY       = 1 << 24; // legacy
        const ANY_LAYOUT            = 1 << 27; // legacy
        const RING_INDIRECT_DESC    = 1 << 28;
        const RING_EVENT_IDX        = 1 << 29;
        const UNUSED                = 1 << 30; // legacy
        const VERSION_1             = 1 << 32; // detect legacy

        // since virtio v1.1
        const ACCESS_PLATFORM       = 1 << 33;
        const RING_PACKED           = 1 << 34;
        const IN_ORDER              = 1 << 35;
        const ORDER_PLATFORM        = 1 << 36;
        const SR_IOV                = 1 << 37;
        const NOTIFICATION_DATA     = 1 << 38;
    }
}

#[repr(u32)]
#[derive(Debug)]
enum Command {
    GetDisplayInfo = 0x100,
    ResourceCreate2d = 0x101,
    ResourceUnref = 0x102,
    SetScanout = 0x103,
    ResourceFlush = 0x104,
    TransferToHost2d = 0x105,
    ResourceAttachBacking = 0x106,
    ResourceDetachBacking = 0x107,
    GetCapsetInfo = 0x108,
    GetCapset = 0x109,
    GetEdid = 0x10a,

    UpdateCursor = 0x300,
    MoveCursor = 0x301,

    OkNodata = 0x1100,
    OkDisplayInfo = 0x1101,
    OkCapsetInfo = 0x1102,
    OkCapset = 0x1103,
    OkEdid = 0x1104,

    ErrUnspec = 0x1200,
    ErrOutOfMemory = 0x1201,
    ErrInvalidScanoutId = 0x1202,
}

const GPU_FLAG_FENCE: u32 = 1 << 0;

#[repr(C)]
#[derive(Debug)]
struct GpuCtrlHdr {
    hdr_type: Command,
    flags: u32,
    fence_id: u64,
    ctx_id: u32,
    padding: u32,
}

impl GpuCtrlHdr {
    fn with_type(hdr_type: Command) -> GpuCtrlHdr {
        GpuCtrlHdr {
            hdr_type,
            flags: 0,
            fence_id: 0,
            ctx_id: 0,
            padding: 0,
        }
    }
}

#[repr(C)]
#[derive(Debug, Copy, Clone, Default)]
struct GpuRect {
    x: u32,
    y: u32,
    width: u32,
    height: u32,
}

#[repr(C)]
#[derive(Debug)]
struct GpuRespDisplayInfo {
    header: GpuCtrlHdr,
    rect: GpuRect,
    enabled: u32,
    flags: u32,
}

const GPU_FORMAT_B8G8R8A8_UNORM: u32 = 1;

#[repr(C)]
#[derive(Debug)]
struct GpuResourceCreate2D {
    header: GpuCtrlHdr,
    resource_id: u32,
    format: u32,
    width: u32,
    height: u32,
}

#[repr(C)]
#[derive(Debug)]
struct GpuResourceAttachBacking {
    header: GpuCtrlHdr,
    resource_id: u32,
    nr_entries: u32, // always 1
    addr: u64,
    length: u32,
    padding: u32,
}

#[repr(C)]
#[derive(Debug)]
struct GpuSetScanout {
    header: GpuCtrlHdr,
    rect: GpuRect,
    scanout_id: u32,
    resource_id: u32,
}

#[repr(C)]
#[derive(Debug)]
struct GpuTransferToHost2D {
    header: GpuCtrlHdr,
    rect: GpuRect,
    offset: u64,
    resource_id: u32,
    padding: u32,
}

#[repr(C)]
#[derive(Debug)]
struct GpuResourceFlush {
    header: GpuCtrlHdr,
    rect: GpuRect,
    resource_id: u32,
    padding: u32,
}

const QUEUE_TRANSMIT: usize = 0;
const QUEUE_CURSOR: usize = 1;

const GPU_RESOURCE_ID: u32 = 0xbabe;
