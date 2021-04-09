use super::*;
use crate::queue::VirtQueue;
use bitflags::*;
use core::hint::spin_loop;
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
    rect: Rect,
    /// DMA area of frame buffer.
    frame_buffer_dma: Option<DMA>,
    /// Queue for sending control commands.
    control_queue: VirtQueue<'a>,
    /// Queue for sending cursor commands.
    cursor_queue: VirtQueue<'a>,
    /// Queue buffer DMA
    queue_buf_dma: DMA,
    /// Send buffer for queue.
    queue_buf_send: &'a mut [u8],
    /// Recv buffer for queue.
    queue_buf_recv: &'a mut [u8],
}

impl VirtIOGpu<'_> {
    /// Create a new VirtIO-Gpu driver.
    pub fn new(header: &'static mut VirtIOHeader) -> Result<Self> {
        header.begin_init(|features| {
            let features = Features::from_bits_truncate(features);
            info!("Device features {:?}", features);
            let supported_features = Features::empty();
            (features & supported_features).bits()
        });

        // read configuration space
        let config = unsafe { &mut *(header.config_space() as *mut Config) };
        info!("Config: {:?}", config);

        let control_queue = VirtQueue::new(header, QUEUE_TRANSMIT, 2)?;
        let cursor_queue = VirtQueue::new(header, QUEUE_CURSOR, 2)?;

        let queue_buf_dma = DMA::new(2)?;
        let queue_buf_send = unsafe { &mut queue_buf_dma.as_buf()[..PAGE_SIZE] };
        let queue_buf_recv = unsafe { &mut queue_buf_dma.as_buf()[PAGE_SIZE..] };

        header.finish_init();

        Ok(VirtIOGpu {
            header,
            frame_buffer_dma: None,
            rect: Rect::default(),
            control_queue,
            cursor_queue,
            queue_buf_dma,
            queue_buf_send,
            queue_buf_recv,
        })
    }

    /// Acknowledge interrupt.
    pub fn ack_interrupt(&mut self) -> bool {
        self.header.ack_interrupt()
    }

    /// Get the resolution (width, height).
    pub fn resolution(&self) -> (u32, u32) {
        (self.rect.width, self.rect.height)
    }

    /// Setup framebuffer
    pub fn setup_framebuffer(&mut self) -> Result<&mut [u8]> {
        // get display info
        let display_info: RespDisplayInfo =
            self.request(CtrlHeader::with_type(Command::GetDisplayInfo))?;
        display_info.header.check_type(Command::OkDisplayInfo)?;
        info!("=> {:?}", display_info);
        self.rect = display_info.rect;

        // create resource 2d
        let rsp: CtrlHeader = self.request(ResourceCreate2D {
            header: CtrlHeader::with_type(Command::ResourceCreate2d),
            resource_id: RESOURCE_ID,
            format: Format::B8G8R8A8UNORM,
            width: display_info.rect.width,
            height: display_info.rect.height,
        })?;
        rsp.check_type(Command::OkNodata)?;

        // alloc continuous pages for the frame buffer
        let size = display_info.rect.width * display_info.rect.height * 4;
        let frame_buffer_dma = DMA::new(pages(size as usize))?;

        // resource_attach_backing
        let rsp: CtrlHeader = self.request(ResourceAttachBacking {
            header: CtrlHeader::with_type(Command::ResourceAttachBacking),
            resource_id: RESOURCE_ID,
            nr_entries: 1,
            addr: frame_buffer_dma.paddr() as u64,
            length: size,
            padding: 0,
        })?;
        rsp.check_type(Command::OkNodata)?;

        // map frame buffer to screen
        let rsp: CtrlHeader = self.request(SetScanout {
            header: CtrlHeader::with_type(Command::SetScanout),
            rect: display_info.rect,
            scanout_id: 0,
            resource_id: RESOURCE_ID,
        })?;
        rsp.check_type(Command::OkNodata)?;

        let buf = unsafe { frame_buffer_dma.as_buf() };
        self.frame_buffer_dma = Some(frame_buffer_dma);
        Ok(buf)
    }

    /// Flush framebuffer to screen.
    pub fn flush(&mut self) -> Result {
        // copy data from guest to host
        let rsp: CtrlHeader = self.request(TransferToHost2D {
            header: CtrlHeader::with_type(Command::TransferToHost2d),
            rect: self.rect,
            offset: 0,
            resource_id: RESOURCE_ID,
            padding: 0,
        })?;
        rsp.check_type(Command::OkNodata)?;

        // flush data to screen
        let rsp: CtrlHeader = self.request(ResourceFlush {
            header: CtrlHeader::with_type(Command::ResourceFlush),
            rect: self.rect,
            resource_id: RESOURCE_ID,
            padding: 0,
        })?;
        rsp.check_type(Command::OkNodata)?;

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
        while !self.control_queue.can_pop() {
            spin_loop();
        }
        self.control_queue.pop_used()?;
        Ok(unsafe { (self.queue_buf_recv.as_ptr() as *const Rsp).read() })
    }
}

#[repr(C)]
#[derive(Debug)]
struct Config {
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
const EVENT_DISPLAY: u32 = 1 << 0;

bitflags! {
    struct Features: u64 {
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
#[derive(Debug, PartialEq, Eq)]
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
struct CtrlHeader {
    hdr_type: Command,
    flags: u32,
    fence_id: u64,
    ctx_id: u32,
    padding: u32,
}

impl CtrlHeader {
    fn with_type(hdr_type: Command) -> CtrlHeader {
        CtrlHeader {
            hdr_type,
            flags: 0,
            fence_id: 0,
            ctx_id: 0,
            padding: 0,
        }
    }

    /// Return error if the type is not same as expected.
    fn check_type(&self, expected: Command) -> Result {
        if self.hdr_type == expected {
            Ok(())
        } else {
            Err(Error::IoError)
        }
    }
}

#[repr(C)]
#[derive(Debug, Copy, Clone, Default)]
struct Rect {
    x: u32,
    y: u32,
    width: u32,
    height: u32,
}

#[repr(C)]
#[derive(Debug)]
struct RespDisplayInfo {
    header: CtrlHeader,
    rect: Rect,
    enabled: u32,
    flags: u32,
}

#[repr(C)]
#[derive(Debug)]
struct ResourceCreate2D {
    header: CtrlHeader,
    resource_id: u32,
    format: Format,
    width: u32,
    height: u32,
}

#[repr(u32)]
#[derive(Debug)]
enum Format {
    B8G8R8A8UNORM = 1,
}

#[repr(C)]
#[derive(Debug)]
struct ResourceAttachBacking {
    header: CtrlHeader,
    resource_id: u32,
    nr_entries: u32, // always 1
    addr: u64,
    length: u32,
    padding: u32,
}

#[repr(C)]
#[derive(Debug)]
struct SetScanout {
    header: CtrlHeader,
    rect: Rect,
    scanout_id: u32,
    resource_id: u32,
}

#[repr(C)]
#[derive(Debug)]
struct TransferToHost2D {
    header: CtrlHeader,
    rect: Rect,
    offset: u64,
    resource_id: u32,
    padding: u32,
}

#[repr(C)]
#[derive(Debug)]
struct ResourceFlush {
    header: CtrlHeader,
    rect: Rect,
    resource_id: u32,
    padding: u32,
}

const QUEUE_TRANSMIT: usize = 0;
const QUEUE_CURSOR: usize = 1;

const RESOURCE_ID: u32 = 0xbabe;
