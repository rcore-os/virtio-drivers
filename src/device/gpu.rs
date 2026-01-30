//! Driver for VirtIO GPU devices.

use crate::config::{read_config, ReadOnly, WriteOnly};
use crate::hal::{BufferDirection, Dma, Hal};
use crate::queue::VirtQueue;
use crate::transport::{InterruptStatus, Transport};
use crate::{pages, Error, Result, PAGE_SIZE};
use alloc::boxed::Box;
use bitflags::bitflags;
use log::info;
use zerocopy::{FromBytes, FromZeros, Immutable, IntoBytes, KnownLayout};

const QUEUE_SIZE: u16 = 2;
const SUPPORTED_FEATURES: Features = Features::RING_EVENT_IDX
    .union(Features::RING_INDIRECT_DESC)
    .union(Features::VERSION_1)
    .union(Features::EDID);

/// A virtio based graphics adapter.
///
/// It can operate in 2D mode and in 3D (virgl) mode.
/// 3D mode will offload rendering ops to the host gpu and therefore requires
/// a gpu with 3D support on the host machine.
/// In 2D mode the virtio-gpu device provides support for ARGB Hardware cursors
/// and multiple scanouts (aka heads).
pub struct VirtIOGpu<H: Hal, T: Transport> {
    transport: T,
    rect: Option<Rect>,
    /// DMA area of frame buffer.
    frame_buffer_dma: Option<Dma<H>>,
    /// DMA area of cursor image buffer.
    cursor_buffer_dma: Option<Dma<H>>,
    /// Queue for sending control commands.
    control_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    /// Queue for sending cursor commands.
    cursor_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    /// Send buffer for queue.
    queue_buf_send: Box<[u8]>,
    /// Recv buffer for queue.
    queue_buf_recv: Box<[u8]>,
    /// Whether EDID feature was negotiated.
    has_edid: bool,
}

impl<H: Hal, T: Transport> VirtIOGpu<H, T> {
    /// Create a new VirtIO-Gpu driver.
    pub fn new(mut transport: T) -> Result<Self> {
        let negotiated_features = transport.begin_init(SUPPORTED_FEATURES);

        // read configuration space
        let events_read = read_config!(transport, Config, events_read)?;
        let num_scanouts = read_config!(transport, Config, num_scanouts)?;
        info!(
            "events_read: {:#x}, num_scanouts: {:#x}",
            events_read, num_scanouts
        );

        let control_queue = VirtQueue::new(
            &mut transport,
            QUEUE_TRANSMIT,
            negotiated_features.contains(Features::RING_INDIRECT_DESC),
            negotiated_features.contains(Features::RING_EVENT_IDX),
        )?;
        let cursor_queue = VirtQueue::new(
            &mut transport,
            QUEUE_CURSOR,
            negotiated_features.contains(Features::RING_INDIRECT_DESC),
            negotiated_features.contains(Features::RING_EVENT_IDX),
        )?;

        let queue_buf_send = FromZeros::new_box_zeroed_with_elems(PAGE_SIZE).unwrap();
        let queue_buf_recv = FromZeros::new_box_zeroed_with_elems(PAGE_SIZE).unwrap();

        transport.finish_init();

        let has_edid = negotiated_features.contains(Features::EDID);

        Ok(VirtIOGpu {
            transport,
            frame_buffer_dma: None,
            cursor_buffer_dma: None,
            rect: None,
            control_queue,
            cursor_queue,
            queue_buf_send,
            queue_buf_recv,
            has_edid,
        })
    }

    /// Acknowledge interrupt.
    pub fn ack_interrupt(&mut self) -> InterruptStatus {
        self.transport.ack_interrupt()
    }

    /// Get the resolution (width, height).
    pub fn resolution(&mut self) -> Result<(u32, u32)> {
        let display_info = self.get_display_info()?;
        Ok((display_info.rect.width, display_info.rect.height))
    }

    /// Get the EDID data for the specified scanout.
    ///
    /// Returns the EDID blob (up to 1024 bytes) and its actual size.
    /// Requires the EDID feature to have been negotiated.
    pub fn get_edid(&mut self, scanout: u32) -> Result<([u8; 1024], u32)> {
        if !self.has_edid {
            return Err(Error::Unsupported);
        }
        let rsp: RespEdid = self.request(CmdGetEdid {
            header: CtrlHeader::with_type(Command::GET_EDID),
            scanout,
            _padding: 0,
        })?;
        rsp.header.check_type(Command::OK_EDID)?;
        Ok((rsp.edid, rsp.size))
    }

    /// Get the preferred resolution from the EDID data.
    ///
    /// Parses the first Detailed Timing Descriptor in the EDID to extract
    /// the preferred display resolution. Returns (width, height).
    pub fn edid_preferred_resolution(&mut self) -> Result<(u32, u32)> {
        let (edid, size) = self.get_edid(SCANOUT_ID)?;
        parse_edid_preferred_resolution(&edid, size)
    }

    /// Get the list of supported resolutions from EDID data.
    ///
    /// Returns up to 8 resolutions from the Standard Timings block, sorted
    /// by total pixel count (largest first). Each entry is (width, height).
    pub fn edid_supported_resolutions(&mut self) -> Result<alloc::vec::Vec<(u32, u32)>> {
        let (edid, size) = self.get_edid(SCANOUT_ID)?;
        Ok(parse_edid_standard_timings(&edid, size))
    }

    /// Setup framebuffer
    pub fn setup_framebuffer(&mut self) -> Result<&mut [u8]> {
        // get display info
        let display_info = self.get_display_info()?;
        info!("=> {:?}", display_info);
        self.rect = Some(display_info.rect);

        // create resource 2d
        self.resource_create_2d(
            RESOURCE_ID_FB,
            display_info.rect.width,
            display_info.rect.height,
        )?;

        // alloc continuous pages for the frame buffer
        let size = display_info.rect.width * display_info.rect.height * 4;
        let frame_buffer_dma = Dma::new(pages(size as usize), BufferDirection::DriverToDevice)?;

        // resource_attach_backing
        self.resource_attach_backing(RESOURCE_ID_FB, frame_buffer_dma.paddr() as u64, size)?;

        // map frame buffer to screen
        self.set_scanout(display_info.rect, SCANOUT_ID, RESOURCE_ID_FB)?;

        // SAFETY: `Dma::new` guarantees that the pointer returned from
        // `raw_slice` is non-null, aligned, and the allocation is zeroed. We
        // store the `Dma` object in `self.frame_buffer_dma`, which prevents the
        // allocation from being freed while `self` exists. The returned ptr
        // borrows `self` mutably, which prevents other code from getting
        // another reference to `frame_buffer_dma` while the returned slice is
        // still in use.
        let buf = unsafe { frame_buffer_dma.raw_slice().as_mut() };
        self.frame_buffer_dma = Some(frame_buffer_dma);
        Ok(buf)
    }

    /// Setup framebuffer with an explicit resolution, ignoring the display info
    /// reported by the device. This is useful when the device reports a default
    /// resolution (e.g. 640x480 from UEFI firmware) but the caller wants a
    /// specific resolution.
    pub fn setup_framebuffer_with_resolution(
        &mut self,
        width: u32,
        height: u32,
    ) -> Result<&mut [u8]> {
        let rect = Rect {
            x: 0,
            y: 0,
            width,
            height,
        };
        self.rect = Some(rect);

        self.resource_create_2d(RESOURCE_ID_FB, width, height)?;

        let size = width * height * 4;
        let frame_buffer_dma = Dma::new(pages(size as usize), BufferDirection::DriverToDevice)?;

        self.resource_attach_backing(RESOURCE_ID_FB, frame_buffer_dma.paddr() as u64, size)?;
        self.set_scanout(rect, SCANOUT_ID, RESOURCE_ID_FB)?;

        let buf = unsafe { frame_buffer_dma.raw_slice().as_mut() };
        self.frame_buffer_dma = Some(frame_buffer_dma);
        Ok(buf)
    }

    /// Change the framebuffer resolution at runtime. Tears down the existing
    /// framebuffer resource and creates a new one at the specified dimensions.
    /// Returns a mutable slice to the new framebuffer memory.
    ///
    /// The old DMA allocation is freed after the new one is set up.
    pub fn change_resolution(&mut self, width: u32, height: u32) -> Result<&mut [u8]> {
        let rect = Rect {
            x: 0,
            y: 0,
            width,
            height,
        };

        // Disable scanout while we reconfigure
        self.set_scanout(Rect::default(), SCANOUT_ID, 0)?;

        // Detach and destroy old resource
        self.resource_detach_backing(RESOURCE_ID_FB)?;
        self.resource_unref(RESOURCE_ID_FB)?;

        // Drop old DMA allocation
        self.frame_buffer_dma = None;

        // Create new resource at new size
        self.rect = Some(rect);
        self.resource_create_2d(RESOURCE_ID_FB, width, height)?;

        let size = width * height * 4;
        let frame_buffer_dma = Dma::new(pages(size as usize), BufferDirection::DriverToDevice)?;

        self.resource_attach_backing(RESOURCE_ID_FB, frame_buffer_dma.paddr() as u64, size)?;
        self.set_scanout(rect, SCANOUT_ID, RESOURCE_ID_FB)?;

        let buf = unsafe { frame_buffer_dma.raw_slice().as_mut() };
        self.frame_buffer_dma = Some(frame_buffer_dma);
        Ok(buf)
    }

    /// Flush framebuffer to screen.
    pub fn flush(&mut self) -> Result {
        let rect = self.rect.ok_or(Error::NotReady)?;
        // copy data from guest to host
        self.transfer_to_host_2d(rect, 0, RESOURCE_ID_FB)?;
        // flush data to screen
        self.resource_flush(rect, RESOURCE_ID_FB)?;
        Ok(())
    }

    /// Set the pointer shape and position.
    pub fn setup_cursor(
        &mut self,
        cursor_image: &[u8],
        pos_x: u32,
        pos_y: u32,
        hot_x: u32,
        hot_y: u32,
    ) -> Result {
        let size = CURSOR_RECT.width * CURSOR_RECT.height * 4;
        if cursor_image.len() != size as usize {
            return Err(Error::InvalidParam);
        }
        let cursor_buffer_dma = Dma::new(pages(size as usize), BufferDirection::DriverToDevice)?;

        // SAFETY: `Dma::new` guarantees that the pointer returned from
        // `raw_slice` is non-null, aligned, and the allocation is zeroed. The
        // returned reference is only used within this function while
        // `cursor_buffer_dma` is alive.
        let buf = unsafe { cursor_buffer_dma.raw_slice().as_mut() };
        buf.copy_from_slice(cursor_image);

        self.resource_create_2d(RESOURCE_ID_CURSOR, CURSOR_RECT.width, CURSOR_RECT.height)?;
        self.resource_attach_backing(RESOURCE_ID_CURSOR, cursor_buffer_dma.paddr() as u64, size)?;
        self.transfer_to_host_2d(CURSOR_RECT, 0, RESOURCE_ID_CURSOR)?;
        self.update_cursor(
            RESOURCE_ID_CURSOR,
            SCANOUT_ID,
            pos_x,
            pos_y,
            hot_x,
            hot_y,
            false,
        )?;
        self.cursor_buffer_dma = Some(cursor_buffer_dma);
        Ok(())
    }

    /// Move the pointer without updating the shape.
    pub fn move_cursor(&mut self, pos_x: u32, pos_y: u32) -> Result {
        self.update_cursor(RESOURCE_ID_CURSOR, SCANOUT_ID, pos_x, pos_y, 0, 0, true)?;
        Ok(())
    }

    /// Send a request to the device and block for a response.
    fn request<Req: IntoBytes + Immutable, Rsp: FromBytes>(&mut self, req: Req) -> Result<Rsp> {
        req.write_to_prefix(&mut self.queue_buf_send).unwrap();
        self.control_queue.add_notify_wait_pop(
            &[&self.queue_buf_send],
            &mut [&mut self.queue_buf_recv],
            &mut self.transport,
        )?;
        Ok(Rsp::read_from_prefix(&self.queue_buf_recv).unwrap().0)
    }

    /// Send a mouse cursor operation request to the device and block for a response.
    fn cursor_request<Req: IntoBytes + Immutable>(&mut self, req: Req) -> Result {
        req.write_to_prefix(&mut self.queue_buf_send).unwrap();
        self.cursor_queue.add_notify_wait_pop(
            &[&self.queue_buf_send],
            &mut [],
            &mut self.transport,
        )?;
        Ok(())
    }

    fn get_display_info(&mut self) -> Result<RespDisplayInfo> {
        let info: RespDisplayInfo =
            self.request(CtrlHeader::with_type(Command::GET_DISPLAY_INFO))?;
        info.header.check_type(Command::OK_DISPLAY_INFO)?;
        Ok(info)
    }

    fn resource_create_2d(&mut self, resource_id: u32, width: u32, height: u32) -> Result {
        let rsp: CtrlHeader = self.request(ResourceCreate2D {
            header: CtrlHeader::with_type(Command::RESOURCE_CREATE_2D),
            resource_id,
            format: Format::B8G8R8A8UNORM,
            width,
            height,
        })?;
        rsp.check_type(Command::OK_NODATA)
    }

    fn set_scanout(&mut self, rect: Rect, scanout_id: u32, resource_id: u32) -> Result {
        let rsp: CtrlHeader = self.request(SetScanout {
            header: CtrlHeader::with_type(Command::SET_SCANOUT),
            rect,
            scanout_id,
            resource_id,
        })?;
        rsp.check_type(Command::OK_NODATA)
    }

    fn resource_flush(&mut self, rect: Rect, resource_id: u32) -> Result {
        let rsp: CtrlHeader = self.request(ResourceFlush {
            header: CtrlHeader::with_type(Command::RESOURCE_FLUSH),
            rect,
            resource_id,
            _padding: 0,
        })?;
        rsp.check_type(Command::OK_NODATA)
    }

    fn transfer_to_host_2d(&mut self, rect: Rect, offset: u64, resource_id: u32) -> Result {
        let rsp: CtrlHeader = self.request(TransferToHost2D {
            header: CtrlHeader::with_type(Command::TRANSFER_TO_HOST_2D),
            rect,
            offset,
            resource_id,
            _padding: 0,
        })?;
        rsp.check_type(Command::OK_NODATA)
    }

    fn resource_attach_backing(&mut self, resource_id: u32, paddr: u64, length: u32) -> Result {
        let rsp: CtrlHeader = self.request(ResourceAttachBacking {
            header: CtrlHeader::with_type(Command::RESOURCE_ATTACH_BACKING),
            resource_id,
            nr_entries: 1,
            addr: paddr,
            length,
            _padding: 0,
        })?;
        rsp.check_type(Command::OK_NODATA)
    }

    fn resource_detach_backing(&mut self, resource_id: u32) -> Result {
        let rsp: CtrlHeader = self.request(ResourceDetachBacking {
            header: CtrlHeader::with_type(Command::RESOURCE_DETACH_BACKING),
            resource_id,
            _padding: 0,
        })?;
        rsp.check_type(Command::OK_NODATA)
    }

    fn resource_unref(&mut self, resource_id: u32) -> Result {
        let rsp: CtrlHeader = self.request(ResourceUnref {
            header: CtrlHeader::with_type(Command::RESOURCE_UNREF),
            resource_id,
            _padding: 0,
        })?;
        rsp.check_type(Command::OK_NODATA)
    }

    fn update_cursor(
        &mut self,
        resource_id: u32,
        scanout_id: u32,
        pos_x: u32,
        pos_y: u32,
        hot_x: u32,
        hot_y: u32,
        is_move: bool,
    ) -> Result {
        self.cursor_request(UpdateCursor {
            header: if is_move {
                CtrlHeader::with_type(Command::MOVE_CURSOR)
            } else {
                CtrlHeader::with_type(Command::UPDATE_CURSOR)
            },
            pos: CursorPos {
                scanout_id,
                x: pos_x,
                y: pos_y,
                _padding: 0,
            },
            resource_id,
            hot_x,
            hot_y,
            _padding: 0,
        })
    }
}

impl<H: Hal, T: Transport> Drop for VirtIOGpu<H, T> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(QUEUE_TRANSMIT);
        self.transport.queue_unset(QUEUE_CURSOR);
    }
}

#[repr(C)]
struct Config {
    /// Signals pending events to the driver。
    events_read: ReadOnly<u32>,

    /// Clears pending events in the device.
    events_clear: WriteOnly<u32>,

    /// Specifies the maximum number of scanouts supported by the device.
    ///
    /// Minimum value is 1, maximum value is 16.
    num_scanouts: ReadOnly<u32>,
}

/// Display configuration has changed.
const EVENT_DISPLAY: u32 = 1 << 0;

bitflags! {
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
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

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
struct Command(u32);

impl Command {
    const GET_DISPLAY_INFO: Command = Command(0x100);
    const RESOURCE_CREATE_2D: Command = Command(0x101);
    const RESOURCE_UNREF: Command = Command(0x102);
    const SET_SCANOUT: Command = Command(0x103);
    const RESOURCE_FLUSH: Command = Command(0x104);
    const TRANSFER_TO_HOST_2D: Command = Command(0x105);
    const RESOURCE_ATTACH_BACKING: Command = Command(0x106);
    const RESOURCE_DETACH_BACKING: Command = Command(0x107);
    const GET_CAPSET_INFO: Command = Command(0x108);
    const GET_CAPSET: Command = Command(0x109);
    const GET_EDID: Command = Command(0x10a);

    const UPDATE_CURSOR: Command = Command(0x300);
    const MOVE_CURSOR: Command = Command(0x301);

    const OK_NODATA: Command = Command(0x1100);
    const OK_DISPLAY_INFO: Command = Command(0x1101);
    const OK_CAPSET_INFO: Command = Command(0x1102);
    const OK_CAPSET: Command = Command(0x1103);
    const OK_EDID: Command = Command(0x1104);

    const ERR_UNSPEC: Command = Command(0x1200);
    const ERR_OUT_OF_MEMORY: Command = Command(0x1201);
    const ERR_INVALID_SCANOUT_ID: Command = Command(0x1202);
}

const GPU_FLAG_FENCE: u32 = 1 << 0;

#[repr(C)]
#[derive(Debug, Clone, Copy, FromBytes, Immutable, IntoBytes, KnownLayout)]
struct CtrlHeader {
    hdr_type: Command,
    flags: u32,
    fence_id: u64,
    ctx_id: u32,
    _padding: u32,
}

impl CtrlHeader {
    fn with_type(hdr_type: Command) -> CtrlHeader {
        CtrlHeader {
            hdr_type,
            flags: 0,
            fence_id: 0,
            ctx_id: 0,
            _padding: 0,
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
#[derive(Debug, Copy, Clone, Default, FromBytes, Immutable, IntoBytes, KnownLayout)]
struct Rect {
    x: u32,
    y: u32,
    width: u32,
    height: u32,
}

#[repr(C)]
#[derive(Debug, FromBytes, Immutable, KnownLayout)]
struct RespDisplayInfo {
    header: CtrlHeader,
    rect: Rect,
    enabled: u32,
    flags: u32,
}

#[repr(C)]
#[derive(Debug, Immutable, IntoBytes, KnownLayout)]
struct CmdGetEdid {
    header: CtrlHeader,
    scanout: u32,
    _padding: u32,
}

#[repr(C)]
#[derive(Debug, FromBytes, Immutable, KnownLayout)]
struct RespEdid {
    header: CtrlHeader,
    size: u32,
    _padding: u32,
    edid: [u8; 1024],
}

#[repr(C)]
#[derive(Debug, Immutable, IntoBytes, KnownLayout)]
struct ResourceCreate2D {
    header: CtrlHeader,
    resource_id: u32,
    format: Format,
    width: u32,
    height: u32,
}

#[repr(u32)]
#[derive(Debug, Immutable, IntoBytes, KnownLayout)]
enum Format {
    B8G8R8A8UNORM = 1,
}

#[repr(C)]
#[derive(Debug, Immutable, IntoBytes, KnownLayout)]
struct ResourceAttachBacking {
    header: CtrlHeader,
    resource_id: u32,
    nr_entries: u32, // always 1
    addr: u64,
    length: u32,
    _padding: u32,
}

#[repr(C)]
#[derive(Debug, Immutable, IntoBytes, KnownLayout)]
struct ResourceDetachBacking {
    header: CtrlHeader,
    resource_id: u32,
    _padding: u32,
}

#[repr(C)]
#[derive(Debug, Immutable, IntoBytes, KnownLayout)]
struct ResourceUnref {
    header: CtrlHeader,
    resource_id: u32,
    _padding: u32,
}

#[repr(C)]
#[derive(Debug, Immutable, IntoBytes, KnownLayout)]
struct SetScanout {
    header: CtrlHeader,
    rect: Rect,
    scanout_id: u32,
    resource_id: u32,
}

#[repr(C)]
#[derive(Debug, Immutable, IntoBytes, KnownLayout)]
struct TransferToHost2D {
    header: CtrlHeader,
    rect: Rect,
    offset: u64,
    resource_id: u32,
    _padding: u32,
}

#[repr(C)]
#[derive(Debug, Immutable, IntoBytes, KnownLayout)]
struct ResourceFlush {
    header: CtrlHeader,
    rect: Rect,
    resource_id: u32,
    _padding: u32,
}

#[repr(C)]
#[derive(Copy, Clone, Debug, Immutable, IntoBytes, KnownLayout)]
struct CursorPos {
    scanout_id: u32,
    x: u32,
    y: u32,
    _padding: u32,
}

#[repr(C)]
#[derive(Copy, Clone, Debug, Immutable, IntoBytes, KnownLayout)]
struct UpdateCursor {
    header: CtrlHeader,
    pos: CursorPos,
    resource_id: u32,
    hot_x: u32,
    hot_y: u32,
    _padding: u32,
}

const QUEUE_TRANSMIT: u16 = 0;
const QUEUE_CURSOR: u16 = 1;

const SCANOUT_ID: u32 = 0;
const RESOURCE_ID_FB: u32 = 0xbabe;
const RESOURCE_ID_CURSOR: u32 = 0xdade;

const CURSOR_RECT: Rect = Rect {
    x: 0,
    y: 0,
    width: 64,
    height: 64,
};

/// Parse the preferred resolution from an EDID blob.
///
/// Extracts the width and height from the first Detailed Timing Descriptor
/// (bytes 54-71 of the base EDID block). Returns (width, height).
///
/// Reference: VESA Enhanced EDID Standard (E-EDID), Release A, Rev. 2,
/// Section 3.10.2 "Detailed Timing Definitions".
fn parse_edid_preferred_resolution(
    edid: &[u8; 1024],
    size: u32,
) -> core::result::Result<(u32, u32), Error> {
    if size < 128 {
        return Err(Error::IoError);
    }
    // First Detailed Timing Descriptor starts at byte 54 (0x36).
    // Horizontal active: lower 8 bits at byte 0x38, upper 4 bits at byte 0x3A high nibble.
    // Vertical active: lower 8 bits at byte 0x3B, upper 4 bits at byte 0x3D high nibble.
    let h_active = edid[0x38] as u32 | ((edid[0x3A] as u32 & 0xF0) << 4);
    let v_active = edid[0x3B] as u32 | ((edid[0x3D] as u32 & 0xF0) << 4);
    if h_active == 0 || v_active == 0 {
        return Err(Error::IoError);
    }
    Ok((h_active, v_active))
}

/// Parse the Standard Timings block from an EDID blob.
///
/// Returns a list of (width, height) pairs sorted by total pixel count
/// (largest first). EDID bytes 38-53 contain up to 8 standard timing entries,
/// each 2 bytes. Unused entries are marked as 0x0101.
///
/// Each entry encodes horizontal pixels as `(byte0 + 31) * 8` and the aspect
/// ratio in the top 2 bits of byte1: 0=16:10, 1=4:3, 2=5:4, 3=16:9.
///
/// Reference: VESA Enhanced EDID Standard (E-EDID), Release A, Rev. 2,
/// Section 3.9 "Standard Timing Identification".
fn parse_edid_standard_timings(edid: &[u8; 1024], size: u32) -> alloc::vec::Vec<(u32, u32)> {
    let mut resolutions = alloc::vec::Vec::new();
    if size < 128 {
        return resolutions;
    }
    for i in 0..8 {
        let b0 = edid[38 + i * 2];
        let b1 = edid[38 + i * 2 + 1];
        // 0x0101 = unused entry
        if b0 == 0x01 && b1 == 0x01 {
            continue;
        }
        let h_pixels = (b0 as u32 + 31) * 8;
        let aspect = (b1 >> 6) & 0x03;
        let v_pixels = match aspect {
            0 => h_pixels * 10 / 16, // 16:10
            1 => h_pixels * 3 / 4,   // 4:3
            2 => h_pixels * 4 / 5,   // 5:4
            3 => h_pixels * 9 / 16,  // 16:9
            _ => unreachable!(),
        };
        if h_pixels > 0 && v_pixels > 0 {
            resolutions.push((h_pixels, v_pixels));
        }
    }
    resolutions.sort_by(|a, b| (b.0 as u64 * b.1 as u64).cmp(&(a.0 as u64 * a.1 as u64)));
    resolutions
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a minimal 128-byte EDID with a Detailed Timing Descriptor
    /// encoding the given resolution.
    fn make_edid(width: u32, height: u32) -> [u8; 1024] {
        let mut edid = [0u8; 1024];
        // EDID header (bytes 0-7)
        edid[0] = 0x00;
        edid[1] = 0xFF;
        edid[2] = 0xFF;
        edid[3] = 0xFF;
        edid[4] = 0xFF;
        edid[5] = 0xFF;
        edid[6] = 0xFF;
        edid[7] = 0x00;

        // First Detailed Timing Descriptor at byte 54 (0x36)
        // Pixel clock must be non-zero for a valid DTD
        edid[0x36] = 0x01; // pixel clock low byte (non-zero)
        edid[0x37] = 0x00; // pixel clock high byte

        // Horizontal active: lower 8 bits at 0x38, upper 4 at high nibble of 0x3A
        edid[0x38] = (width & 0xFF) as u8;
        let h_blank: u32 = 0;
        edid[0x39] = (h_blank & 0xFF) as u8;
        edid[0x3A] = (((width >> 8) & 0x0F) << 4) as u8 | ((h_blank >> 8) & 0x0F) as u8;

        // Vertical active: lower 8 bits at 0x3B, upper 4 at high nibble of 0x3D
        edid[0x3B] = (height & 0xFF) as u8;
        let v_blank: u32 = 0;
        edid[0x3C] = (v_blank & 0xFF) as u8;
        edid[0x3D] = (((height >> 8) & 0x0F) << 4) as u8 | ((v_blank >> 8) & 0x0F) as u8;

        edid
    }

    #[test]
    fn parse_edid_1920x1080() {
        let edid = make_edid(1920, 1080);
        let (w, h) = parse_edid_preferred_resolution(&edid, 128).unwrap();
        assert_eq!(w, 1920);
        assert_eq!(h, 1080);
    }

    #[test]
    fn parse_edid_1280x800() {
        let edid = make_edid(1280, 800);
        let (w, h) = parse_edid_preferred_resolution(&edid, 128).unwrap();
        assert_eq!(w, 1280);
        assert_eq!(h, 800);
    }

    #[test]
    fn parse_edid_640x480() {
        let edid = make_edid(640, 480);
        let (w, h) = parse_edid_preferred_resolution(&edid, 128).unwrap();
        assert_eq!(w, 640);
        assert_eq!(h, 480);
    }

    #[test]
    fn parse_edid_2560x1440() {
        let edid = make_edid(2560, 1440);
        let (w, h) = parse_edid_preferred_resolution(&edid, 128).unwrap();
        assert_eq!(w, 2560);
        assert_eq!(h, 1440);
    }

    #[test]
    fn parse_edid_3840x2160() {
        let edid = make_edid(3840, 2160);
        let (w, h) = parse_edid_preferred_resolution(&edid, 128).unwrap();
        assert_eq!(w, 3840);
        assert_eq!(h, 2160);
    }

    #[test]
    fn parse_edid_too_short() {
        let edid = [0u8; 1024];
        assert!(parse_edid_preferred_resolution(&edid, 64).is_err());
    }

    #[test]
    fn parse_edid_zero_resolution() {
        let edid = make_edid(0, 0);
        assert!(parse_edid_preferred_resolution(&edid, 128).is_err());
    }

    #[test]
    fn parse_edid_zero_width() {
        let edid = make_edid(0, 1080);
        assert!(parse_edid_preferred_resolution(&edid, 128).is_err());
    }

    #[test]
    fn parse_edid_zero_height() {
        let edid = make_edid(1920, 0);
        assert!(parse_edid_preferred_resolution(&edid, 128).is_err());
    }

    /// Encode a standard timing entry: h_pixels and aspect ratio (0=16:10, 1=4:3, 2=5:4, 3=16:9).
    fn encode_standard_timing(h_pixels: u32, aspect: u8, refresh: u8) -> [u8; 2] {
        let b0 = (h_pixels / 8 - 31) as u8;
        let b1 = ((aspect & 0x03) << 6) | ((refresh - 60) & 0x3F);
        [b0, b1]
    }

    fn make_edid_with_standard_timings(timings: &[[u8; 2]]) -> [u8; 1024] {
        let mut edid = [0u8; 1024];
        // Valid EDID header
        edid[0] = 0x00;
        edid[1] = 0xFF;
        edid[2] = 0xFF;
        edid[3] = 0xFF;
        edid[4] = 0xFF;
        edid[5] = 0xFF;
        edid[6] = 0xFF;
        edid[7] = 0x00;
        // Fill standard timings (bytes 38-53), unused slots = 0x0101
        for i in 0..8 {
            if i < timings.len() {
                edid[38 + i * 2] = timings[i][0];
                edid[38 + i * 2 + 1] = timings[i][1];
            } else {
                edid[38 + i * 2] = 0x01;
                edid[38 + i * 2 + 1] = 0x01;
            }
        }
        edid
    }

    #[test]
    fn standard_timings_parses_1920x1080() {
        let timings = [encode_standard_timing(1920, 3, 60)]; // 16:9
        let edid = make_edid_with_standard_timings(&timings);
        let res = parse_edid_standard_timings(&edid, 128);
        assert_eq!(res, vec![(1920, 1080)]);
    }

    #[test]
    fn standard_timings_parses_multiple_sorted_by_size() {
        let timings = [
            encode_standard_timing(1280, 1, 60), // 4:3 → 1280x960
            encode_standard_timing(1920, 3, 60), // 16:9 → 1920x1080
            encode_standard_timing(640, 1, 60),  // 4:3 → 640x480
        ];
        let edid = make_edid_with_standard_timings(&timings);
        let res = parse_edid_standard_timings(&edid, 128);
        assert_eq!(res, vec![(1920, 1080), (1280, 960), (640, 480)]);
    }

    #[test]
    fn standard_timings_skips_unused_entries() {
        let timings = [
            encode_standard_timing(1920, 3, 60),
            [0x01, 0x01], // unused
            encode_standard_timing(1280, 1, 60),
        ];
        let edid = make_edid_with_standard_timings(&timings);
        let res = parse_edid_standard_timings(&edid, 128);
        assert_eq!(res, vec![(1920, 1080), (1280, 960)]);
    }

    #[test]
    fn standard_timings_all_unused() {
        let edid = make_edid_with_standard_timings(&[]);
        let res = parse_edid_standard_timings(&edid, 128);
        assert!(res.is_empty());
    }

    #[test]
    fn standard_timings_too_short_edid() {
        let edid = [0u8; 1024];
        let res = parse_edid_standard_timings(&edid, 64);
        assert!(res.is_empty());
    }

    #[test]
    fn standard_timings_aspect_ratios() {
        let timings = [
            encode_standard_timing(1920, 0, 60), // 16:10 → 1920x1200
            encode_standard_timing(1920, 1, 60), // 4:3 → 1920x1440
            encode_standard_timing(1280, 2, 60), // 5:4 → 1280x1024
            encode_standard_timing(1920, 3, 60), // 16:9 → 1920x1080
        ];
        let edid = make_edid_with_standard_timings(&timings);
        let res = parse_edid_standard_timings(&edid, 128);
        // Sorted by pixel count: 1920x1440, 1920x1200, 1920x1080, 1280x1024
        assert_eq!(
            res,
            vec![(1920, 1440), (1920, 1200), (1920, 1080), (1280, 1024)]
        );
    }
}
