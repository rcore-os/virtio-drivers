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

    /// Set or change the framebuffer resolution. If a framebuffer already exists,
    /// tears down the existing resource before creating the new one. Can be called
    /// before or after [`setup_framebuffer`] to set an explicit resolution.
    /// Returns a mutable slice to the new framebuffer memory.
    pub fn change_resolution(&mut self, width: u32, height: u32) -> Result<&mut [u8]> {
        let rect = Rect {
            x: 0,
            y: 0,
            width,
            height,
        };

        // Tear down existing framebuffer if one exists
        if self.frame_buffer_dma.is_some() {
            self.set_scanout(Rect::default(), SCANOUT_ID, 0)?;
            self.resource_detach_backing(RESOURCE_ID_FB)?;
            self.resource_unref(RESOURCE_ID_FB)?;
            self.frame_buffer_dma = None;
        }

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

    /// Real EDID captured from QEMU virtio-GPU with `-device virtio-gpu,xres=1920,yres=1080`.
    /// QEMU generates this EDID dynamically. The base block (bytes 0-127) contains:
    /// - Manufacturer: "RHT" (Red Hat), product code 0x1234
    /// - DTD1 preferred mode: 1920x1080 @ 60Hz
    /// - 8 Standard Timings: 2048x1152, 1920x1080, 1920x1200, 1600x1200,
    ///   1680x1050, 1440x900, 1280x1024, 1280x960
    /// - CEA extension block (bytes 128-255) with SVDs for additional modes
    /// Remaining bytes (256-1023) are zero-padded by the virtio-GPU device.
    fn qemu_edid() -> [u8; 1024] {
        let mut edid = [0u8; 1024];
        let data: [u8; 256] = [
            // Base EDID block (128 bytes)
            0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x49, 0x14, 0x34, 0x12, 0x00, 0x00,
            0x00, 0x00, 0x2a, 0x18, 0x01, 0x04, 0xa5, 0x30, 0x1b, 0x78, 0x06, 0xee, 0x91, 0xa3,
            0x54, 0x4c, 0x99, 0x26, 0x0f, 0x50, 0x54, 0x21, 0x08, 0x00, 0xe1, 0xc0, 0xd1, 0xc0,
            0xd1, 0x00, 0xa9, 0x40, 0xb3, 0x00, 0x95, 0x00, 0x81, 0x80, 0x81, 0x40, 0xd2, 0x54,
            0x80, 0xa0, 0x72, 0x38, 0x25, 0x40, 0xe0, 0x39, 0x55, 0x40, 0xe7, 0x12, 0x11, 0x00,
            0x00, 0x18, 0x00, 0x00, 0x00, 0xf7, 0x00, 0x0a, 0x00, 0x40, 0x82, 0x00, 0x28, 0x20,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xfd, 0x00, 0x32, 0x7d, 0x1e,
            0xa0, 0xff, 0x01, 0x0a, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x00, 0x00, 0x00, 0xfc,
            0x00, 0x51, 0x45, 0x4d, 0x55, 0x20, 0x4d, 0x6f, 0x6e, 0x69, 0x74, 0x6f, 0x72, 0x0a,
            0x01, 0xb0, // CEA extension block (128 bytes)
            0x02, 0x03, 0x0b, 0x00, 0x46, 0x7d, 0x65, 0x60, 0x59, 0x1f, 0x61, 0x00, 0x00, 0x00,
            0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x2f,
        ];
        edid[..256].copy_from_slice(&data);
        edid
    }

    #[test]
    fn qemu_edid_preferred_resolution() {
        let edid = qemu_edid();
        let (w, h) = parse_edid_preferred_resolution(&edid, 256).unwrap();
        assert_eq!((w, h), (1920, 1080));
    }

    #[test]
    fn qemu_edid_standard_timings() {
        let edid = qemu_edid();
        let res = parse_edid_standard_timings(&edid, 256);
        // QEMU advertises 8 standard timings, sorted by total pixel count (largest first).
        // Note: 1600x1200 (1,920,000 px) > 1680x1050 (1,764,000 px) despite narrower width,
        // and 1280x1024 (1,310,720 px) > 1440x900 (1,296,000 px) for the same reason.
        assert_eq!(
            res,
            vec![
                (2048, 1152), // 16:9,  2,359,296 px
                (1920, 1200), // 16:10, 2,304,000 px
                (1920, 1080), // 16:9,  2,073,600 px
                (1600, 1200), // 4:3,   1,920,000 px
                (1680, 1050), // 16:10, 1,764,000 px
                (1280, 1024), // 5:4,   1,310,720 px
                (1440, 900),  // 16:10, 1,296,000 px
                (1280, 960),  // 4:3,   1,228,800 px
            ]
        );
    }

    #[test]
    fn qemu_edid_highest_resolution_is_2048x1152() {
        let edid = qemu_edid();
        let res = parse_edid_standard_timings(&edid, 256);
        assert_eq!(res.first(), Some(&(2048, 1152)));
    }

    #[test]
    fn preferred_resolution_too_short() {
        let edid = [0u8; 1024];
        assert!(parse_edid_preferred_resolution(&edid, 64).is_err());
    }

    #[test]
    fn preferred_resolution_zeroed_active_pixels() {
        // Zero out horizontal and vertical active pixels in DTD1
        let mut edid = qemu_edid();
        edid[0x38] = 0x00; // h_active low
        edid[0x3A] &= 0x0F; // h_active high nibble = 0
        edid[0x3B] = 0x00; // v_active low
        edid[0x3D] &= 0x0F; // v_active high nibble = 0
        assert!(parse_edid_preferred_resolution(&edid, 256).is_err());
    }

    #[test]
    fn standard_timings_too_short() {
        let edid = [0u8; 1024];
        let res = parse_edid_standard_timings(&edid, 32);
        assert!(res.is_empty());
    }

    #[test]
    fn standard_timings_all_unused() {
        // Overwrite all standard timing slots with 0x0101 (unused marker)
        let mut edid = qemu_edid();
        for i in 0..8 {
            edid[38 + i * 2] = 0x01;
            edid[38 + i * 2 + 1] = 0x01;
        }
        let res = parse_edid_standard_timings(&edid, 256);
        assert!(res.is_empty());
    }

    #[test]
    fn standard_timings_partial_entries() {
        // Keep only the first two standard timing entries, mark rest unused
        let mut edid = qemu_edid();
        for i in 2..8 {
            edid[38 + i * 2] = 0x01;
            edid[38 + i * 2 + 1] = 0x01;
        }
        let res = parse_edid_standard_timings(&edid, 256);
        // First two entries from QEMU: 2048x1152 (16:9) and 1920x1080 (16:9)
        assert_eq!(res, vec![(2048, 1152), (1920, 1080)]);
    }
}
