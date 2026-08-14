//! virgl 3D regression test for the virtio-gpu driver.
//!
//! Exercises the whole virgl command path: feature negotiation, capset query,
//! context create/destroy, 3D resource create, attach/detach, host transfers,
//! fenced command submission and blob resources. Runs only when the VIRGL
//! feature was negotiated — i.e. the host exposes a GL context (`make run
//! gl=on` with a GL-capable QEMU). On a plain 2D device the caller skips us.

use super::HalImpl;
use virtio_drivers::device::gpu::{GpuBox, VirtIOGpu};
use virtio_drivers::transport::Transport;
use virtio_drivers::{BufferDirection, Hal, PAGE_SIZE};

// ── pipe / virgl constants (from Gallium/virglrenderer headers) ──────────
/// Capset id for VIRGL (OpenGL).
const CAPSET_VIRGL: u32 = 1;
/// PIPE_TEXTURE_2D
const PIPE_TEXTURE_2D: u32 = 2;
/// PIPE_FORMAT_B8G8R8A8_UNORM
const PIPE_FORMAT_B8G8R8A8_UNORM: u32 = 1;
/// PIPE_BIND_RENDER_TARGET
const PIPE_BIND_RENDER_TARGET: u32 = 2;
/// VIRTIO_GPU_RESOURCE_FLAG_Y_0_TOP
const RESOURCE_FLAG_Y_0_TOP: u32 = 1;
/// VIRTIO_GPU_BLOB_MEM_GUEST — guest-backed blob (`resource_create_blob`).
///
/// We exercise the guest-backed path rather than `BLOB_MEM_HOST3D`: a HOST3D
/// blob requires the context to already contain a resource registered under
/// the given `blob_id` (virglrenderer `vrend_get_blob_pipe`), which is only
/// created by a preceding virgl `VIRGL_PIPE_RES_CREATE` submit — something
/// `resource_create_blob` alone cannot express. A GUEST blob is the API's
/// primary use and works with just a DMA region.
const BLOB_MEM_GUEST: u32 = 0x1;
/// VIRGL_CCMD_CREATE_OBJECT (enum `virgl_context_cmd`, value 1)
const VIRGL_CCMD_CREATE_OBJECT: u32 = 1;
/// VIRGL_CCMD_SET_FRAMEBUFFER_STATE (enum `virgl_context_cmd`, value 5)
const VIRGL_CCMD_SET_FRAMEBUFFER_STATE: u32 = 5;
/// VIRGL_CCMD_CLEAR (enum `virgl_context_cmd`, value 7)
const VIRGL_CCMD_CLEAR: u32 = 7;
/// VIRGL_OBJECT_SURFACE (enum `virgl_object_type`, value 8)
const VIRGL_OBJECT_SURFACE: u32 = 8;
/// PIPE_CLEAR_COLOR
const PIPE_CLEAR_COLOR: u32 = 0x1;

/// 256×256 render target.
const RESOURCE_ID: u32 = 100;
/// Surface handle bound to RESOURCE_ID as the framebuffer color attachment.
const SURFACE_ID: u32 = 200;
const WIDTH: u32 = 256;
const HEIGHT: u32 = 256;
/// B8G8R8A8 backing for the render target (WIDTH*HEIGHT*4 bytes).
const TRANSFER_SIZE: u32 = WIDTH * HEIGHT * 4;
/// Blob resource (guest-backed).
const RESOURCE_ID_BLOB: u32 = 101;
const BLOB_SIZE: usize = PAGE_SIZE;

/// Number of contiguous pages for `size` bytes.
const fn pages(size: usize) -> usize {
    (size + PAGE_SIZE - 1) / PAGE_SIZE
}

/// Build a virgl CLEAR command buffer (9 dwords = 36 bytes).
///
/// Wire format (little-endian, `len` counts the dwords *after* the header):
///   dword[0] = (len << 16) | VIRGL_CCMD_CLEAR   (len = 8)
///   dword[1] = buffers bitmask (1=color, 2=depth, 4=stencil)
///   dword[2..5] = RGBA clear color as f32
///   dword[6..7] = depth clear value as f64 (double)
///   dword[8] = stencil clear value as u32
fn build_clear_cmd(
    buffers: u32,
    r: f32,
    g: f32,
    b: f32,
    a: f32,
    depth: f64,
    stencil: u32,
) -> [u8; 36] {
    let mut cmd = [0u8; 36];
    cmd[0..4].copy_from_slice(&((8u32 << 16) | VIRGL_CCMD_CLEAR).to_le_bytes());
    cmd[4..8].copy_from_slice(&buffers.to_le_bytes());
    cmd[8..12].copy_from_slice(&r.to_bits().to_le_bytes());
    cmd[12..16].copy_from_slice(&g.to_bits().to_le_bytes());
    cmd[16..20].copy_from_slice(&b.to_bits().to_le_bytes());
    cmd[20..24].copy_from_slice(&a.to_bits().to_le_bytes());
    cmd[24..32].copy_from_slice(&depth.to_bits().to_le_bytes());
    cmd[32..36].copy_from_slice(&stencil.to_le_bytes());
    cmd
}

/// Build a render command stream (19 dwords = 76 bytes):
/// CREATE_OBJECT(surface) → SET_FRAMEBUFFER_STATE → CLEAR.
///
/// A bare CLEAR on a context with no bound surface fails in virglrenderer with
/// GL_INVALID_FRAMEBUFFER_OPERATION (`vrend_clear` runs `glClear` on the current
/// framebuffer), so the stream first creates a surface over the render target and
/// binds it as the single color attachment. Wire format per virgl_protocol.h
/// (`len` counts the dwords *after* the header, host advances `buf_offset += len+1`):
///   dword[0]  = (len=5 << 16) | (obj=SURFACE << 8) | cmd=CREATE_OBJECT
///   dword[1]  = surface handle
///   dword[2]  = res handle (the render target)
///   dword[3]  = format (PIPE_FORMAT_B8G8R8A8_UNORM)
///   dword[4]  = texture level
///   dword[5]  = layers (first=0, last=0 → 1 layer)
///   dword[6]  = (len=3 << 16) | cmd=SET_FRAMEBUFFER_STATE
///   dword[7]  = nr_cbufs = 1
///   dword[8]  = zsurf handle (0 = none)
///   dword[9]  = cbuf0 handle (the surface)
///   dword[10..18] = CLEAR (see `build_clear_cmd`)
fn build_render_cmd(
    buffers: u32,
    r: f32,
    g: f32,
    b: f32,
    a: f32,
    depth: f64,
    stencil: u32,
) -> [u8; 76] {
    let mut cmd = [0u8; 76];
    // ── CREATE_OBJECT surface (6 dwords) ──
    cmd[0..4].copy_from_slice(
        &((5u32 << 16) | (VIRGL_OBJECT_SURFACE << 8) | VIRGL_CCMD_CREATE_OBJECT).to_le_bytes(),
    );
    cmd[4..8].copy_from_slice(&SURFACE_ID.to_le_bytes());
    cmd[8..12].copy_from_slice(&RESOURCE_ID.to_le_bytes());
    cmd[12..16].copy_from_slice(&PIPE_FORMAT_B8G8R8A8_UNORM.to_le_bytes());
    cmd[16..20].copy_from_slice(&0u32.to_le_bytes());
    cmd[20..24].copy_from_slice(&0u32.to_le_bytes());
    // ── SET_FRAMEBUFFER_STATE (4 dwords) ──
    cmd[24..28].copy_from_slice(&((3u32 << 16) | VIRGL_CCMD_SET_FRAMEBUFFER_STATE).to_le_bytes());
    cmd[28..32].copy_from_slice(&1u32.to_le_bytes());
    cmd[32..36].copy_from_slice(&0u32.to_le_bytes());
    cmd[36..40].copy_from_slice(&SURFACE_ID.to_le_bytes());
    // ── CLEAR (9 dwords) ──
    cmd[40..76].copy_from_slice(&build_clear_cmd(buffers, r, g, b, a, depth, stencil));
    cmd
}

/// Run the virgl 3D regression tests. Panics on the first failing step.
pub fn run(gpu: &mut VirtIOGpu<HalImpl, impl Transport>) {
    // ── 01/15: VIRGL feature negotiated ──
    assert!(gpu.has_virgl(), "[VIRGL] 01/15 has_virgl() == false");
    info!("[VIRGL] 01/15 has_virgl OK");

    // ── 02/15: capset info ──
    let info = gpu
        .get_capset_info(0)
        .expect("[VIRGL] 02/15 get_capset_info(0) failed");
    assert_eq!(
        info.capset_id, CAPSET_VIRGL,
        "[VIRGL] 02/15 wrong capset id"
    );
    assert!(
        info.capset_max_version >= 1,
        "[VIRGL] 02/15 max_version < 1"
    );
    assert!(info.capset_max_size > 0, "[VIRGL] 02/15 max_size == 0");
    info!(
        "[VIRGL] 02/15 capset id={} max_ver={} max_size={}",
        info.capset_id, info.capset_max_version, info.capset_max_size
    );

    // ── 03/15: capset data ──
    let capset = gpu
        .get_capset(info.capset_id, 0, info.capset_max_size)
        .expect("[VIRGL] 03/15 get_capset failed");
    assert_eq!(
        capset.len(),
        info.capset_max_size as usize,
        "[VIRGL] 03/15 capset len != max_size"
    );
    info!("[VIRGL] 03/15 capset data {} bytes OK", capset.len());

    // ── 04/15: create context ──
    gpu.ctx_create(1, "virgl", CAPSET_VIRGL)
        .expect("[VIRGL] 04/15 ctx_create(1, \"virgl\") failed");
    info!("[VIRGL] 04/15 ctx_create OK");

    // ── 05/15: create a 256×256 render target ──
    gpu.resource_create_3d(
        1,
        RESOURCE_ID,
        PIPE_TEXTURE_2D,
        PIPE_FORMAT_B8G8R8A8_UNORM,
        PIPE_BIND_RENDER_TARGET,
        WIDTH,
        HEIGHT,
        1,
        1,
        0,
        0,
        RESOURCE_FLAG_Y_0_TOP,
    )
    .expect("[VIRGL] 05/15 resource_create_3d(100) failed");
    info!("[VIRGL] 05/15 resource_create_3d(100, 256×256 T2D RT) OK");

    // ── 06/15: attach resource to context ──
    gpu.ctx_attach_resource(1, RESOURCE_ID)
        .expect("[VIRGL] 06/15 ctx_attach_resource(1, 100) failed");
    info!("[VIRGL] 06/15 ctx_attach_resource OK");

    // ── 07/15: attach guest backing for the transfers ──
    // The host transfers only happen if the resource carries guest backing
    // (`res->iov` in virglrenderer) or the transfer itself supplies iovecs —
    // QEMU's virgl path does neither by itself, so without this step the
    // transfer commands are silently rejected with "Illegal resource".
    let (transfer_paddr, _transfer_vaddr) =
        HalImpl::dma_alloc(pages(TRANSFER_SIZE as usize), BufferDirection::Both, false);
    gpu.resource_attach_backing(RESOURCE_ID, transfer_paddr, TRANSFER_SIZE)
        .expect("[VIRGL] 07/15 resource_attach_backing(100) failed");
    info!("[VIRGL] 07/15 resource_attach_backing OK");

    // ── 08/15: upload into the resource ──
    gpu.transfer_to_host_3d(
        1,
        RESOURCE_ID,
        GpuBox {
            x: 0,
            y: 0,
            z: 0,
            w: WIDTH,
            h: HEIGHT,
            d: 1,
        },
        0,
        0,
        1024,
        0,
    )
    .expect("[VIRGL] 08/15 transfer_to_host_3d(100) failed");
    info!("[VIRGL] 08/15 transfer_to_host_3d OK");

    // ── 09/15: download command (host writes back into the same backing) ──
    gpu.transfer_from_host_3d(
        1,
        RESOURCE_ID,
        GpuBox {
            x: 0,
            y: 0,
            z: 0,
            w: WIDTH,
            h: HEIGHT,
            d: 1,
        },
        0,
        0,
        1024,
        0,
    )
    .expect("[VIRGL] 09/15 transfer_from_host_3d(100) failed");
    info!("[VIRGL] 09/15 transfer_from_host_3d OK");

    // ── 10/15: submit a fenced CLEAR against a bound surface ──
    let render_cmd = build_render_cmd(PIPE_CLEAR_COLOR, 0.2, 0.4, 0.6, 0.8, 1.0, 0);
    // The stream must be dword-aligned and length-consistent with each command
    // header: (5+1) + (3+1) + (8+1) = 19 dwords.
    assert_eq!(render_cmd.len(), 19 * 4, "[VIRGL] 10/15 render stream size");
    gpu.submit_3d(1, 1, &render_cmd)
        .expect("[VIRGL] 10/15 submit_3d(CREATE_SURFACE+FBO+CLEAR) failed");
    // The fence response is sent after the host flushes GL, so rendering is
    // done once `submit_3d` returns.
    info!("[VIRGL] 10/15 submit_3d(CREATE_SURFACE+FBO+CLEAR) OK");

    // ── 11/15: blob resource (feature-gated) ──
    if gpu.has_resource_blob() {
        let (blob_paddr, _blob_vaddr) =
            HalImpl::dma_alloc(pages(BLOB_SIZE), BufferDirection::Both, false);
        // SAFETY: `blob_paddr` is a dedicated DMA allocation that is valid
        // device-accessible memory, outlives the blob resource (nothing frees
        // it before the resource is unref'd), and is not aliased.
        unsafe {
            gpu.resource_create_blob(
                1,
                RESOURCE_ID_BLOB,
                BLOB_MEM_GUEST,
                0,
                BLOB_SIZE as u64,
                0,
                &[(blob_paddr, BLOB_SIZE)],
            )
            .expect("[VIRGL] 11/15 resource_create_blob(GUEST) failed");
        }
        gpu.resource_unref(RESOURCE_ID_BLOB)
            .expect("[VIRGL] 11/15 resource_unref(101) failed");
        info!("[VIRGL] 11/15 resource_create_blob(GUEST) OK");
    } else {
        info!("[VIRGL] 11/15 resource_create_blob SKIP (no RESOURCE_BLOB feature)");
    }

    // ── 12/15: detach from context ──
    gpu.ctx_detach_resource(1, RESOURCE_ID)
        .expect("[VIRGL] 12/15 ctx_detach_resource(1, 100) failed");
    info!("[VIRGL] 12/15 ctx_detach_resource OK");

    // ── 13/15: release the backing mapping ──
    gpu.resource_detach_backing(RESOURCE_ID)
        .expect("[VIRGL] 13/15 resource_detach_backing(100) failed");
    info!("[VIRGL] 13/15 resource_detach_backing OK");

    // ── 14/15: release resource ──
    gpu.resource_unref(RESOURCE_ID)
        .expect("[VIRGL] 14/15 resource_unref(100) failed");
    info!("[VIRGL] 14/15 resource_unref OK");

    // ── 15/15: destroy context ──
    gpu.ctx_destroy(1)
        .expect("[VIRGL] 15/15 ctx_destroy(1) failed");
    info!("[VIRGL] 15/15 ctx_destroy OK");

    info!("[VIRGL] === ALL 15 STEPS PASSED ===");
}
