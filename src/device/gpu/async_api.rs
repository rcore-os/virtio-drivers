//! Fire-and-forget entry points of [`VirtIOGpu`], plus the fence and
//! completion-monitoring API that goes with them.
//!
//! These are the asynchronous halves of the control commands whose blocking
//! versions live on the main type (see its [submission model](VirtIOGpu)
//! documentation): they enqueue and return immediately, deliver to the host at
//! the latest once 8 of them accumulate since the last kick (or when the ring
//! nears capacity, or when any blocking command or [`VirtIOGpu::wait_fence`]
//! runs), and report device-side errors via the log rather than their return
//! value. Consumers with a
//! transaction boundary should call [`VirtIOGpu::ctrl_notify`] at its end to
//! deliver each batch with a single kick — measurably faster than waiting for
//! the threshold, and what makes the numbers in this crate's benchmarks.

use super::{
    CmdCtxResource, CmdResourceCreate3D, CmdSubmit3D, Command, CtrlHeader, Format, Rect,
    ResourceAttachBacking, ResourceCreate2D, ResourceFlush, ResourceUnref, SetScanout,
    TransferToHost2D, VirtIOGpu,
};
use crate::{Result, hal::Hal, transport::Transport};

impl<H: Hal, T: Transport> VirtIOGpu<H, T> {
    /// Delivers all fire-and-forget control commands accumulated since the
    /// last kick with a single MMIO write — Linux `virtio_gpu_notify()` at the
    /// transaction boundary.
    ///
    /// Optional but recommended for latency: commands are *always* delivered
    /// at the latest once 8 of them have accumulated since the last kick (or
    /// when a synchronous command forces a kick), so consumers without a
    /// transaction boundary still work. Calling this once at the end of a
    /// batch (e.g. after an EXECBUFFER-style submit) delivers the batch
    /// immediately instead. Also called internally before cursor-queue
    /// commands, which run on a separate queue with no ordering relationship
    /// to the control queue (see `cursor_request`). No-op when nothing has
    /// accumulated.
    pub fn ctrl_notify(&mut self) {
        self.ctrl.notify(&mut self.transport);
    }

    /// Pop and reclaim every used control-queue entry currently available.
    ///
    /// Recycles the descriptors, advances the fence high-water mark, and logs
    /// device-side error responses. This is the counterpart of Linux's IRQ-driven
    /// `virtio_gpu_dequeue_ctrl_func`; call it from the IRQ handler and/or from the
    /// polling wait paths. Entries belonging to an in-flight synchronous request are
    /// left for their waiter.
    pub fn pump_completions(&mut self) -> Result {
        self.ctrl.pump_completions(&mut self.transport)
    }

    /// Block until the fence identified by `fence_id` (and everything enqueued before
    /// it) has been popped from the control queue. Implicit ordering: any entry
    /// completes all ≤ its id.
    ///
    /// Also delivers fire-and-forget commands accumulated since the last kick
    /// before waiting — the fenced entry itself may not have reached the host
    /// yet (below [`VirtIOGpu::ctrl_notify`]'s threshold, `enqueue` performs
    /// no kick on its own).
    pub fn wait_fence(&mut self, fence_id: u64) -> Result {
        self.ctrl.wait_fence(&mut self.transport, fence_id)
    }

    /// Non-blocking fence query: has `fence_id` (and everything enqueued before it)
    /// already been popped, i.e. has its virgl fence fired?
    ///
    /// Only reflects batches that have actually been delivered to the host; a
    /// consumer that only polls must ensure delivery itself (e.g.
    /// [`VirtIOGpu::ctrl_notify`] at the transaction boundary, or a
    /// [`VirtIOGpu::wait_fence`]). The high-water mark only advances when
    /// completed entries are popped, so without an IRQ handler calling
    /// [`VirtIOGpu::pump_completions`] the poll loop must call it itself. The
    /// counterpart of Linux `dma_resv_test_signaled` in the NOWAIT probe of
    /// `virtio_gpu_wait_ioctl` (virtgpu_ioctl.c).
    pub fn fence_completed(&self, fence_id: u64) -> bool {
        self.ctrl.fence_completed(fence_id)
    }

    /// Fire-and-forget variant of [`VirtIOGpu::resource_create_2d`]: returns as
    /// soon as the command is enqueued (see the [`super::VirtIOGpu`] submission-model docs). Device
    /// errors are logged, not returned.
    pub fn resource_create_2d_async(
        &mut self,
        resource_id: u32,
        width: u32,
        height: u32,
    ) -> Result {
        self.ctrl.enqueue(
            &mut self.transport,
            &ResourceCreate2D {
                header: CtrlHeader::with_type(Command::RESOURCE_CREATE_2D),
                resource_id,
                format: Format::B8G8R8A8UNORM,
                width,
                height,
            },
            None,
            0,
        )?;
        Ok(())
    }

    /// Fire-and-forget variant of [`VirtIOGpu::set_scanout`] (Linux
    /// `virtio_gpu_primary_plane_update` doesn't wait); see the
    /// [`super::VirtIOGpu`] submission-model docs for the ordering argument.
    /// Device errors are logged, not returned.
    pub fn set_scanout_async(&mut self, rect: Rect, scanout_id: u32, resource_id: u32) -> Result {
        self.ctrl.enqueue(
            &mut self.transport,
            &SetScanout {
                header: CtrlHeader::with_type(Command::SET_SCANOUT),
                rect,
                scanout_id,
                resource_id,
            },
            None,
            0,
        )?;
        Ok(())
    }

    /// Fire-and-forget variant of [`VirtIOGpu::resource_flush`]; see the
    /// [`super::VirtIOGpu`] submission-model docs for the ordering argument.
    /// Device errors are logged, not returned.
    pub fn resource_flush_async(&mut self, rect: Rect, resource_id: u32) -> Result {
        self.ctrl.enqueue(
            &mut self.transport,
            &ResourceFlush {
                header: CtrlHeader::with_type(Command::RESOURCE_FLUSH),
                rect,
                resource_id,
                _padding: 0,
            },
            None,
            0,
        )?;
        Ok(())
    }

    /// Fire-and-forget variant of [`VirtIOGpu::transfer_to_host_2d`]; see the
    /// [`super::VirtIOGpu`] submission-model docs for the ordering argument.
    /// Device errors are logged, not returned.
    pub fn transfer_to_host_2d_async(
        &mut self,
        rect: Rect,
        offset: u64,
        resource_id: u32,
    ) -> Result {
        self.ctrl.enqueue(
            &mut self.transport,
            &TransferToHost2D {
                header: CtrlHeader::with_type(Command::TRANSFER_TO_HOST_2D),
                rect,
                offset,
                resource_id,
                _padding: 0,
            },
            None,
            0,
        )?;
        Ok(())
    }

    /// Fire-and-forget variant of [`VirtIOGpu::resource_attach_backing`]; see
    /// the [`super::VirtIOGpu`] submission-model docs for the ordering argument. Device errors are
    /// logged, not returned.
    pub fn resource_attach_backing_async(
        &mut self,
        resource_id: u32,
        paddr: u64,
        length: u32,
    ) -> Result {
        self.ctrl.enqueue(
            &mut self.transport,
            &ResourceAttachBacking {
                header: CtrlHeader::with_type(Command::RESOURCE_ATTACH_BACKING),
                resource_id,
                nr_entries: 1,
                addr: paddr,
                length,
                _padding: 0,
            },
            None,
            0,
        )?;
        Ok(())
    }

    /// Fire-and-forget variant of [`VirtIOGpu::resource_unref`]; see the
    /// [`super::VirtIOGpu`] submission-model docs for the ordering argument.
    /// Device errors are logged, not returned.
    pub fn resource_unref_async(&mut self, resource_id: u32) -> Result {
        self.ctrl.enqueue(
            &mut self.transport,
            &ResourceUnref {
                header: CtrlHeader::with_type(Command::RESOURCE_UNREF),
                resource_id,
                _padding: 0,
            },
            None,
            0,
        )?;
        Ok(())
    }

    /// Fire-and-forget variant of [`VirtIOGpu::ctx_attach_resource`] (Linux
    /// `virtio_gpu_cmd_ctx_attach_resource` doesn't wait); see the
    /// [`super::VirtIOGpu`] submission-model docs for the ordering argument.
    /// Device errors are logged, not returned.
    pub fn ctx_attach_resource_async(&mut self, ctx_id: u32, resource_id: u32) -> Result {
        self.require_virgl()?;
        self.ctrl.enqueue(
            &mut self.transport,
            &CmdCtxResource {
                header: CtrlHeader::with_type_and_ctx(Command::CTX_ATTACH_RESOURCE, ctx_id),
                resource_id,
                _padding: 0,
            },
            None,
            0,
        )?;
        Ok(())
    }

    /// Fire-and-forget variant of [`super::VirtIOGpu::resource_create_3d`]
    /// (Linux `virtio_gpu_cmd_resource_create_3d` doesn't wait); see the
    /// [`super::VirtIOGpu`] submission-model docs for the ordering argument.
    /// Device errors are logged, not returned.
    #[allow(clippy::too_many_arguments)]
    pub fn resource_create_3d_async(
        &mut self,
        ctx_id: u32,
        resource_id: u32,
        target: u32,
        format: u32,
        bind: u32,
        width: u32,
        height: u32,
        depth: u32,
        array_size: u32,
        last_level: u32,
        nr_samples: u32,
        flags: u32,
    ) -> Result {
        self.require_virgl()?;
        self.ctrl.enqueue(
            &mut self.transport,
            &CmdResourceCreate3D {
                header: CtrlHeader::with_type_and_ctx(Command::RESOURCE_CREATE_3D, ctx_id),
                resource_id,
                target,
                format,
                bind,
                width,
                height,
                depth,
                array_size,
                last_level,
                nr_samples,
                flags,
                _padding: 0,
            },
            None,
            0,
        )?;
        Ok(())
    }

    /// Fire-and-forget variant of [`VirtIOGpu::submit_3d`]: returns as soon as
    /// the command stream is enqueued, not when rendering has finished.
    /// `fence_id` is recorded; block on [`VirtIOGpu::wait_fence`] (which also
    /// delivers the batch) or poll [`VirtIOGpu::fence_completed`] alongside
    /// [`VirtIOGpu::ctrl_notify`] before reading back anything the batch
    /// renders. The high-water mark only advances when completed entries are
    /// popped ([`VirtIOGpu::pump_completions`], from the IRQ handler or the
    /// poll loop itself), so a poll loop with neither spins forever. Mirrors
    /// Linux `virtio_gpu_cmd_submit` (enqueue-and-return).
    ///
    /// The command carries `VIRTIO_GPU_FLAG_FENCE`, so the host pops the used
    /// entry — and thus advances the fence high-water mark past `fence_id` —
    /// only when the virgl fence fires, i.e. after the host finished decoding
    /// and executing the batch (Linux fences every EXECBUFFER;
    /// `virtio_gpu_init_submit`, virtgpu_submit.c). Without the flag the
    /// used-pop would happen at decode+enqueue, making `wait_fence` report
    /// completion before rendering actually finished. Device errors are
    /// logged, not returned.
    pub fn submit_3d_async(&mut self, ctx_id: u32, fence_id: u64, cmds: &[u8]) -> Result {
        self.require_virgl()?;
        let req = CmdSubmit3D {
            header: CtrlHeader::with_fence(Command::SUBMIT_3D, ctx_id, fence_id),
            size: Self::submit_3d_size(cmds)?,
            _padding: 0,
        };
        // Fire-and-forget: the popped response is dropped (the fence is the
        // completion signal), and the command stream is copied into a heap box.
        self.ctrl
            .enqueue(&mut self.transport, &req, Some(cmds), fence_id)?;
        Ok(())
    }
}
