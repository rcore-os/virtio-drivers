//! Asynchronous control-queue submission machinery for the GPU device.
//!
//! Implements the Linux virtio_gpu submission model on top of a plain
//! split-ring virtqueue:
//!
//! - **Fire-and-forget commands** ([`ControlQueue::enqueue`]) are added to the
//!   ring and return immediately. Strict virtqueue ordering guarantees the
//!   host applies them in submission order, so create → attach-backing →
//!   transfer → flush → scanout sequences need no per-command fence. Device
//!   error responses are logged by [`ControlQueue::pump_completions`] but not
//!   returned to the caller — commands that must observe the device's answer
//!   go through [`ControlQueue::request_sync`] instead.
//! - **Bounded-deferral delivery**: commands are delivered to the host at the
//!   latest after [`KICK_THRESHOLD`] enqueues, when the ring nears capacity,
//!   or when a synchronous request or [`ControlQueue::wait_fence`] forces a
//!   kick — every command reaches the host without any caller-side batching
//!   contract (unlike Linux, which
//!   defers its kick to the DRM ioctl boundary via `virtio_gpu_notify`, a
//!   boundary this no-std crate cannot assume exists). Consumers that *do*
//!   have a transaction boundary should call [`ControlQueue::notify`] there:
//!   it delivers the accumulated batch with a single kick immediately, which
//!   measurably beats waiting for the threshold (one MMIO write and one host
//!   wakeup per transaction instead of per threshold window).
//! - **Bounded memory**: command/response bytes live in preallocated,
//!   address-stable vbuf slots — the fork's equivalent of Linux's
//!   `virtio_gpu_vbuf` slab (`kmem_cache`), one slot per ring entry plus the
//!   parking-FIFO cap — so a host that drains slower than the guest produces
//!   cannot grow guest-side buffering without bound.

use super::{Command, CtrlHeader, QUEUE_TRANSMIT};
use crate::{Error, Result, hal::Hal, queue::VirtQueue, transport::Transport};
use alloc::{boxed::Box, collections::VecDeque, vec, vec::Vec};
use core::hint::spin_loop;
use core::mem::size_of;
use zerocopy::{FromBytes, Immutable, IntoBytes};

/// Number of descriptors on the control virtqueue.
///
/// With `RING_INDIRECT_DESC` a whole command collapses into one queue slot, so
/// this is effectively the number of commands that can be in flight at once.
/// 64 matches what QEMU advertises for the control queue (Linux also uses the
/// device-negotiated size).
pub(crate) const CTRL_QUEUE_SIZE: u16 = 64;
/// Cap for the parking FIFO ([`ControlQueue::pending_commands`]). Above this
/// the driver degrades to the bounded wait, so a host that drains far slower
/// than the guest produces cannot grow guest-side buffering without bound.
const PENDING_FIFO_CAP: usize = 128;
/// Maximum inline size of an async control-command buffer, mirroring Linux
/// `MAX_INLINE_CMD_SIZE` (virtgpu_vq.c): the largest control command is
/// `CmdCtxCreate` at 96 bytes, and every command submitted fire-and-forget
/// (create/attach/transfer/flush/scanout/unref/submit_3d) fits well within it.
const INLINE_CMD_SIZE: usize = 96;
/// Number of fire-and-forget commands that may accumulate in the avail ring
/// before the driver kicks the host unconditionally. Consumers that call
/// [`ControlQueue::notify`] at their transaction boundary drain the
/// accumulator early (typical transactions hold only a few commands), so the
/// threshold never fires for them; consumers that never call it still get
/// every command delivered, at the latest after this many enqueues.
const KICK_THRESHOLD: u32 = 8;
const RESP_SIZE: usize = size_of::<CtrlHeader>();
/// Maximum number of live fire-and-forget commands: one per control-queue
/// slot plus the parking-FIFO cap. Bounds the vbuf arenas below.
const MAX_INFLIGHT: usize = CTRL_QUEUE_SIZE as usize + PENDING_FIFO_CAP;

/// A fire-and-forget command in flight on the control queue (or parked while
/// the queue is full): a reference to its vbuf-arena slot plus the metadata
/// that only the driver cares about.
struct PendingSubmit {
    /// Index into the vbuf arenas holding this command's bytes.
    slot: usize,
    /// Number of valid bytes in this command's `vbuf_cmds[slot]`.
    cmd_len: usize,
    /// Optional extra device-readable payload (e.g. the virgl command stream).
    /// Heap-allocated (stable address) — Linux `vmemdup_user`s this too.
    data: Option<Box<[u8]>>,
    /// Monotonic fence id assigned by the upper layer (SUBMIT_3D only).
    fence_id: u64,
}

/// The GPU control queue: a [`VirtQueue`] plus the state needed to run it in
/// the Linux async style (in-flight tracking, parking FIFO, kick suppression,
/// fence bookkeeping). See the [module docs](self) for the model.
///
/// The command/response bytes live in two parallel boxed arenas
/// ([`ControlQueue::vbuf_cmds`] / [`ControlQueue::vbuf_resps`]) that never
/// move, because the device DMAs from these addresses at arbitrary later
/// times: storing the bytes inline in a `PendingSubmit` that later gets moved
/// (into `pending[token]` or the parking FIFO) would leave the descriptors
/// pointing at a dead stack frame. Only the slot's *index* travels around the
/// driver; the bytes stay put until the used entry is popped.
pub(crate) struct ControlQueue<H: Hal> {
    queue: VirtQueue<H, { CTRL_QUEUE_SIZE as usize }>,
    /// Stable-address arena of command bytes, one slot per possible in-flight
    /// or parked command.
    vbuf_cmds: Box<[[u8; INLINE_CMD_SIZE]]>,
    /// Parallel arena of device-writable response buffers, indexed like
    /// [`ControlQueue::vbuf_cmds`] (kept separate so `add_pending` can borrow
    /// command and response from `self` simultaneously).
    vbuf_resps: Box<[[u8; RESP_SIZE]]>,
    /// Indices of unused vbuf slots (a set, not a queue — any free slot works,
    /// no ordering requirement on buffer storage).
    vbuf_free: Vec<usize>,
    /// In-flight commands, keyed by descriptor token. `add` always returns a
    /// token in `0..CTRL_QUEUE_SIZE` (the free-list head is a descriptor table
    /// index), so the token can index this array directly.
    pending: [Option<PendingSubmit>; CTRL_QUEUE_SIZE as usize],
    /// Fire-and-forget commands parked while the ring is full. Re-added
    /// in-order by [`ControlQueue::flush_pending`], which runs from the next
    /// enqueue, from [`ControlQueue::pump_completions`], and therefore also
    /// from the consumer's IRQ path.
    pending_commands: VecDeque<PendingSubmit>,
    /// Number of fire-and-forget commands enqueued since the last kick
    /// decision (Linux `pending_commands` in `virtgpu_vq.c`). Capped at
    /// [`KICK_THRESHOLD`].
    ctrl_pending: u32,
    /// Highest fence id whose completion has been observed (implicit ordering:
    /// fence N done ⇒ all ≤ N done).
    ///
    /// INVARIANT: every path that pops a fenced entry must advance this
    /// counter — [`ControlQueue::pump_completions`] for `*_async` entries and
    /// [`ControlQueue::request_sync_fenced`] for blocking `submit_3d` —
    /// otherwise `wait_fence` deadlocks on an already-fired fence.
    completed_fence_id: u64,
}

impl<H: Hal> ControlQueue<H> {
    /// Creates the control queue on the given transport.
    pub(crate) fn new(
        transport: &mut impl Transport,
        indirect: bool,
        event_idx: bool,
        access_platform: bool,
    ) -> Result<Self> {
        let queue = VirtQueue::new(
            transport,
            QUEUE_TRANSMIT,
            indirect,
            event_idx,
            access_platform,
        )?;
        Ok(Self {
            queue,
            vbuf_cmds: vec![[0; INLINE_CMD_SIZE]; MAX_INFLIGHT].into_boxed_slice(),
            vbuf_resps: vec![[0; RESP_SIZE]; MAX_INFLIGHT].into_boxed_slice(),
            vbuf_free: (0..MAX_INFLIGHT).collect(),
            pending: [const { None }; { CTRL_QUEUE_SIZE as usize }],
            pending_commands: VecDeque::new(),
            ctrl_pending: 0,
            completed_fence_id: 0,
        })
    }

    /// Enqueues a fire-and-forget control command and returns its queue token
    /// immediately, without waiting for the device.
    ///
    /// The request bytes (`req`) and optional second device-readable payload
    /// (`data`) are copied into a vbuf slot (plus a heap box for a large
    /// payload), because the device may DMA from them long after this call
    /// returns and no caller stack survives to hold them.
    ///
    /// If the ring is full, finished entries are reclaimed once and the command
    /// is retried; if it still doesn't fit it parks in `pending_commands` and
    /// `Ok(None)` is returned — a submit never blocks on host drain (the Linux
    /// model). Parked commands are re-added in order by
    /// [`ControlQueue::flush_pending`]. Only if all vbuf slots are live (ring
    /// full *and* FIFO at cap) does the caller degrade to the bounded wait,
    /// same as [`ControlQueue::request_sync`]: every reclaimed entry returns
    /// one slot, so the wait always makes progress.
    ///
    /// Returns the queue token (`0..CTRL_QUEUE_SIZE`) for an enqueued command,
    /// or `None` if it was parked. Callers must not wait on a parked command.
    pub(crate) fn enqueue<Req: IntoBytes + Immutable>(
        &mut self,
        transport: &mut impl Transport,
        req: &Req,
        data: Option<&[u8]>,
        fence_id: u64,
    ) -> Result<Option<u16>> {
        // Put any parked commands onto the virtqueue first, so strict
        // submission order is preserved relative to this command.
        self.flush_pending(transport)?;

        let cmd_bytes = req.as_bytes();
        if cmd_bytes.len() > INLINE_CMD_SIZE {
            return Err(Error::InvalidParam);
        }
        // At most one `PendingSubmit` is created per call (each loop iteration
        // either reuses `held` or returns), so the payload box is moved, not
        // cloned — for SUBMIT_3D it can be hundreds of kilobytes.
        let mut data: Option<Box<[u8]>> = data.map(<[u8]>::to_vec).map(Vec::into_boxed_slice);

        // Acquire a stable-address slot and a ring slot; both are guaranteed to
        // be returned by pops (each reclaimed entry frees exactly one of
        // each), so pump + wait always makes progress.
        let mut held: Option<PendingSubmit> = None;
        loop {
            let mut entry = match held.take() {
                Some(entry) => entry,
                None => {
                    let Some(slot) = self.vbuf_free.pop() else {
                        // All slots live: ring full AND FIFO at cap. Degrade to
                        // the bounded wait, same as the sync path.
                        self.pump_completions(transport)?;
                        spin_loop();
                        continue;
                    };
                    self.vbuf_cmds[slot][..cmd_bytes.len()].copy_from_slice(cmd_bytes);
                    self.vbuf_resps[slot] = [0; RESP_SIZE];
                    PendingSubmit {
                        slot,
                        cmd_len: cmd_bytes.len(),
                        data: data.take(),
                        fence_id,
                    }
                }
            };

            match self.add_pending(&mut entry) {
                Ok(token) => {
                    self.account_enqueued(transport);
                    self.pending[token as usize] = Some(entry);
                    return Ok(Some(token));
                }
                Err(Error::QueueFull) => {
                    // Never busy-spin on host drain: reclaim finished entries,
                    // try once more, then park the owned command in the FIFO
                    // and return.
                    self.pump_completions(transport)?;
                    match self.add_pending(&mut entry) {
                        Ok(token) => {
                            self.account_enqueued(transport);
                            self.pending[token as usize] = Some(entry);
                            return Ok(Some(token));
                        }
                        Err(Error::QueueFull) if self.pending_commands.len() < PENDING_FIFO_CAP => {
                            self.pending_commands.push_back(entry);
                            return Ok(None);
                        }
                        Err(Error::QueueFull) => {
                            // FIFO at cap too: hold the slot and wait for the
                            // host to drain, then retry with the same entry.
                            held = Some(entry);
                            spin_loop();
                        }
                        Err(e) => {
                            self.vbuf_free.push(entry.slot);
                            return Err(e);
                        }
                    }
                }
                Err(e) => {
                    self.vbuf_free.push(entry.slot);
                    return Err(e);
                }
            }
        }
    }

    /// Synchronous, zero-copy control request: adds the caller's borrowed
    /// buffers to the control queue, kicks, waits for the used entry, and pops
    /// it back into the same buffers, which live in the caller's stack frame
    /// across the entire call.
    ///
    /// Parked commands are flushed first and earlier in-flight entries are
    /// drained while waiting, so strict submission order is preserved
    /// end-to-end: the used ring is FIFO, so this command's entry completes
    /// only after every older one.
    ///
    /// The wait busy-polls with `spin_loop`, exactly as upstream
    /// `add_notify_wait_pop` does.
    pub(crate) fn request_sync<'a: 'b, 'b>(
        &mut self,
        transport: &mut impl Transport,
        inputs: &'a [&'b [u8]],
        outputs: &'a mut [&'b mut [u8]],
    ) -> Result<u32> {
        let token = self.add_sync(transport, inputs, outputs)?;
        self.wait_sync(token, transport, inputs, outputs)
    }

    /// Like [`Self::request_sync`], but also records `fence_id` as observed
    /// once the response has been popped. Used by the blocking `submit_3d`,
    /// whose `VIRTIO_GPU_FLAG_FENCE` response the host writes only after
    /// rendering finished — popping it *is* the fence observation, and a
    /// subsequent `wait_fence`/`fence_completed` must immediately see it.
    pub(crate) fn request_sync_fenced<'a: 'b, 'b>(
        &mut self,
        transport: &mut impl Transport,
        inputs: &'a [&'b [u8]],
        outputs: &'a mut [&'b mut [u8]],
        fence_id: u64,
    ) -> Result<u32> {
        let used_len = self.request_sync(transport, inputs, outputs)?;
        if fence_id > self.completed_fence_id {
            self.completed_fence_id = fence_id;
        }
        Ok(used_len)
    }

    /// Adds a synchronous request's buffers and kicks the host exactly as
    /// upstream `add_notify_wait_pop` does: notify only when the device has not
    /// suppressed kicks (`should_notify` ≡ `virtqueue_kick_prepare`; with
    /// event-index the host is only asked when it is waiting). If the host is
    /// still draining earlier commands it will reach this one without a kick —
    /// the standard virtio no-lost-wakeup protocol covers it.
    fn add_sync<'a, 'b>(
        &mut self,
        transport: &mut impl Transport,
        inputs: &'a [&'b [u8]],
        outputs: &'a mut [&'b mut [u8]],
    ) -> Result<u16> {
        self.flush_pending(transport)?;

        let token = loop {
            // SAFETY: the borrowed buffers live in the caller's frame until the
            // matching `pop_used` in `wait_sync`, exactly as
            // `add_notify_wait_pop` requires.
            match unsafe { self.queue.add(inputs, outputs) } {
                Ok(t) => break t,
                Err(Error::QueueFull) => {
                    // The ring is full of commands the host has not drained
                    // yet: kick so it makes progress, reclaim finished entries
                    // and retry. Bounded, like the old blocking behaviour.
                    transport.notify(QUEUE_TRANSMIT);
                    self.pump_completions(transport)?;
                    spin_loop();
                }
                Err(e) => return Err(e),
            }
        };

        if self.queue.should_notify() {
            transport.notify(QUEUE_TRANSMIT);
        }
        Ok(token)
    }

    /// Waits until the synchronous request `token` is at the head of the used
    /// ring, then pops it back into the caller's buffers.
    fn wait_sync<'a: 'b, 'b>(
        &mut self,
        token: u16,
        transport: &mut impl Transport,
        inputs: &'a [&'b [u8]],
        outputs: &'a mut [&'b mut [u8]],
    ) -> Result<u32> {
        loop {
            // Reclaim earlier in-flight entries (fire-and-forget commands
            // submitted before this one) so the whole queue keeps making
            // progress.
            self.pump_completions(transport)?;
            if self.queue.peek_used() == Some(token) {
                // SAFETY: same buffers as the `add` in `add_sync`; still alive
                // in the caller's frame.
                return unsafe { self.queue.pop_used(token, inputs, outputs) };
            }
            spin_loop();
        }
    }

    /// Adds the buffers of a [`PendingSubmit`] to the ring WITHOUT notifying
    /// the host. Callers must eventually call [`ControlQueue::maybe_kick`], or
    /// the command sits in the avail ring undelivered.
    fn add_pending(&mut self, entry: &mut PendingSubmit) -> Result<u16> {
        let (cmd, data, resp) = entry_bufs(entry, &self.vbuf_cmds, &mut self.vbuf_resps);
        match data {
            // SAFETY: the entry's buffers are owned by the vbuf arenas and the
            // entry, and stay alive (untouched) until the used entry is popped
            // with them.
            Some(d) => unsafe { self.queue.add(&[cmd, d], &mut [resp]) },
            // SAFETY: as above; there is no extra payload buffer.
            None => unsafe { self.queue.add(&[cmd], &mut [resp]) },
        }
    }

    /// Accounts a successfully enqueued command and delivers the batch when
    /// `KICK_THRESHOLD` commands have accumulated (bounds delivery latency for
    /// consumers that never notify) or when the ring is nearly full (real
    /// backpressure — a host that stopped draining is always nudged).
    fn account_enqueued(&mut self, transport: &mut impl Transport) {
        self.ctrl_pending = self.ctrl_pending.saturating_add(1);
        if self.ctrl_pending >= KICK_THRESHOLD || self.queue.available_desc() <= 2 {
            self.maybe_kick(transport, true);
        }
    }

    /// Decides whether to physically notify the host.
    ///
    /// Drains the accumulator, then: `force` notifies unconditionally (the
    /// threshold was reached, a response is owed, or the caller needs commands
    /// on another queue to see control-queue state); otherwise
    /// `should_notify()` (≡ `virtqueue_kick_prepare`) reads the
    /// host-suppressed `avail_event` and notifies only when the host is
    /// waiting for a kick — with `RING_EVENT_IDX` this coalesces bursts of
    /// commands into ~one MMIO write per host-drain cycle.
    fn maybe_kick(&mut self, transport: &mut impl Transport, force: bool) {
        if !force && self.ctrl_pending == 0 {
            return;
        }
        self.ctrl_pending = 0;
        if force || self.queue.available_desc() <= 2 || self.queue.should_notify() {
            transport.notify(QUEUE_TRANSMIT);
        }
    }

    /// Notifies the host if it is waiting for a kick and accumulated commands
    /// exist — Linux `virtio_gpu_notify()` at the transaction boundary. Call
    /// at the end of a batch of fire-and-forget commands to deliver them with
    /// a single kick instead of waiting for [`KICK_THRESHOLD`]; also before
    /// submitting a command on a *different* queue that references resources
    /// created by control commands (the queues have no mutual ordering
    /// guarantee). Commands parked because the ring was full are *not*
    /// delivered by this — they re-enter the ring via
    /// [`ControlQueue::flush_pending`] once the host drains. No-op when the
    /// accumulator is empty.
    pub(crate) fn notify(&mut self, transport: &mut impl Transport) {
        self.maybe_kick(transport, false);
    }

    /// Pops and reclaims every used control-queue entry currently available.
    ///
    /// For each reclaimed entry, recycles the descriptors (`H::unshare` with
    /// the persisted vbuf buffers), advances `completed_fence_id` (implicit
    /// ordering: fence N popped ⇒ all ≤ N done), and logs device-side error
    /// responses (fire-and-forget callers have no other way to learn about
    /// them; Linux `virtio_gpu_dequeue_ctrl_func` logs them too). This is the
    /// counterpart of Linux's IRQ-driven dequeue func; call it from the IRQ
    /// handler and/or from the polling wait paths.
    ///
    /// Entries belonging to an in-flight [`ControlQueue::request_sync`] have
    /// no pending record (their buffers live in the caller's frame); the used
    /// ring is strictly ordered, so once one is reached nothing behind it can
    /// be reclaimed either and this returns, leaving it for its waiter.
    pub(crate) fn pump_completions(&mut self, transport: &mut impl Transport) -> Result {
        while self.queue.can_pop() {
            let Some(token) = self.queue.peek_used() else {
                break;
            };
            let Some(entry) = self.pending[token as usize].take() else {
                break;
            };
            {
                let (cmd, data, resp) = entry_bufs(&entry, &self.vbuf_cmds, &mut self.vbuf_resps);
                let popped = match data {
                    // SAFETY: the vbuf arena slot and the data box are the
                    // exact buffers `add` saw; they are owned, address-stable,
                    // and untouched since enqueue, so unshare gets valid
                    // buffers.
                    Some(d) => unsafe { self.queue.pop_used(token, &[cmd, d], &mut [resp]) },
                    // SAFETY: as above; there is no extra payload buffer.
                    None => unsafe { self.queue.pop_used(token, &[cmd], &mut [resp]) },
                };
                if let Err(e) = popped {
                    // The entry never completed: give its buffers back before
                    // propagating, so the pool does not leak slots.
                    self.vbuf_free.push(entry.slot);
                    return Err(e);
                }
            }
            if entry.fence_id > self.completed_fence_id {
                self.completed_fence_id = entry.fence_id;
            }
            // Fire-and-forget: the response is dropped here (no waiter), but
            // surface device-side errors on the log.
            let rsp_hdr = CtrlHeader::read_from_bytes(&self.vbuf_resps[entry.slot])
                .expect("response buffer is exactly one CtrlHeader");
            if rsp_hdr.hdr_type.0 >= Command::ERR_UNSPEC.0 {
                let cmd_hdr = CtrlHeader::read_from_bytes(&self.vbuf_cmds[entry.slot][..RESP_SIZE])
                    .expect("command buffer holds at least one CtrlHeader");
                log::warn!(
                    "virtio-gpu: control command 0x{:x} (token {}) failed with error response \
                     0x{:x}",
                    cmd_hdr.hdr_type.0,
                    token,
                    rsp_hdr.hdr_type.0
                );
            }
            self.vbuf_free.push(entry.slot);
        }
        // Slots freed by the pops: put any parked commands back on the ring in
        // submission order (this drains the FIFO as the host makes progress,
        // even when the guest is between transactions — e.g. driven by the IRQ
        // path).
        self.flush_pending(transport)
    }

    /// Moves parked commands onto the ring in strict FIFO order, as long as
    /// there are free slots.
    ///
    /// Re-added commands count toward the accumulator; if any were re-added,
    /// one notify at the end delivers them (the host may be idle between
    /// transactions and nothing else would kick). No-op when the FIFO is
    /// empty.
    fn flush_pending(&mut self, transport: &mut impl Transport) -> Result {
        let mut re_added = false;
        while let Some(mut cmd) = self.pending_commands.pop_front() {
            // `cmd` is moved out of the FIFO first, so no borrow of
            // `pending_commands` outlives the `add_pending` call.
            match self.add_pending(&mut cmd) {
                Ok(token) => {
                    self.pending[token as usize] = Some(cmd);
                    self.ctrl_pending = self.ctrl_pending.saturating_add(1);
                    re_added = true;
                }
                Err(Error::QueueFull) => {
                    // Ring saturated again: park it back at the front and wait
                    // for another drain trigger (next enqueue / pump / IRQ).
                    self.pending_commands.push_front(cmd);
                    break;
                }
                Err(e) => {
                    self.pending_commands.push_front(cmd);
                    return Err(e);
                }
            }
        }
        if re_added {
            self.maybe_kick(transport, false);
        }
        Ok(())
    }

    /// Blocks until the fence identified by `fence_id` (and everything
    /// enqueued before it) has been popped from the ring.
    ///
    /// Delivers the fire-and-forget commands accumulated since the last kick
    /// before waiting: the fenced entry itself may still be sitting in the
    /// kick accumulator, so a wait must force delivery (the same invariant
    /// Linux guarantees with its `virtio_gpu_notify()` before
    /// `virtio_gpu_wait_ioctl`).
    ///
    /// The wait busy-polls with `spin_loop`, like [`ControlQueue::request_sync`].
    pub(crate) fn wait_fence(&mut self, transport: &mut impl Transport, fence_id: u64) -> Result {
        while self.completed_fence_id < fence_id {
            // Force a kick decision: the fenced entry may not have been
            // delivered to the host yet (below [`KICK_THRESHOLD`] and away
            // from a full ring, `enqueue` performs no kick on its own).
            self.notify(transport);
            self.pump_completions(transport)?;
            if self.completed_fence_id >= fence_id {
                break;
            }
            spin_loop();
        }
        Ok(())
    }

    /// Non-blocking fence query: has `fence_id` (and everything enqueued
    /// before it) already been popped, i.e. has its virgl fence fired?
    ///
    /// The counterpart of Linux `dma_resv_test_signaled` in the NOWAIT probe
    /// of `virtio_gpu_wait_ioctl` (virtgpu_ioctl.c).
    pub(crate) fn fence_completed(&self, fence_id: u64) -> bool {
        self.completed_fence_id >= fence_id
    }
}

/// Slices a pending entry's device-visible buffers out of the arenas: the
/// command bytes, the optional extra payload, and the device-writable response
/// buffer.
fn entry_bufs<'a>(
    entry: &'a PendingSubmit,
    cmds: &'a [[u8; INLINE_CMD_SIZE]],
    resps: &'a mut [[u8; RESP_SIZE]],
) -> (&'a [u8], Option<&'a [u8]>, &'a mut [u8]) {
    (
        &cmds[entry.slot][..entry.cmd_len],
        entry.data.as_deref(),
        &mut resps[entry.slot],
    )
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
    use alloc::sync::Arc;
    use std::sync::Mutex;
    use zerocopy::{FromBytes, Immutable, IntoBytes};

    const Q: u16 = QUEUE_TRANSMIT;
    const QSIZE: usize = CTRL_QUEUE_SIZE as usize;
    const RSP: u32 = RESP_SIZE as u32;

    #[repr(C)]
    #[derive(Clone, Copy, FromBytes, Immutable, IntoBytes)]
    struct TestCmd {
        kind: u32,
        seq: u32,
    }

    fn make_ctrl(
        event_idx: bool,
    ) -> (
        ControlQueue<FakeHal>,
        Arc<Mutex<State<()>>>,
        FakeTransport<()>,
    ) {
        let state = Arc::new(Mutex::new(State::new(
            vec![QueueStatus::default(), QueueStatus::default()],
            (),
        )));
        let mut transport = FakeTransport {
            device_type: DeviceType::Block,
            max_queue_size: CTRL_QUEUE_SIZE as u32,
            device_features: 0,
            state: state.clone(),
        };
        let ctrl = ControlQueue::new(&mut transport, true, event_idx, false).unwrap();
        (ctrl, state, transport)
    }

    /// Simulates the device processing exactly one descriptor chain (FIFO):
    /// reads the command, writes an `OK` response, marks the entry used.
    fn complete_one(state: &Mutex<State<()>>) -> bool {
        state.lock().unwrap().read_write_queue::<QSIZE>(Q, |input| {
            // A zero hdr_type is below ERR_UNSPEC, so no error is logged.
            let mut out = vec![0u8; RESP_SIZE];
            out[0] = input[0];
            out
        })
    }

    #[test]
    fn fire_and_forget_commands_are_delivered_without_caller_notify() {
        // event_idx off, so `should_notify` never suppresses. A consumer that
        // NEVER calls `notify` still gets every command delivered: the
        // threshold kicks after KICK_THRESHOLD enqueues. This is the safety
        // property that keeps such consumers working.
        let (mut ctrl, state, mut transport) = make_ctrl(false);

        for i in 0..(KICK_THRESHOLD - 1) {
            ctrl.enqueue(&mut transport, &TestCmd { kind: 0, seq: i }, None, 0)
                .unwrap();
        }
        assert!(!State::poll_queue_notified(&state, Q));

        // The threshold enqueue forces the kick covering the whole batch.
        ctrl.enqueue(
            &mut transport,
            &TestCmd {
                kind: 0,
                seq: KICK_THRESHOLD - 1,
            },
            None,
            0,
        )
        .unwrap();
        assert!(State::poll_queue_notified(&state, Q));

        // An explicit notify with an empty accumulator must NOT kick.
        ctrl.notify(&mut transport);
        assert!(!State::poll_queue_notified(&state, Q));

        // The host drains one command; nothing new to notify until the next
        // enqueue.
        assert!(complete_one(&state));
        ctrl.pump_completions(&mut transport).unwrap();
        assert!(!State::poll_queue_notified(&state, Q));
    }

    #[test]
    fn notify_delivers_accumulated_batch_early() {
        // A transaction-boundary consumer: notify after a small batch delivers
        // it immediately, well before the threshold.
        let (mut ctrl, state, mut transport) = make_ctrl(false);

        for i in 0..3 {
            ctrl.enqueue(&mut transport, &TestCmd { kind: 0, seq: i }, None, 0)
                .unwrap();
        }
        assert!(!State::poll_queue_notified(&state, Q));
        ctrl.notify(&mut transport);
        assert!(State::poll_queue_notified(&state, Q));
    }

    #[test]
    fn sync_request_roundtrip_zero_copy() {
        let (mut ctrl, state, mut transport) = make_ctrl(true);

        let req = [7u8; 16];
        let mut resp = [0u8; RESP_SIZE];
        let token = ctrl
            .add_sync(&mut transport, &[&req], &mut [&mut resp])
            .unwrap();

        // A response is owed, so the add kicks unconditionally.
        assert!(State::poll_queue_notified(&state, Q));

        // The device reads the command bytes (shared copy) and writes the
        // response into the shared copy of `resp`.
        assert!(state.lock().unwrap().read_write_queue::<QSIZE>(Q, |input| {
            assert_eq!(&input[..16], &[7u8; 16]);
            let mut out = vec![0u8; RESP_SIZE];
            out[0] = 0xAA;
            out
        }));

        let used_len = ctrl
            .wait_sync(token, &mut transport, &[&req], &mut [&mut resp])
            .unwrap();
        assert_eq!(used_len, 16 + RSP);
        // `unshare` copied the device-written bytes back into our buffer.
        assert_eq!(resp[0], 0xAA);
        assert_eq!(ctrl.completed_fence_id, 0);
    }

    #[test]
    fn parked_commands_flush_in_fifo_order() {
        let (mut ctrl, state, mut transport) = make_ctrl(true);

        // Fill the ring (indirect: one ring slot per command).
        for i in 1..=64u64 {
            let r = ctrl
                .enqueue(
                    &mut transport,
                    &TestCmd {
                        kind: 0,
                        seq: i as u32,
                    },
                    None,
                    i,
                )
                .unwrap();
            assert!(r.is_some());
        }
        // Threshold and near-full kicks happened during the fill; clear the
        // flag so later assertions start from a clean slate.
        State::poll_queue_notified(&state, Q);

        // Ring full: further fire-and-forget commands park instead of
        // blocking, and `enqueue` reports `None` for them.
        for i in 65..=67u64 {
            let r = ctrl
                .enqueue(
                    &mut transport,
                    &TestCmd {
                        kind: 0,
                        seq: i as u32,
                    },
                    None,
                    i,
                )
                .unwrap();
            assert!(r.is_none());
        }
        assert_eq!(ctrl.pending_commands.len(), 3);

        // Host drains everything originally in the ring.
        while complete_one(&state) {}
        ctrl.pump_completions(&mut transport).unwrap();
        assert_eq!(ctrl.completed_fence_id, 64);
        assert!(ctrl.fence_completed(64));
        assert!(!ctrl.fence_completed(65));

        // Freed ring slots let the parked commands back on, in FIFO order.
        assert_eq!(ctrl.pending_commands.len(), 0);

        // Completing exactly one more entry must advance the fence to 65 —
        // proving the first re-added command was the first parked one.
        assert!(complete_one(&state));
        ctrl.pump_completions(&mut transport).unwrap();
        assert_eq!(ctrl.completed_fence_id, 65);

        // The rest completes in order too.
        while complete_one(&state) {}
        ctrl.pump_completions(&mut transport).unwrap();
        assert_eq!(ctrl.completed_fence_id, 67);
        assert!(ctrl.fence_completed(67));

        // Every vbuf slot is back on the free list and nothing is in flight.
        assert_eq!(ctrl.vbuf_free.len(), MAX_INFLIGHT);
        assert!(ctrl.pending.iter().all(|p| p.is_none()));
    }

    #[test]
    fn fenced_sync_request_advances_fence() {
        // Regression for a deadlock: a BLOCKING fenced submit pops its own
        // FLAG_FENCE response, and that pop is the fence observation. The
        // high-water mark must advance here too — or a following
        // `wait_fence` spins forever on an already-fired fence.
        let (mut ctrl, state, mut transport) = make_ctrl(true);

        let worker_state = state.clone();
        let worker = std::thread::spawn(move || {
            State::wait_until_queue_notified(&worker_state, Q);
            assert!(complete_one(&worker_state));
        });

        let req = [3u8; 8];
        let mut resp = [0u8; RESP_SIZE];
        ctrl.request_sync_fenced(&mut transport, &[&req], &mut [&mut resp], 5)
            .unwrap();
        worker.join().unwrap();

        assert!(ctrl.fence_completed(5));
        // Must return immediately: the fence was already observed by the
        // blocking submit itself.
        ctrl.wait_fence(&mut transport, 5).unwrap();
    }

    #[test]
    fn wait_fence_delivers_undelivered_fenced_command() {
        // Regression for a deadlock: below KICK_THRESHOLD and away from a full
        // ring, `enqueue` performs no kick decision at all, so a fenced
        // command sits undelivered in the avail ring until something forces
        // delivery. `wait_fence` must deliver it itself (Linux guarantees the
        // same with virtio_gpu_notify() before virtio_gpu_wait_ioctl).
        let (mut ctrl, state, mut transport) = make_ctrl(true);
        ctrl.enqueue(&mut transport, &TestCmd { kind: 0, seq: 1 }, None, 5)
            .unwrap();
        // Not delivered: the enqueue is below the threshold and the ring is
        // not near full, so no kick decision ran.
        assert!(!State::poll_queue_notified(&state, Q));

        // Fake device: process the entry as soon as it IS notified.
        let worker_state = state.clone();
        let worker = std::thread::spawn(move || {
            State::wait_until_queue_notified(&worker_state, Q);
            assert!(complete_one(&worker_state));
        });

        ctrl.wait_fence(&mut transport, 5).unwrap();
        worker.join().unwrap();
        assert!(ctrl.fence_completed(5));
    }

    #[test]
    fn sync_entry_survives_pump_completions() {
        let (mut ctrl, state, mut transport) = make_ctrl(true);

        // Fill the ring with fire-and-forget commands and park two more.
        for i in 1..=64u64 {
            ctrl.enqueue(
                &mut transport,
                &TestCmd {
                    kind: 0,
                    seq: i as u32,
                },
                None,
                i,
            )
            .unwrap();
        }
        for i in 65..=66u64 {
            ctrl.enqueue(
                &mut transport,
                &TestCmd {
                    kind: 0,
                    seq: i as u32,
                },
                None,
                i,
            )
            .unwrap();
        }
        assert_eq!(ctrl.pending_commands.len(), 2);

        // Host drains the whole ring; the flush in pump re-adds the parked
        // pair.
        while complete_one(&state) {}
        ctrl.pump_completions(&mut transport).unwrap();
        assert_eq!(ctrl.pending_commands.len(), 0);

        // A sync request whose entry the device completes before its waiter
        // runs: `pump_completions` (e.g. from the IRQ path) must leave the
        // completed entry alone for `wait_sync` instead of erroring on it.
        let req = [9u8; 8];
        let mut resp = [0u8; RESP_SIZE];
        let token = ctrl
            .add_sync(&mut transport, &[&req], &mut [&mut resp])
            .unwrap();
        // The device completes everything in FIFO order, including the sync
        // request's own entry.
        while complete_one(&state) {}
        let used_len = ctrl
            .wait_sync(token, &mut transport, &[&req], &mut [&mut resp])
            .unwrap();
        assert_eq!(used_len, 8 + RSP);
        // The sync request's fence id is 0, so the high-water mark is untouched.
        assert_eq!(ctrl.completed_fence_id, 66);
    }
}
