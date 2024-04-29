//! TODO: Add docs

use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use bitflags::bitflags;
use core::mem;
use log::info;
use zerocopy::{AsBytes, FromBytes, FromZeroes};
type PCMStateResult<T = ()> = core::result::Result<T, StreamError>;

use crate::{queue::VirtQueue, transport::Transport, volatile::ReadOnly, Error, Hal, Result, PAGE_SIZE};

/// TODO: Add docs
pub struct VirtIOSound<H: Hal, T: Transport> {
    transport: T,

    control_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    event_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    tx_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    rx_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,

    negotiated_features: SoundFeatures,
    config: VirtIOSoundConfig,

    queue_buf_send: Box<[u8]>,
    queue_buf_recv: Box<[u8]>,
}

impl<H: Hal, T: Transport> VirtIOSound<H, T> {
    /// Craete a new VirtIO-Sound driver.
    pub fn new(mut transport: T) -> Result<Self> {
        let negotiated_features = transport.begin_init(SUPPORTED_FEATURES);
        info!(
            "[sound device] negotiated_features: {}",
            String::from(negotiated_features)
        );

        let control_queue = VirtQueue::new(
            &mut transport,
            CONTROL_QUEUE_IDX,
            negotiated_features.contains(SoundFeatures::VIRTIO_F_INDIRECT_DESC),
            negotiated_features.contains(SoundFeatures::VIRTIO_F_EVENT_IDX),
        )?;
        // The driver MUST populate the event queue
        // with empty buffers of at least the struct virtio_snd_event size(struct VirtIOSndEvent Size in config.rs)
        let event_queue = VirtQueue::new(
            &mut transport,
            EVENT_QUEUE_IDX,
            negotiated_features.contains(SoundFeatures::VIRTIO_F_INDIRECT_DESC),
            negotiated_features.contains(SoundFeatures::VIRTIO_F_EVENT_IDX),
        )?;
        let tx_queue = VirtQueue::new(
            &mut transport,
            TX_QUEUE_IDX,
            negotiated_features.contains(SoundFeatures::VIRTIO_F_INDIRECT_DESC),
            negotiated_features.contains(SoundFeatures::VIRTIO_F_EVENT_IDX),
        )?;
        let rx_queue = VirtQueue::new(
            &mut transport,
            RX_QUEUE_IDX,
            negotiated_features.contains(SoundFeatures::VIRTIO_F_INDIRECT_DESC),
            negotiated_features.contains(SoundFeatures::VIRTIO_F_EVENT_IDX),
        )?;

        // read configuration space
        let config_ptr = transport.config_space::<VirtIOSoundConfig>()?;
        let config = unsafe { *(config_ptr.as_ptr()) };
        info!("[sound device] config: {:?}", config);

        let queue_buf_send = FromZeroes::new_box_slice_zeroed(PAGE_SIZE);
        let queue_buf_recv = FromZeroes::new_box_slice_zeroed(PAGE_SIZE);

        transport.finish_init();

        Ok(VirtIOSound {
            transport,
            control_queue,
            event_queue,
            tx_queue,
            rx_queue,
            negotiated_features,
            config,
            queue_buf_send,
            queue_buf_recv,
        })
    }

    /// Acknowledge interrupt.
    pub fn ack_interrupt(&mut self) -> bool {
        self.transport.ack_interrupt()
    }

    fn request<Req: AsBytes, Rsp: FromBytes>(&mut self, req: Req) -> Result<Rsp> {
        req.write_to_prefix(&mut self.queue_buf_send).unwrap();
        self.control_queue.add_notify_wait_pop(
            &[&self.queue_buf_send],
            &mut [&mut self.queue_buf_recv],
            &mut self.transport,
        )?;
        Ok(Rsp::read_from_prefix(&self.queue_buf_recv).unwrap())
    }

    /// TODO: Add docs
    pub fn query_config_info(&mut self, request_type: ItemInfomationRequestType) -> Result<VirtIOSndInfo> {
        let request_header = VirtIOSndHdr::from(request_type);
        let (start_id, count, size) = match request_type {
            ItemInfomationRequestType::VirtioSndRJackInfo => (0, 1, mem::size_of::<VirtIOSndJackInfo>()),
            ItemInfomationRequestType::VirtioSndRPcmInfo => (1, 1, mem::size_of::<u32>()),
            ItemInfomationRequestType::VirtioSndRChmapInfo => (2, 1, mem::size_of::<u32>()),
        };
        let rsp: VirtIOSndQueryInfoRsp = self.request(VirtIOSndQueryInfo {
            hdr: request_header,
            start_id,
            count,
            size: size as u32,
        })?;
        if rsp.hdr == VirtIOSndHdr::from(RequestStatusCode::VirtioSndSOk) {
            Ok(rsp.info)
        } else {
            Err(Error::IoError)
        }
    }

    /// Query information about the available jacks.
    pub fn jack_info(&mut self) -> Result<VirtIOSndJackInfo> {
        let request_header = VirtIOSndHdr::from(ItemInfomationRequestType::VirtioSndRJackInfo);
        let rsp: VirtIOSndJackInfoRsp = self.request(VirtIOSndQueryInfo {
            hdr: request_header,
            start_id: 0,
            count: 1,
            size: mem::size_of::<VirtIOSndJackInfoRsp>() as u32
        })?;
        if rsp.hdr == VirtIOSndHdr::from(RequestStatusCode::VirtioSndSOk) {
            Ok(rsp.body)
        } else {
            Err(Error::IoError)
        }
    }

    /// Query information about the available streams.
    pub fn pcm_info(&mut self) -> Result<VirtIOSndPcmInfo> {
        let request_hdr = VirtIOSndHdr::from(ItemInfomationRequestType::VirtioSndRPcmInfo);
        let rsp: VirtIOSndPcmInfoRsp = self.request(VirtIOSndQueryInfo {
            hdr: request_hdr,
            start_id: 1,
            count: 1,
            size: mem::size_of::<VirtIOSndPcmInfoRsp>() as u32
        })?;
        if rsp.hdr == VirtIOSndHdr::from(RequestStatusCode::VirtioSndSOk) {
            Ok(rsp.body)
        } else {
            Err(Error::IoError)
        }
    }

    /// TODO: VIRTIO_SND_R_JACK_REMAP
    pub fn jack_remap() {
        
    }

    /// Set selected stream parameters for the specified stream ID.
    pub fn pcm_set_params(&mut self, stream_id: u32, buffer_bytes: u32, period_bytes: u32, features: u32, channels: u8, format: u8, rate: u8) -> Result {
        let request_hdr = VirtIOSndHdr::from(CommandCode::VirtioSndRPcmSetParams);
        let rsp: VirtIOSndHdr = self.request(VirtIOSndPcmSetParams {
            hdr: VirtIOSndPcmHdr {
                hdr: request_hdr,
                stream_id
            },
            buffer_bytes,
            period_bytes,
            features,
            channels,
            format,
            rate,
            _padding: 0
        })?;
        // rsp is just a header, so it can be compared with VirtIOSndHdr
        if rsp == VirtIOSndHdr::from(RequestStatusCode::VirtioSndSOk) {
            Ok(())
        } else {
            Err(Error::IoError)
        }
    }

    /// Prepare a stream with specified stream ID.
    pub fn pcm_prepare(&mut self, stream_id: u32) -> Result {
        let request_hdr = VirtIOSndHdr::from(CommandCode::VirtioSndRPcmPrepare);
        let rsp: VirtIOSndHdr = self.request(VirtIOSndPcmHdr {
            hdr: request_hdr,
            stream_id
        })?;
        // rsp is just a header, so it can be compared with VirtIOSndHdr
        if rsp == VirtIOSndHdr::from(RequestStatusCode::VirtioSndSOk) {
            Ok(())
        } else {
            Err(Error::IoError)
        }
    }

    /// Release a stream with specified stream ID.
    pub fn pcm_release(&mut self, stream_id: u32) -> Result {
        let request_hdr = VirtIOSndHdr::from(CommandCode::VirtioSndRPcmRelease);
        let rsp: VirtIOSndHdr = self.request(VirtIOSndPcmHdr {
            hdr: request_hdr,
            stream_id
        })?;
        // rsp is just a header, so it can be compared with VirtIOSndHdr
        if rsp == VirtIOSndHdr::from(RequestStatusCode::VirtioSndSOk) {
            Ok(())
        } else {
            Err(Error::IoError)
        }
    }

    /// Start a stream with specified stream ID.
    pub fn pcm_start(&mut self, stream_id: u32) -> Result {
        let request_hdr = VirtIOSndHdr::from(CommandCode::VirtioSndRPcmStart);
        let rsp: VirtIOSndHdr = self.request(VirtIOSndPcmHdr {
            hdr: request_hdr,
            stream_id
        })?;
        // rsp is just a header, so it can be compared with VirtIOSndHdr
        if rsp == VirtIOSndHdr::from(RequestStatusCode::VirtioSndSOk) {
            Ok(())
        } else {
            Err(Error::IoError)
        }
    }

    /// Stop a stream with specified stream ID.
    pub fn pcm_stop(&mut self, stream_id: u32) -> Result {
        let request_hdr = VirtIOSndHdr::from(CommandCode::VirtioSndRPcmStop);
        let rsp: VirtIOSndHdr = self.request(VirtIOSndPcmHdr {
            hdr: request_hdr,
            stream_id
        })?;
        // rsp is just a header, so it can be compared with VirtIOSndHdr
        if rsp == VirtIOSndHdr::from(RequestStatusCode::VirtioSndSOk) {
            Ok(())
        } else {
            Err(Error::IoError)
        }
    }

}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
enum PCMState {
    #[default]
    SetParams,
    Prepare,
    Release,
    Start,
    Stop,
}

/// Stream errors.
#[derive(Debug, PartialEq, Eq)]
enum StreamError {
    ///
    InvalidState(&'static str, PCMState),
    ///
    InvalidStateTransition(PCMState, PCMState),
    ///
    InvalidStreamId(u32),
    ///
    DescriptorReadFailed,
    ///
    DescriptorWriteFailed,
    ///
    CouldNotDisconnectStream,
}

macro_rules! set_new_state {
    ($new_state_fn:ident, $new_state:expr, $($valid_source_states:tt)*) => {
        fn $new_state_fn(&mut self) -> PCMStateResult<()> {
            if !matches!(self, $($valid_source_states)*) {
                return Err(StreamError::InvalidStateTransition(*self, $new_state));
            }
            *self = $new_state;
            Ok(())
        }
    };
}

impl PCMState {
    fn new() -> Self {
        Self::default()
    }

    set_new_state!(
        set_parameters,
        Self::SetParams,
        Self::SetParams | Self::Prepare | Self::Release
    );

    set_new_state!(
        prepare,
        Self::Prepare,
        Self::SetParams | Self::Prepare | Self::Release
    );

    set_new_state!(start, Self::Start, Self::Prepare | Self::Stop);

    set_new_state!(stop, Self::Stop, Self::Start);

    set_new_state!(release, Self::Release, Self::Prepare | Self::Stop);
}

const QUEUE_SIZE: u16 = 16;
const CONTROL_QUEUE_IDX: u16 = 0;
const EVENT_QUEUE_IDX: u16 = 1;
const TX_QUEUE_IDX: u16 = 2;
const RX_QUEUE_IDX: u16 = 3;

const SUPPORTED_FEATURES: SoundFeatures = SoundFeatures::all();

bitflags! {
    /// In virtIO v1.2, there are no specific features defined for virtio-sound, so now it's common
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct SoundFeatures: u64 {
        // device independent
        const VIRTIO_F_NOTIFY_ON_EMPTY       = 1 << 24; // legacy
        const VIRTIO_F_ANY_LAYOUT            = 1 << 27; // legacy
        const VIRTIO_F_INDIRECT_DESC         = 1 << 28;
        const VIRTIO_F_EVENT_IDX             = 1 << 29;
        const UNUSED                         = 1 << 30; // legacy
        const VIRTIO_F_VERSION_1             = 1 << 32; // detect legacy

        // since virtio v1.1
        const VIRTIO_F_ACCESS_PLATFORM       = 1 << 33;
        const VIRTIO_F_RING_PACKED           = 1 << 34;
        const VIRTIO_F_IN_ORDER              = 1 << 35;
        const VIRTIO_F_ORDER_PLATFORM        = 1 << 36;
        const VIRTIO_F_SR_IOV                = 1 << 37;
        const VIRTIO_F_NOTIFICATION_DATA     = 1 << 38;
        const VIRTIO_F_NOTIF_CONFIG_DATA     = 1 << 39;
        const VIRTIO_F_RING_RESET            = 1 << 40;
    }
}

impl From<SoundFeatures> for String {
    fn from(sound_features: SoundFeatures) -> Self {
        let mut features = vec![];
        if sound_features.contains(SoundFeatures::VIRTIO_F_NOTIFY_ON_EMPTY) {
            features.push("NOTIFY_ON_EMPTY");
        }
        if sound_features.contains(SoundFeatures::VIRTIO_F_ANY_LAYOUT) {
            features.push("ANY_LAYOUT");
        }
        if sound_features.contains(SoundFeatures::VIRTIO_F_INDIRECT_DESC) {
            features.push("RING_INDIRECT_DESC");
        }
        if sound_features.contains(SoundFeatures::VIRTIO_F_EVENT_IDX) {
            features.push("RING_EVENT_IDX");
        }
        if sound_features.contains(SoundFeatures::UNUSED) {
            features.push("UNUSED");
        }
        if sound_features.contains(SoundFeatures::VIRTIO_F_VERSION_1) {
            features.push("VERSION_1");
        }
        if sound_features.contains(SoundFeatures::VIRTIO_F_ACCESS_PLATFORM) {
            features.push("ACCESS_PLATFORM");
        }
        if sound_features.contains(SoundFeatures::VIRTIO_F_RING_PACKED) {
            features.push("RING_PACKED");
        }
        if sound_features.contains(SoundFeatures::VIRTIO_F_IN_ORDER) {
            features.push("IN_ORDER");
        }
        if sound_features.contains(SoundFeatures::VIRTIO_F_ORDER_PLATFORM) {
            features.push("ORDER_PLATFORM");
        }
        if sound_features.contains(SoundFeatures::VIRTIO_F_SR_IOV) {
            features.push("SR_IOV");
        }
        if sound_features.contains(SoundFeatures::VIRTIO_F_NOTIFICATION_DATA) {
            features.push("NOTIFICATION_DATA");
        }
        format!("[{}]", features.join(", "))
    }
}

#[derive(Debug, Clone, Copy)]
struct VirtIOSoundConfig {
    jacks: ReadOnly<u32>,
    streams: ReadOnly<u32>,
    chmaps: ReadOnly<u32>,
}

/// In virtIO v1.2, this enum should be called "Code".
///
/// To avoid ambiguity in its meaning, I use the term "CommandCode" here.
enum CommandCode {
    /* jack control request types */
    VirtioSndRJackInfo = 1,
    VirtioSndRJackRemap,

    /* PCM control request types */
    VirtioSndRPcmInfo = 0x0100,
    VirtioSndRPcmSetParams,
    VirtioSndRPcmPrepare,
    VirtioSndRPcmRelease,
    VirtioSndRPcmStart,
    VirtioSndRPcmStop,

    /* channel map control request types */
    VirtioSndRChmapInfo = 0x0200,

    /* jack event types */
    VirtioSndEvtJackConnected = 0x1000,
    VirtioSndEvtJackDisconnected,

    /* PCM event types */
    VirtioSndEvtPcmPeriodElapsed = 0x1100,
    VirtioSndEvtPcmXrun,

    /* common status codes */
    /// success
    VirtioSndSOk = 0x8000,
    /// a control message is malformed or contains invalid parameters
    VirtioSndSBadMsg,
    /// requested operation or parameters are not supported
    VirtioSndSNotSupp,
    ///  an I/O error occurred
    VirtioSndSIoErr,
}

impl From<CommandCode> for VirtIOSndHdr {
    fn from(value: CommandCode) -> Self {
        VirtIOSndHdr { command_code: value as _ }
    }
}

/// TODO: Add docs.
#[derive(Clone, Copy)]
pub enum ItemInfomationRequestType {
    /// TODO
    VirtioSndRJackInfo = 1,
    /// TODO
    VirtioSndRPcmInfo = 0x0100,
    /// TODO
    VirtioSndRChmapInfo = 0x0200,
}

impl From<ItemInfomationRequestType> for VirtIOSndHdr {
    fn from(value: ItemInfomationRequestType) -> Self {
        VirtIOSndHdr {
            command_code: value as _,
        }
    }
}

enum RequestStatusCode {
    /* common status codes */
    VirtioSndSOk = 0x8000,
    VirtioSndSBadMsg,
    VirtioSndSNotSupp,
    VirtioSndSIoErr,
}

impl From<RequestStatusCode> for VirtIOSndHdr {
    fn from(value: RequestStatusCode) -> Self {
        VirtIOSndHdr {
            command_code: value as _,
        }
    }
}


/// A common header
#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes, PartialEq, Eq)]
struct VirtIOSndHdr {
    command_code: u32,
}

#[repr(C)]
// An event notification
struct VirtIOSndEvent {
    hdr: VirtIOSndHdr,
    data: u32,
}

const VIRTIO_SND_D_OUTPUT: u16 = 0;
const VIRTIO_SND_D_INPUT: u16 = 1;

#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
struct VirtIOSndQueryInfo {
    /// specifies a particular item request type (VIRTIO_SND_R_*_INFO)
    hdr: VirtIOSndHdr,
    /// specifies the starting identifier for the item
    /// (the range of available identifiers is limited
    ///  by the total number of particular items
    ///  that is indicated in the device configuration space)
    start_id: u32,
    /// specifies the number of items for which information is requested
    ///  (the total number of particular items is indicated
    ///  in the device configuration space).
    count: u32,
    /// specifies the size of the structure containing information for one item
    /// (used for backward compatibility)
    size: u32,
}

#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
struct VirtIOSndQueryInfoRsp {
    hdr: VirtIOSndHdr,
    info: VirtIOSndInfo
}

/// TODO: Add docs
#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
pub struct VirtIOSndInfo {
    hda_fn_nid: u32,
}

#[repr(C)]
struct VirtIOSndJackHdr {
    hdr: VirtIOSndHdr,
    /// specifies a jack identifier from 0 to jacks - 1
    jack_id: u32,
}

/// TODO
#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
pub struct VirtIOSndJackInfo {
    hdr: VirtIOSndInfo,
    features: u32,
    /// indicates a pin default configuration value
    hda_reg_defconf: u32,
    /// indicates a pin capabilities value
    hda_reg_caps: u32,
    /// indicates the current jack connection status (1 - connected, 0 - disconnected)
    connected: u8,

    _padding: [u8; 7],
}

#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
struct VirtIOSndJackInfoRsp {
    hdr: VirtIOSndHdr,
    body: VirtIOSndJackInfo
}

#[repr(C)]
struct VirtIOSndJackRemap {
    hdr: VirtIOSndJackHdr,
    association: u32,
    sequence: u32,
}

#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
struct VirtIOSndPcmHdr {
    /// specifies request type (VIRTIO_SND_R_PCM_*)
    hdr: VirtIOSndHdr,
    /// specifies a PCM stream identifier from 0 to streams - 1
    stream_id: u32,
}

enum PcmStreamFeatures {
    VirtioSndPcmFShmemHost = 0,
    VirtioSndPcmFShmemGuest,
    VirtioSndPcmFMsgPolling,
    VirtioSndPcmFEvtShmemPeriods,
    VirtioSndPcmFEvtXruns,
}

impl From<PcmStreamFeatures> for u32 {
    fn from(value: PcmStreamFeatures) -> Self {
        value as _
    }
}

enum PcmSampleFormat {
    /* analog formats (width / physical width) */
    VirtioSndPcmFmtImaAdpcm = 0, /* 4 / 4 bits */
    VirtioSndPcmFmtMuLaw,        /* 8 / 8 bits */
    VirtioSndPcmFmtALaw,         /* 8 / 8 bits */
    VirtioSndPcmFmtS8,           /* 8 / 8 bits */
    VirtioSndPcmFmtU8,           /* 8 / 8 bits */
    VirtioSndPcmFmtS16,          /* 16 / 16 bits */
    VirtioSndPcmFmtU16,          /* 16 / 16 bits */
    VirtioSndPcmFmtS18_3,        /* 18 / 24 bits */
    VirtioSndPcmFmtU18_3,        /* 18 / 24 bits */
    VirtioSndPcmFmtS20_3,        /* 20 / 24 bits */
    VirtioSndPcmFmtU20_3,        /* 20 / 24 bits */
    VirtioSndPcmFmtS24_3,        /* 24 / 24 bits */
    VirtioSndPcmFmtU24_3,        /* 24 / 24 bits */
    VirtioSndPcmFmtS20,          /* 20 / 32 bits */
    VirtioSndPcmFmtU20,          /* 20 / 32 bits */
    VirtioSndPcmFmtS24,          /* 24 / 32 bits */
    VirtioSndPcmFmtU24,          /* 24 / 32 bits */
    VirtioSndPcmFmtS32,          /* 32 / 32 bits */
    VirtioSndPcmFmtU32,          /* 32 / 32 bits */
    VirtioSndPcmFmtFloat,        /* 32 / 32 bits */
    VirtioSndPcmFmtFloat64,      /* 64 / 64 bits */
    /* digital formats (width / physical width) */
    VirtioSndPcmFmtDsdU8,          /* 8 / 8 bits */
    VirtioSndPcmFmtDsdU16,         /* 16 / 16 bits */
    VirtioSndPcmFmtDsdU32,         /* 32 / 32 bits */
    VirtioSndPcmFmtIec958Subframe, /* 32 / 32 bits */
}

impl From<PcmSampleFormat> for u64 {
    fn from(value: PcmSampleFormat) -> Self {
        value as _
    }
}

enum PcmFrameRate {
    VirtioSndPcmRate5512 = 0,
    VirtioSndPcmRate8000,
    VirtioSndPcmRate11025,
    VirtioSndPcmRate16000,
    VirtioSndPcmRate22050,
    VirtioSndPcmRate32000,
    VirtioSndPcmRate44100,
    VirtioSndPcmRate48000,
    VirtioSndPcmRate64000,
    VirtioSndPcmRate88200,
    VirtioSndPcmRate96000,
    VirtioSndPcmRate176400,
    VirtioSndPcmRate192000,
    VirtioSndPcmRate384000,
}

impl From<PcmFrameRate> for u64 {
    fn from(value: PcmFrameRate) -> Self {
        value as _
    }
}

/// TODO: Add docs
#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
pub struct VirtIOSndPcmInfo {
    hdr: VirtIOSndInfo,
    features: u32, /* 1 << VIRTIO_SND_PCM_F_XXX */
    formats: u64,  /* 1 << VIRTIO_SND_PCM_FMT_XXX */
    rate: u64,     /* 1 << VIRTIO_SND_PCM_RATE_XXX */
    /// indicates the direction of data flow (VIRTIO_SND_D_*)
    direction: u8,
    /// indicates a minimum number of supported channels
    channels_min: u8,
    /// indicates a maximum number of supported channels
    channels_max: u8,
    _padding: [u8; 5],
}

#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
struct VirtIOSndPcmInfoRsp {
    hdr: VirtIOSndHdr,
    _padding: [u8; 4], // TODO: Is it right that put _padding here?
    body: VirtIOSndPcmInfo,
}

#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
struct VirtIOSndPcmSetParams {
    hdr: VirtIOSndPcmHdr, /* .code = VIRTIO_SND_R_PCM_SET_PARAMS */
    buffer_bytes: u32,
    period_bytes: u32,
    features: u32, /* 1 << VIRTIO_SND_PCM_F_XXX */
    channels: u8,
    format: u8,
    rate: u8,

    _padding: u8,
}

/// An I/O header
#[repr(C)]
struct VirtIOSndPcmXfer {
    srteam_id: u32,
}

/// An I/O status
#[repr(C)]
struct VirtIOSndPcmStatus {
    status: u32,
    latency_bytes: u32,
}

enum ChannelPosition {
    VirtioSndChmapNone = 0, /* undefined */
    VirtioSndChmapNa,       /* silent */
    VirtioSndChmapMono,     /* mono stream */
    VirtioSndChmapFl,       /* front left */
    VirtioSndChmapFr,       /* front right */
    VirtioSndChmapRl,       /* rear left */
    VirtioSndChmapRr,       /* rear right */
    VirtioSndChmapFc,       /* front center */
    VirtioSndChmapLfe,      /* low frequency (LFE) */
    VirtioSndChmapSl,       /* side left */
    VirtioSndChmapSr,       /* side right */
    VirtioSndChmapRc,       /* rear center */
    VirtioSndChmapFlc,      /* front left center */
    VirtioSndChmapFrc,      /* front right center */
    VirtioSndChmapRlc,      /* rear left center */
    VirtioSndChmapRrc,      /* rear right center */
    VirtioSndChmapFlw,      /* front left wide */
    VirtioSndChmapFrw,      /* front right wide */
    VirtioSndChmapFlh,      /* front left high */
    VirtioSndChmapFch,      /* front center high */
    VirtioSndChmapFrh,      /* front right high */
    VirtioSndChmapTc,       /* top center */
    VirtioSndChmapTfl,      /* top front left */
    VirtioSndChmapTfr,      /* top front right */
    VirtioSndChmapTfc,      /* top front center */
    VirtioSndChmapTrl,      /* top rear left */
    VirtioSndChmapTrr,      /* top rear right */
    VirtioSndChmapTrc,      /* top rear center */
    VirtioSndChmapTflc,     /* top front left center */
    VirtioSndChmapTfrc,     /* top front right center */
    VirtioSndChmapTsl,      /* top side left */
    VirtioSndChmapTsr,      /* top side right */
    VirtioSndChmapLlfe,     /* left LFE */
    VirtioSndChmapRlfe,     /* right LFE */
    VirtioSndChmapBc,       /* bottom center */
    VirtioSndChmapBlc,      /* bottom left center */
    VirtioSndChmapBrc,      /* bottom right center */
}

impl From<ChannelPosition> for u8 {
    fn from(value: ChannelPosition) -> Self {
        value as _
    }
}

/// maximum possible number of channels
const VIRTIO_SND_CHMAP_MAX_SIZE: usize = 18;

struct VirtIOSndChmapInfo {
    hdr: VirtIOSndInfo,
    direction: u8,
    channels: u8,
    positions: [u8; VIRTIO_SND_CHMAP_MAX_SIZE],
}
