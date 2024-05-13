//! TODO: Add docs

use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use bitflags::bitflags;
use core::{fmt::Display, hint::spin_loop, mem, ops::RangeInclusive};
use log::{error, info, warn};
use num_enum::{FromPrimitive, IntoPrimitive};
use zerocopy::{AsBytes, FromBytes, FromZeroes};
type PCMStateResult<T = ()> = core::result::Result<T, StreamError>;

use crate::{
    queue::VirtQueue,
    transport::Transport,
    volatile::{volread, ReadOnly},
    Error, Hal, Result, PAGE_SIZE,
};

/// TODO: Add docs
pub struct VirtIOSound<H: Hal, T: Transport> {
    transport: T,

    control_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    event_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    tx_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,
    rx_queue: VirtQueue<H, { QUEUE_SIZE as usize }>,

    negotiated_features: SoundFeatures,

    jacks: u32,
    streams: u32,
    chmaps: u32,

    pcm_infos: Option<Vec<VirtIOSndPcmInfo>>,
    jack_infos: Option<Vec<VirtIOSndJackInfo>>,
    chmap_infos: Option<Vec<VirtIOSndChmapInfo>>,

    // pcm params
    pcm_parameters: Vec<PcmParameters>,

    queue_buf_send: Box<[u8]>,
    queue_buf_recv: Box<[u8]>,

    set_up: bool,

    output_rsp: Box<[u8]>, // includes pcm_xfer response msg

    event_buf: Box<[u8]>,

    pcm_states: Vec<PCMState>,
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
        let (jacks, streams, chmaps) = unsafe {
            (
                volread!(config_ptr, jacks),
                volread!(config_ptr, streams),
                volread!(config_ptr, chmaps),
            )
        };
        info!(
            "[sound device] config: jacks: {}, streams: {}, chmaps: {}",
            jacks, streams, chmaps
        );

        let queue_buf_send = FromZeroes::new_box_slice_zeroed(PAGE_SIZE);
        let queue_buf_recv = FromZeroes::new_box_slice_zeroed(PAGE_SIZE);

        let output_rsp = FromZeroes::new_box_slice_zeroed(PAGE_SIZE);

        let event_buf = FromZeroes::new_box_slice_zeroed(PAGE_SIZE);

        // set pcm params to default
        let mut pcm_parameters = vec![];
        for _ in 0..streams {
            pcm_parameters.push(PcmParameters::default());
        }

        transport.finish_init();

        Ok(VirtIOSound {
            transport,
            control_queue,
            event_queue,
            tx_queue,
            rx_queue,
            negotiated_features,
            jacks,
            streams,
            chmaps,
            pcm_infos: None,
            jack_infos: None,
            chmap_infos: None,
            queue_buf_send,
            queue_buf_recv,
            pcm_parameters,
            set_up: false,
            output_rsp,
            event_buf,
            pcm_states: vec![],
        })
    }

    /// Total jack num.
    pub fn jacks(&self) -> u32 {
        self.jacks
    }

    /// Total stream num.
    pub fn streams(&self) -> u32 {
        self.streams
    }

    /// Total chmap num.
    pub fn chmaps(&self) -> u32 {
        self.chmaps
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

    /// Set up the driver, initate pcm_infos and jacks_infos
    fn set_up(&mut self) {
        // init jack info
        if let Ok(jack_infos) = self.jack_info(0, self.jacks) {
            for jack_info in &jack_infos {
                info!("[sound device] jack_info: {}", jack_info);
            }
            self.jack_infos = Some(jack_infos);
        } else {
            self.jack_infos = Some(vec![]);
            warn!("[sound device] There are no available jacks!");
        }
        // init pcm info
        if let Ok(pcm_infos) = self.pcm_info(0, self.streams) {
            for pcm_info in &pcm_infos {
                info!("[sound device] pcm_info: {}", pcm_info);
            }
            self.pcm_infos = Some(pcm_infos);
        } else {
            self.pcm_infos = Some(vec![]);
            warn!("[sound device] There are no available streams!");
        }
        // init chmap info
        if let Ok(chmap_infos) = self.chmap_info(0, self.chmaps) {
            for chmap_info in &chmap_infos {
                info!("[sound device] chmap_info: {}", chmap_info);
            }
            self.chmap_infos = Some(chmap_infos);
        } else {
            self.chmap_infos = Some(vec![]);
            warn!("[sound device] There are no available chmaps!");
        }
        // set pcm state to defalut
        for _ in 0..self.streams {
            self.pcm_states.push(PCMState::default());
        }
        self.event_queue.set_dev_notify(true);
    }

    /// Query information about the available jacks.
    fn jack_info(&mut self, jack_start_id: u32, jack_count: u32) -> Result<Vec<VirtIOSndJackInfo>> {
        if self.jacks == 0 {
            return Err(Error::ConfigSpaceTooSmall);
        }
        if jack_start_id + jack_count > self.jacks {
            error!("jack_start_id + jack_count > jacks! There are not enough jacks to be queried!");
            return Err(Error::IoError);
        }
        let hdr: VirtIOSndHdr = self.request(VirtIOSndQueryInfo {
            hdr: ItemInfomationRequestType::VirtioSndRJackInfo.into(),
            start_id: jack_start_id,
            count: jack_count,
            size: mem::size_of::<VirtIOSndJackInfo>() as u32,
        })?;
        // mem::size_of::<VirtIOSndHdr>() bytes are header
        if hdr != RequestStatusCode::VirtioSndSOk.into() {
            return Err(Error::IoError);
        }
        // read struct VirtIOSndJackInfo
        let mut jack_infos = vec![];
        for i in 0..jack_count as usize {
            const HDR_SIZE: usize = mem::size_of::<VirtIOSndHdr>();
            const JACK_INFO_SIZE: usize = mem::size_of::<VirtIOSndJackInfo>();
            let start_byte_idx = HDR_SIZE + i * JACK_INFO_SIZE;
            let end_byte_idx = HDR_SIZE + (i + 1) * JACK_INFO_SIZE;
            let jack_info =
                VirtIOSndJackInfo::read_from(&self.queue_buf_recv[start_byte_idx..end_byte_idx])
                    .unwrap();
            jack_infos.push(jack_info)
        }
        Ok(jack_infos)
    }

    /// Query information about the available streams.
    fn pcm_info(
        &mut self,
        stream_start_id: u32,
        stream_count: u32,
    ) -> Result<Vec<VirtIOSndPcmInfo>> {
        if self.streams == 0 {
            return Err(Error::ConfigSpaceTooSmall);
        }
        if stream_start_id + stream_count > self.streams {
            error!("stream_start_id + stream_count > streams! There are not enough streams to be queried!");
            return Err(Error::IoError);
        }
        let request_hdr = VirtIOSndHdr::from(ItemInfomationRequestType::VirtioSndRPcmInfo);
        let hdr: VirtIOSndHdr = self.request(VirtIOSndQueryInfo {
            hdr: request_hdr,
            start_id: stream_start_id,
            count: stream_count,
            size: mem::size_of::<VirtIOSndPcmInfo>() as u32,
        })?;
        // mem::size_of::<VirtIOSndHdr>() bytes are header
        if hdr != RequestStatusCode::VirtioSndSOk.into() {
            return Err(Error::IoError);
        }
        // read struct VirtIOSndPcmInfo
        let mut pcm_infos = vec![];
        for i in 0..stream_count as usize {
            const HDR_SIZE: usize = mem::size_of::<VirtIOSndHdr>();
            const PCM_INFO_SIZE: usize = mem::size_of::<VirtIOSndPcmInfo>();
            let start_byte_idx = HDR_SIZE + i * PCM_INFO_SIZE;
            let end_byte_idx = HDR_SIZE + (i + 1) * PCM_INFO_SIZE;
            let pcm_info =
                VirtIOSndPcmInfo::read_from(&self.queue_buf_recv[start_byte_idx..end_byte_idx])
                    .unwrap();
            pcm_infos.push(pcm_info);
        }
        Ok(pcm_infos)
    }

    /// Query information about the available chmaps.
    fn chmap_info(
        &mut self,
        chmaps_start_id: u32,
        chamaps_count: u32,
    ) -> Result<Vec<VirtIOSndChmapInfo>> {
        if self.chmaps == 0 {
            return Err(Error::ConfigSpaceTooSmall);
        }
        if chmaps_start_id + chamaps_count > self.chmaps {
            error!("chmaps_start_id + chamaps_count > self.chmaps");
            return Err(Error::IoError);
        }
        let hdr: VirtIOSndHdr = self.request(VirtIOSndQueryInfo {
            hdr: ItemInfomationRequestType::VirtioSndRChmapInfo.into(),
            start_id: chmaps_start_id,
            count: chamaps_count,
            size: mem::size_of::<VirtIOSndChmapInfo>() as u32,
        })?;
        if hdr != RequestStatusCode::VirtioSndSOk.into() {
            return Err(Error::IoError);
        }
        let mut chmap_infos = vec![];
        for i in 0..chamaps_count as usize {
            const OFFSET: usize = mem::size_of::<VirtIOSndHdr>();
            let start_byte = OFFSET + i * mem::size_of::<VirtIOSndChmapInfo>();
            let end_byte = OFFSET + (i + 1) * mem::size_of::<VirtIOSndChmapInfo>();
            let chmap_info =
                VirtIOSndChmapInfo::read_from(&self.queue_buf_recv[start_byte..end_byte]).unwrap();
            chmap_infos.push(chmap_info);
        }
        Ok(chmap_infos)
    }

    /// If the VIRTIO_SND_JACK_F_REMAP feature bit is set in the jack information, then the driver can send a
    /// control request to change the association and/or sequence number for the specified jack ID.
    /// # Arguments
    ///
    /// * `jack_id` - A u32 int which is in the range of [0, jacks)
    pub fn jack_remap(&mut self, jack_id: u32, association: u32, sequence: u32) -> Result {
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        if self.jacks == 0 {
            error!("[sound device] There is no available jacks!");
            return Err(Error::InvalidParam);
        }
        if self.jack_infos == None {
            error!("Could not read jack_infos, you need to call set_up() to initate it.");
            return Err(Error::InvalidParam);
        }
        if jack_id >= self.jacks {
            error!("jack_id >= self.jacks! Make sure jack_id is in the range of [0, jacks - 1)!");
            return Err(Error::InvalidParam);
        }

        let jack_features = JackFeatures::from(
            self.jack_infos
                .as_ref()
                .unwrap()
                .get(jack_id as usize)
                .unwrap()
                .features,
        );
        if !jack_features.contains(JackFeatures::VIRTIO_SND_JACK_F_REMAP) {
            // not support VIRTIO_SND_JACK_F_REMAP
            error!("The jack selected does not support VIRTIO_SND_JACK_F_REMAP!");
            return Err(Error::Unsupported);
        }
        let hdr: VirtIOSndHdr = self.request(VirtIOSndJackRemap {
            hdr: VirtIOSndJackHdr {
                hdr: CommandCode::VirtioSndRJackRemap.into(),
                jack_id,
            },
            association,
            sequence,
        })?;
        if hdr == RequestStatusCode::VirtioSndSOk.into() {
            Ok(())
        } else {
            Err(Error::Unsupported)
        }
    }

    /// Set selected stream parameters for the specified stream ID.
    pub fn pcm_set_params(
        &mut self,
        stream_id: u32,
        buffer_bytes: u32,
        period_bytes: u32,
        features: PcmFeatures,
        channels: u8,
        format: PcmFormats,
        rate: PcmRate,
    ) -> Result {
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        let request_hdr = VirtIOSndHdr::from(CommandCode::VirtioSndRPcmSetParams);
        let rsp: VirtIOSndHdr = self.request(VirtIOSndPcmSetParams {
            hdr: VirtIOSndPcmHdr {
                hdr: request_hdr,
                stream_id,
            },
            buffer_bytes,
            period_bytes,
            features: features.into(),
            channels,
            format: format.into(),
            rate: rate.into(),
            _padding: 0,
        })?;
        // rsp is just a header, so it can be compared with VirtIOSndHdr
        if rsp == VirtIOSndHdr::from(RequestStatusCode::VirtioSndSOk) {
            self.pcm_parameters[stream_id as usize] = PcmParameters {
                setup: true,
                buffer_bytes,
                period_bytes,
                features,
                channels,
                format,
                rate,
            };
            Ok(())
        } else {
            Err(Error::IoError)
        }
    }

    /// Prepare a stream with specified stream ID.
    pub fn pcm_prepare(&mut self, stream_id: u32) -> Result {
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        let request_hdr = VirtIOSndHdr::from(CommandCode::VirtioSndRPcmPrepare);
        let rsp: VirtIOSndHdr = self.request(VirtIOSndPcmHdr {
            hdr: request_hdr,
            stream_id,
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
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        let request_hdr = VirtIOSndHdr::from(CommandCode::VirtioSndRPcmRelease);
        let rsp: VirtIOSndHdr = self.request(VirtIOSndPcmHdr {
            hdr: request_hdr,
            stream_id,
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
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        let request_hdr = VirtIOSndHdr::from(CommandCode::VirtioSndRPcmStart);
        let rsp: VirtIOSndHdr = self.request(VirtIOSndPcmHdr {
            hdr: request_hdr,
            stream_id,
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
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        let request_hdr = VirtIOSndHdr::from(CommandCode::VirtioSndRPcmStop);
        let rsp: VirtIOSndHdr = self.request(VirtIOSndPcmHdr {
            hdr: request_hdr,
            stream_id,
        })?;
        // rsp is just a header, so it can be compared with VirtIOSndHdr
        if rsp == VirtIOSndHdr::from(RequestStatusCode::VirtioSndSOk) {
            Ok(())
        } else {
            Err(Error::IoError)
        }
    }

    /// Transfer PCM frame to device, based on the stream type(OUTPUT/INPUT).
    /// TODO: if frames.len() is to short, the func with generate a error.
    pub fn pcm_xfer(&mut self, stream_id: u32, frames: &[u8]) -> Result {
        const U32_SIZE: usize = mem::size_of::<u32>();
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        if !self.pcm_parameters[stream_id as usize].setup {
            warn!("Please set parameters for a stream before using it!");
            return Err(Error::IoError);
        }
        let buffer_size = self.pcm_parameters[stream_id as usize].buffer_bytes as usize;
        // TODO
        assert!(buffer_size * 2 <= frames.len());
        let mut buf1 = vec![0; U32_SIZE + buffer_size];
        let mut buf2 = vec![0; U32_SIZE + buffer_size];

        buf1[..U32_SIZE].copy_from_slice(&stream_id.to_le_bytes());
        buf1[U32_SIZE..U32_SIZE + buffer_size]
            .copy_from_slice(&frames[..buffer_size]);

        buf2[..U32_SIZE].copy_from_slice(&stream_id.to_le_bytes());
        buf2[U32_SIZE..U32_SIZE + buffer_size]
            .copy_from_slice(&frames[buffer_size..buffer_size * 2]);

        let mut outputs = vec![0; 32];
        let mut token1 = unsafe { self.tx_queue.add(&[&buf1], &mut [&mut outputs]).unwrap() };
        let mut token2 = unsafe { self.tx_queue.add(&[&buf2], &mut [&mut outputs]).unwrap() };

        let xfer_times = if frames.len() % buffer_size == 0 {
            frames.len() / buffer_size
        } else {
            frames.len() / buffer_size + 1
        };

        let mut turn1 = true;

        for i in 2..xfer_times {
            if self.tx_queue.should_notify() {
                self.transport.notify(TX_QUEUE_IDX);
            }

            let start_byte = i * buffer_size;
            let end_byte = if i != xfer_times - 1 {
                (i + 1) * buffer_size
            } else {
                frames.len()
            };
            if turn1 {
                while let Err(_) = unsafe {
                    self.tx_queue
                        .pop_used(token1, &[&buf1], &mut [&mut outputs])
                } {
                    spin_loop();
                }
                turn1 = false;
                buf1[U32_SIZE..U32_SIZE + end_byte - start_byte]
                    .copy_from_slice(&frames[start_byte..end_byte]);
                token1 = unsafe { self.tx_queue.add(&[&buf1], &mut [&mut outputs]).unwrap() }
            } else {
                while let Err(_) = unsafe {
                    self.tx_queue
                        .pop_used(token2, &[&buf2], &mut [&mut outputs])
                } {
                    spin_loop();
                }
                turn1 = true;
                buf2[U32_SIZE..U32_SIZE + end_byte - start_byte]
                    .copy_from_slice(&frames[start_byte..end_byte]);
                token2 = unsafe { self.tx_queue.add(&[&buf2], &mut [&mut outputs]).unwrap() }
            }
        }
        // wait for the last buffer
        if turn1 {
            while let Err(_) = unsafe {
                self.tx_queue
                    .pop_used(token1, &[&buf1], &mut [&mut outputs])
            } {
                spin_loop();
            }
        } else {
            while let Err(_) = unsafe {
                self.tx_queue
                    .pop_used(token2, &[&buf2], &mut [&mut outputs])
            } {
                spin_loop();
            }
        }
        Ok(())
    }

    ///
    pub fn pcm_xfer_wait(&mut self, io_request: &[u8]) -> Result {
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        self.tx_queue.add_notify_wait_pop(
            &[&io_request],
            &mut [&mut self.output_rsp],
            &mut self.transport,
        )?;
        Ok(())
    }

    /// Get all output streams.
    pub fn output_streams(&mut self) -> Vec<u32> {
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        self.pcm_infos
            .as_ref()
            .unwrap()
            .iter()
            .enumerate()
            .filter(|(_, info)| info.direction == VIRTIO_SND_D_OUTPUT)
            .map(|(idx, _)| idx as u32)
            .collect()
    }

    /// Get all input streams.
    pub fn input_streams(&mut self) -> Vec<u32> {
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        self.pcm_infos
            .as_ref()
            .unwrap()
            .iter()
            .enumerate()
            .filter(|(_, info)| info.direction == VIRTIO_SND_D_INPUT)
            .map(|(idx, _)| idx as u32)
            .collect()
    }

    /// Get the rates that a stream supports.
    pub fn rates_supported(&mut self, stream_id: u32) -> Result<PcmRate> {
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        if stream_id >= self.pcm_infos.as_ref().unwrap().len() as u32 {
            return Err(Error::InvalidParam);
        }
        Ok(self.pcm_infos.as_ref().unwrap()[stream_id as usize]
            .rate
            .into())
    }

    /// Get the formats that a stream supports.
    pub fn formats_supported(&mut self, stream_id: u32) -> Result<PcmFormats> {
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        if stream_id >= self.pcm_infos.as_ref().unwrap().len() as u32 {
            return Err(Error::InvalidParam);
        }
        Ok(self.pcm_infos.as_ref().unwrap()[stream_id as usize]
            .formats
            .into())
    }

    /// Get channel range that a stream supports.
    pub fn channel_range_supported(&mut self, stream_id: u32) -> Result<RangeInclusive<u8>> {
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        if stream_id >= self.pcm_infos.as_ref().unwrap().len() as u32 {
            return Err(Error::InvalidParam);
        }
        let pcm_info = &self.pcm_infos.as_ref().unwrap()[stream_id as usize];
        Ok(pcm_info.channels_min..=pcm_info.channels_max)
    }

    /// Get features that a stream supports.
    pub fn features_supported(&mut self, stream_id: u32) -> Result<PcmFeatures> {
        if !self.set_up {
            self.set_up();
            self.set_up = true;
        }
        if stream_id >= self.pcm_infos.as_ref().unwrap().len() as u32 {
            return Err(Error::InvalidParam);
        }
        let pcm_info = &self.pcm_infos.as_ref().unwrap()[stream_id as usize];
        Ok(pcm_info.features.into())
    }

    /// Get the latest notification.
    pub fn latest_notification(&mut self) -> Result<Notification> {
        if let Some(token) = self.event_queue.peek_used() {
            unsafe {
                self.event_queue
                    .pop_used(token, &[], &mut [&mut self.event_buf])?;
            }
        } else {
            info!("Not ready");
            return Err(Error::NotReady);
        }
        let event = VirtIOSndEvent::read_from_prefix(&self.event_buf).unwrap();
        Ok(Notification {
            notification_type: NotificationType::from(event.hdr.command_code),
            data: event.data,
        })
    }
}

/// TODO
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
    InvalidState(&'static str, PCMState),
    InvalidStateTransition(PCMState, PCMState),
    InvalidStreamId(u32),
    DescriptorReadFailed,
    DescriptorWriteFailed,
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

const QUEUE_SIZE: u16 = 32;
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

struct JackFeatures(u32);

bitflags! {
    impl JackFeatures: u32 {
        /// jack remapping support.
        const VIRTIO_SND_JACK_F_REMAP = 1 << 0;
    }
}

impl From<u32> for JackFeatures {
    fn from(value: u32) -> Self {
        JackFeatures(value)
    }
}

/// TODO
#[derive(Clone, Copy)]
pub struct PcmFeatures(u32);

bitflags! {
    impl PcmFeatures: u32 {
        /// TODO
        const VIRTIO_SND_PCM_F_SHMEM_HOST = 1 << 0;
        /// TODO
        const VIRTIO_SND_PCM_F_SHMEM_GUEST = 1 << 1;
        /// TODO
        const VIRTIO_SND_PCM_F_MSG_POLLING = 1 << 2;
        /// TODO
        const VIRTIO_SND_PCM_F_EVT_SHMEM_PERIODS = 1 << 3;
        /// TODO
        const VIRTIO_SND_PCM_F_EVT_XRUNS = 1 << 4;
    }
}

impl From<u32> for PcmFeatures {
    fn from(value: u32) -> Self {
        PcmFeatures(value)
    }
}

impl Into<u32> for PcmFeatures {
    fn into(self) -> u32 {
        self.0
    }
}

/// TODO
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct PcmFormats(u64);

bitflags! {
    impl PcmFormats: u64 {
        /* analog formats (width / physical width) */
        /// TODO
        const VIRTIO_SND_PCM_FMT_IMA_ADPCM = 1 << 0;
        /// TODO
        const VIRTIO_SND_PCM_FMT_MU_LAW = 1 << 1;
        /// TODO
        const VIRTIO_SND_PCM_FMT_A_LAW = 1 << 2;
        /// TODO
        const VIRTIO_SND_PCM_FMT_S8 = 1 << 3;
        /// TODO
        const VIRTIO_SND_PCM_FMT_U8 = 1 << 4;
        /// TODO
        const VIRTIO_SND_PCM_FMT_S16 = 1 << 5;
        /// TODO
        const VIRTIO_SND_PCM_FMT_U16 = 1 << 6;
        /// TODO
        const VIRTIO_SND_PCM_FMT_S18_3 = 1 << 7;
        /// TODO
        const VIRTIO_SND_PCM_FMT_U18_3 = 1 << 8;
        /// TODO
        const VIRTIO_SND_PCM_FMT_S20_3 = 1 << 9;
        /// TODO
        const VIRTIO_SND_PCM_FMT_U20_3 = 1 << 10;
        /// TODO
        const VIRTIO_SND_PCM_FMT_S24_3 = 1 << 11;
        /// TODO
        const VIRTIO_SND_PCM_FMT_U24_3 = 1 << 12;
        /// TODO
        const VIRTIO_SND_PCM_FMT_S20 = 1 << 13;
        /// TODO
        const VIRTIO_SND_PCM_FMT_U20 = 1 << 14;
        /// TODO
        const VIRTIO_SND_PCM_FMT_S24 = 1 << 15;
        /// TODO
        const VIRTIO_SND_PCM_FMT_U24 = 1 << 16;
        /// TODO
        const VIRTIO_SND_PCM_FMT_S32 = 1 << 17;
        /// TODO
        const VIRTIO_SND_PCM_FMT_U32 = 1 << 18;
        /// TODO
        const VIRTIO_SND_PCM_FMT_FLOAT = 1 << 19;
        /// TODO
        const VIRTIO_SND_PCM_FMT_FLOAT64 = 1 << 20;
        /* digital formats (width / physical width) */
        /// TODO
        const VIRTIO_SND_PCM_FMT_DSD_U8 = 1 << 21;
        /// TODO
        const VIRTIO_SND_PCM_FMT_DSD_U16 = 1 << 22;
        /// TODO
        const VIRTIO_SND_PCM_FMT_DSD_U32 = 1 << 23;
        /// TODO
        const VIRTIO_SND_PCM_FMT_IEC958_SUBFRAME = 1 << 24;

    }
}

impl From<u64> for PcmFormats {
    fn from(value: u64) -> Self {
        PcmFormats(value)
    }
}

impl Into<u8> for PcmFormats {
    fn into(self) -> u8 {
        match self {
            PcmFormats::VIRTIO_SND_PCM_FMT_IMA_ADPCM => 0,
            PcmFormats::VIRTIO_SND_PCM_FMT_MU_LAW => 1,
            PcmFormats::VIRTIO_SND_PCM_FMT_A_LAW => 2,
            PcmFormats::VIRTIO_SND_PCM_FMT_S8 => 3,
            PcmFormats::VIRTIO_SND_PCM_FMT_U8 => 4,
            PcmFormats::VIRTIO_SND_PCM_FMT_S16 => 5,
            PcmFormats::VIRTIO_SND_PCM_FMT_U16 => 6,
            PcmFormats::VIRTIO_SND_PCM_FMT_S18_3 => 7,
            PcmFormats::VIRTIO_SND_PCM_FMT_U18_3 => 8,
            PcmFormats::VIRTIO_SND_PCM_FMT_S20_3 => 9,
            PcmFormats::VIRTIO_SND_PCM_FMT_U20_3 => 10,
            PcmFormats::VIRTIO_SND_PCM_FMT_S24_3 => 11,
            PcmFormats::VIRTIO_SND_PCM_FMT_U24_3 => 12,
            PcmFormats::VIRTIO_SND_PCM_FMT_S20 => 13,
            PcmFormats::VIRTIO_SND_PCM_FMT_U20 => 14,
            PcmFormats::VIRTIO_SND_PCM_FMT_S24 => 15,
            PcmFormats::VIRTIO_SND_PCM_FMT_U24 => 16,
            PcmFormats::VIRTIO_SND_PCM_FMT_S32 => 17,
            PcmFormats::VIRTIO_SND_PCM_FMT_U32 => 18,
            PcmFormats::VIRTIO_SND_PCM_FMT_FLOAT => 19,
            PcmFormats::VIRTIO_SND_PCM_FMT_FLOAT64 => 20,
            PcmFormats::VIRTIO_SND_PCM_FMT_DSD_U8 => 21,
            PcmFormats::VIRTIO_SND_PCM_FMT_DSD_U16 => 22,
            PcmFormats::VIRTIO_SND_PCM_FMT_DSD_U32 => 23,
            PcmFormats::VIRTIO_SND_PCM_FMT_IEC958_SUBFRAME => 24,
            _ => 0,
        }
    }
}

/// TODO
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct PcmRate(u64);

bitflags! {
    impl PcmRate: u64 {
        /// TODO
        const VIRTIO_SND_PCM_RATE_5512 = 1 << 0;
        /// TODO
        const VIRTIO_SND_PCM_RATE_8000 = 1 << 1;
        /// TODO
        const VIRTIO_SND_PCM_RATE_11025 = 1 << 2;
        /// TODO
        const VIRTIO_SND_PCM_RATE_16000 = 1 << 3;
        /// TODO
        const VIRTIO_SND_PCM_RATE_22050 = 1 << 4;
        /// TODO
        const VIRTIO_SND_PCM_RATE_32000 = 1 << 5;
        /// TODO
        const VIRTIO_SND_PCM_RATE_44100 = 1 << 6;
        /// TODO
        const VIRTIO_SND_PCM_RATE_48000 = 1 << 7;
        /// TODO
        const VIRTIO_SND_PCM_RATE_64000 = 1 << 8;
        /// TODO
        const VIRTIO_SND_PCM_RATE_88200 = 1 << 9;
        /// TODO
        const VIRTIO_SND_PCM_RATE_96000 = 1 << 10;
        /// TODO
        const VIRTIO_SND_PCM_RATE_176400 = 1 << 11;
        /// TODO
        const VIRTIO_SND_PCM_RATE_192000 = 1 << 12;
        /// TODO
        const VIRTIO_SND_PCM_RATE_384000 = 1 << 13;
    }
}

impl From<u64> for PcmRate {
    fn from(value: u64) -> Self {
        PcmRate(value)
    }
}

impl From<PcmRate> for u8 {
    fn from(value: PcmRate) -> Self {
        match value {
            PcmRate::VIRTIO_SND_PCM_RATE_5512 => 0,
            PcmRate::VIRTIO_SND_PCM_RATE_8000 => 1,
            PcmRate::VIRTIO_SND_PCM_RATE_11025 => 2,
            PcmRate::VIRTIO_SND_PCM_RATE_16000 => 3,
            PcmRate::VIRTIO_SND_PCM_RATE_22050 => 4,
            PcmRate::VIRTIO_SND_PCM_RATE_32000 => 5,
            PcmRate::VIRTIO_SND_PCM_RATE_44100 => 6,
            PcmRate::VIRTIO_SND_PCM_RATE_48000 => 7,
            PcmRate::VIRTIO_SND_PCM_RATE_64000 => 8,
            PcmRate::VIRTIO_SND_PCM_RATE_88200 => 9,
            PcmRate::VIRTIO_SND_PCM_RATE_96000 => 10,
            PcmRate::VIRTIO_SND_PCM_RATE_176400 => 11,
            PcmRate::VIRTIO_SND_PCM_RATE_192000 => 12,
            PcmRate::VIRTIO_SND_PCM_RATE_384000 => 13,
            _ => 0,
        }
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
        VirtIOSndHdr {
            command_code: value as _,
        }
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

impl Into<u32> for ItemInfomationRequestType {
    fn into(self) -> u32 {
        self as _
    }
}

#[derive(IntoPrimitive)]
#[repr(u32)]
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
#[derive(FromBytes, FromZeroes)]
/// An event notification
struct VirtIOSndEvent {
    hdr: VirtIOSndHdr,
    data: u32,
}

/// The notification type.
#[repr(u32)]
#[derive(FromPrimitive, Copy, Clone)]
pub enum NotificationType {
    /// TODO
    #[num_enum(default)]
    PcmPeriodElapsed = 0x1100,
    /// TODO
    PcmXrun,
    /// TODO
    JackConnected = 0x1000,
    /// TODO
    JackDisconnected,
}

/// Notification from sound device.
pub struct Notification {
    notification_type: NotificationType,
    data: u32,
}

impl Notification {
    /// Get the resource index.
    pub fn data(&self) -> u32 {
        self.data
    }

    /// Get the notification type.
    pub fn notification_type(&self) -> NotificationType {
        self.notification_type
    }
}

const VIRTIO_SND_D_OUTPUT: u8 = 0;
const VIRTIO_SND_D_INPUT: u8 = 1;

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
    info: VirtIOSndInfo,
}

/// TODO: Add docs
#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes, Debug, PartialEq, Eq)]
pub struct VirtIOSndInfo {
    hda_fn_nid: u32,
}

#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
struct VirtIOSndJackHdr {
    hdr: VirtIOSndHdr,
    /// specifies a jack identifier from 0 to jacks - 1
    jack_id: u32,
}

/// TODO
#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes, PartialEq, Eq)]
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

impl Display for VirtIOSndJackInfo {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let jack_features = JackFeatures::from(self.features);
        let mut jack_features_str = String::new();
        bitflags::parser::to_writer(&jack_features, &mut jack_features_str).unwrap();
        let connected_status = if self.connected == 1 {
            "CONNECTED"
        } else {
            "DISCONNECTED"
        };
        write!(
            f,
            "features: {}, hda_reg_defconf: {}, hda_reg_caps: {}, connected: {}",
            jack_features_str, self.hda_reg_defconf, self.hda_reg_caps, connected_status
        )
    }
}

#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
struct VirtIOSndJackInfoRsp {
    hdr: VirtIOSndHdr,
    body: VirtIOSndJackInfo,
}

#[repr(C)]
#[derive(AsBytes, FromBytes, FromZeroes)]
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

impl Into<u64> for PcmFrameRate {
    fn into(self) -> u64 {
        1 << self as usize
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

impl Display for VirtIOSndPcmInfo {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut features = String::new();
        bitflags::parser::to_writer(&PcmFeatures::from(self.features), &mut features).unwrap();
        let mut rates = String::new();
        let _ = bitflags::parser::to_writer(&PcmRate::from(self.rate), &mut rates).unwrap();
        let mut formats = String::new();
        let _ = bitflags::parser::to_writer(&PcmFormats::from(self.formats), &mut formats).unwrap();
        let direction = if self.direction == VIRTIO_SND_D_INPUT {
            "INPUT"
        } else {
            "OUTPUT"
        };
        write!(
            f,
            "features: {}, rates: {}, formats: {}, direction: {}",
            features, rates, formats, direction
        )
    }
}

struct PcmParameters {
    setup: bool,
    buffer_bytes: u32,
    period_bytes: u32,
    features: PcmFeatures,
    channels: u8,
    format: PcmFormats,
    rate: PcmRate,
}

impl Default for PcmParameters {
    fn default() -> Self {
        Self {
            setup: false,
            buffer_bytes: Default::default(),
            period_bytes: Default::default(),
            features: PcmFeatures(0),
            channels: Default::default(),
            format: PcmFormats(0),
            rate: PcmRate(0),
        }
    }
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
#[derive(AsBytes)]
struct VirtIOSndPcmXfer {
    srteam_id: u32,
}

/// An I/O status
#[repr(C)]
#[derive(FromBytes, FromZeroes)]
struct VirtIOSndPcmStatus {
    status: u32,
    latency_bytes: u32,
}

#[derive(FromPrimitive, Debug)]
#[repr(u8)]
enum ChannelPosition {
    #[num_enum(default)]
    VirtioSndChmapNone = 0, /* undefined */
    VirtioSndChmapNa,   /* silent */
    VirtioSndChmapMono, /* mono stream */
    VirtioSndChmapFl,   /* front left */
    VirtioSndChmapFr,   /* front right */
    VirtioSndChmapRl,   /* rear left */
    VirtioSndChmapRr,   /* rear right */
    VirtioSndChmapFc,   /* front center */
    VirtioSndChmapLfe,  /* low frequency (LFE) */
    VirtioSndChmapSl,   /* side left */
    VirtioSndChmapSr,   /* side right */
    VirtioSndChmapRc,   /* rear center */
    VirtioSndChmapFlc,  /* front left center */
    VirtioSndChmapFrc,  /* front right center */
    VirtioSndChmapRlc,  /* rear left center */
    VirtioSndChmapRrc,  /* rear right center */
    VirtioSndChmapFlw,  /* front left wide */
    VirtioSndChmapFrw,  /* front right wide */
    VirtioSndChmapFlh,  /* front left high */
    VirtioSndChmapFch,  /* front center high */
    VirtioSndChmapFrh,  /* front right high */
    VirtioSndChmapTc,   /* top center */
    VirtioSndChmapTfl,  /* top front left */
    VirtioSndChmapTfr,  /* top front right */
    VirtioSndChmapTfc,  /* top front center */
    VirtioSndChmapTrl,  /* top rear left */
    VirtioSndChmapTrr,  /* top rear right */
    VirtioSndChmapTrc,  /* top rear center */
    VirtioSndChmapTflc, /* top front left center */
    VirtioSndChmapTfrc, /* top front right center */
    VirtioSndChmapTsl,  /* top side left */
    VirtioSndChmapTsr,  /* top side right */
    VirtioSndChmapLlfe, /* left LFE */
    VirtioSndChmapRlfe, /* right LFE */
    VirtioSndChmapBc,   /* bottom center */
    VirtioSndChmapBlc,  /* bottom left center */
    VirtioSndChmapBrc,  /* bottom right center */
}

/// maximum possible number of channels
const VIRTIO_SND_CHMAP_MAX_SIZE: usize = 18;

#[repr(C)]
#[derive(FromBytes, FromZeroes)]
struct VirtIOSndChmapInfo {
    hdr: VirtIOSndInfo,
    direction: u8,
    channels: u8,
    positions: [u8; VIRTIO_SND_CHMAP_MAX_SIZE],
}

impl Display for VirtIOSndChmapInfo {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let direction = if self.direction == VIRTIO_SND_D_INPUT {
            "INPUT"
        } else {
            "OUTPUT"
        };
        let mut positions = vec![];
        for i in 0..self.channels as usize {
            let position = format!("{:?}", ChannelPosition::from(self.positions[i]));
            positions.push(position);
        }
        write!(
            f,
            "direction: {}, channels: {}, postions: {:?}",
            direction, self.channels, positions
        )
    }
}
