//! Fake VirtIO sound device for tests.

use super::{
    CommandCode, VirtIOSndChmapInfo, VirtIOSndHdr, VirtIOSndJackInfo, VirtIOSndPcmInfo,
    VirtIOSndQueryInfo, VirtIOSoundConfig, CONTROL_QUEUE_IDX, QUEUE_SIZE,
};
use crate::{
    transport::{
        fake::{FakeTransport, QueueStatus, State},
        DeviceType,
    },
    volatile::ReadOnly,
};
use alloc::{sync::Arc, vec};
use core::{
    convert::{TryFrom, TryInto},
    mem::size_of,
    ptr::NonNull,
    time::Duration,
};
use std::{
    sync::{
        atomic::{AtomicBool, Ordering},
        Mutex,
    },
    thread::{self, JoinHandle},
};
use zerocopy::{AsBytes, FromBytes};

#[derive(Clone, Debug)]
pub struct FakeSoundDevice {
    pub state: Arc<Mutex<State>>,
    pub terminate: Arc<AtomicBool>,
    pub jack_infos: Vec<VirtIOSndJackInfo>,
    pub pcm_infos: Vec<VirtIOSndPcmInfo>,
    pub chmap_infos: Vec<VirtIOSndChmapInfo>,
}

impl FakeSoundDevice {
    pub fn new(
        jack_infos: Vec<VirtIOSndJackInfo>,
        pcm_infos: Vec<VirtIOSndPcmInfo>,
        chmap_infos: Vec<VirtIOSndChmapInfo>,
    ) -> (Self, FakeTransport<VirtIOSoundConfig>) {
        let mut config_space = VirtIOSoundConfig {
            jacks: ReadOnly::new(jack_infos.len().try_into().unwrap()),
            streams: ReadOnly::new(pcm_infos.len().try_into().unwrap()),
            chmaps: ReadOnly::new(chmap_infos.len().try_into().unwrap()),
        };
        let state = Arc::new(Mutex::new(State {
            queues: vec![
                QueueStatus::default(),
                QueueStatus::default(),
                QueueStatus::default(),
                QueueStatus::default(),
            ],
            ..Default::default()
        }));
        let transport = FakeTransport {
            device_type: DeviceType::Socket,
            max_queue_size: 32,
            device_features: 0,
            config_space: NonNull::from(&mut config_space),
            state: state.clone(),
        };

        (
            Self {
                state,
                terminate: Arc::new(AtomicBool::new(false)),
                jack_infos,
                pcm_infos,
                chmap_infos,
            },
            transport,
        )
    }

    /// Start a background thread simulating the device.
    pub fn spawn(&self) -> JoinHandle<()> {
        let clone = self.clone();
        thread::spawn(move || clone.run())
    }

    /// Terminate the background thread for the device.
    pub fn terminate(&self) {
        self.terminate.store(true, Ordering::Release);
    }

    fn run(&self) {
        while !self.terminate.load(Ordering::Acquire) {
            if State::poll_queue_notified(&self.state, CONTROL_QUEUE_IDX) {
                println!("Control queue was notified.");

                self.state
                    .lock()
                    .unwrap()
                    .read_write_queue::<{ QUEUE_SIZE as usize }>(CONTROL_QUEUE_IDX, |request| {
                        self.handle_control_request(&request)
                    })
            } else {
                thread::sleep(Duration::from_millis(10));
            }
        }
    }

    fn handle_control_request(&self, request: &[u8]) -> Vec<u8> {
        {
            let header =
                VirtIOSndHdr::read_from_prefix(&request).expect("Control request too short");
            let mut response = Vec::new();
            const RJACKINFO: u32 = CommandCode::RJackInfo as u32;
            const RPCMINFO: u32 = CommandCode::RPcmInfo as u32;
            const RCHMAPINFO: u32 = CommandCode::RChmapInfo as u32;
            match header.command_code {
                RJACKINFO => {
                    let request = VirtIOSndQueryInfo::read_from(&request)
                        .expect("RJackInfo control request wrong length");
                    assert_eq!(
                        request.size,
                        u32::try_from(size_of::<VirtIOSndJackInfo>()).unwrap()
                    );
                    response.extend_from_slice(
                        VirtIOSndHdr {
                            command_code: CommandCode::SOk.into(),
                        }
                        .as_bytes(),
                    );
                    for jack_info in &self.jack_infos[request.start_id as usize
                        ..request.start_id as usize + request.count as usize]
                    {
                        response.extend_from_slice(jack_info.as_bytes());
                    }
                }
                RPCMINFO => {
                    let request = VirtIOSndQueryInfo::read_from(&request)
                        .expect("RPcmInfo control request wrong length");
                    assert_eq!(
                        request.size,
                        u32::try_from(size_of::<VirtIOSndPcmInfo>()).unwrap()
                    );
                    response.extend_from_slice(
                        VirtIOSndHdr {
                            command_code: CommandCode::SOk.into(),
                        }
                        .as_bytes(),
                    );
                    for pcm_info in &self.pcm_infos[request.start_id as usize
                        ..request.start_id as usize + request.count as usize]
                    {
                        response.extend_from_slice(pcm_info.as_bytes());
                    }
                }
                RCHMAPINFO => {
                    let request = VirtIOSndQueryInfo::read_from(&request)
                        .expect("RJackInfo control request wrong length");
                    assert_eq!(
                        request.size,
                        u32::try_from(size_of::<VirtIOSndChmapInfo>()).unwrap()
                    );
                    response.extend_from_slice(
                        VirtIOSndHdr {
                            command_code: CommandCode::SOk.into(),
                        }
                        .as_bytes(),
                    );
                    for chmap_info in &self.chmap_infos[request.start_id as usize
                        ..request.start_id as usize + request.count as usize]
                    {
                        response.extend_from_slice(chmap_info.as_bytes());
                    }
                }
                _ => {
                    panic!("Unexpected control request, header {:?}", header);
                }
            }
            response
        }
    }
}
