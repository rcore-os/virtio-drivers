use super::*;
use alloc::boxed::Box;
use bitflags::*;
use log::*;
use volatile::Volatile;

/// Virtual human interface devices such as keyboards, mice and tablets.
///
/// An instance of the virtio device represents one such input device.
/// Device behavior mirrors that of the evdev layer in Linux,
/// making pass-through implementations on top of evdev easy.
pub struct VirtIOInput<'a> {
    header: &'static mut VirtIOHeader,
    event_queue: VirtQueue<'a>,
    status_queue: VirtQueue<'a>,
    event_buf: Box<[InputEvent; 32]>,
}

impl<'a> VirtIOInput<'a> {
    /// Create a new VirtIO-Input driver.
    pub fn new(header: &'static mut VirtIOHeader) -> Result<Self> {
        let mut event_buf = Box::new([InputEvent::default(); QUEUE_SIZE]);
        header.begin_init(|features| {
            let features = Feature::from_bits_truncate(features);
            info!("Device features: {:?}", features);
            // negotiate these flags only
            let supported_features = Feature::empty();
            (features & supported_features).bits()
        });

        // read configuration space
        let config = unsafe { &mut *(header.config_space() as *mut Config) };
        info!("Config: {:?}", config);

        let mut event_queue = VirtQueue::new(header, QUEUE_EVENT, QUEUE_SIZE as u16)?;
        let status_queue = VirtQueue::new(header, QUEUE_STATUS, QUEUE_SIZE as u16)?;
        for (i, event) in event_buf.as_mut().iter_mut().enumerate() {
            let token = event_queue.add(&[], &[event.as_buf_mut()])?;
            assert_eq!(token, i as u16);
        }

        header.finish_init();

        Ok(VirtIOInput {
            header,
            event_queue,
            status_queue,
            event_buf,
        })
    }

    /// Acknowledge interrupt and process events.
    pub fn ack_interrupt(&mut self) -> bool {
        self.header.ack_interrupt()
    }

    /// Pop the pending event.
    pub fn pop_pending_event(&mut self) -> Option<InputEvent> {
        if let Ok((token, _)) = self.event_queue.pop_used() {
            let event = &mut self.event_buf[token as usize];
            // requeue
            if self.event_queue.add(&[], &[event.as_buf_mut()]).is_ok() {
                return Some(*event);
            }
        }
        None
    }
}

#[repr(u8)]
#[derive(Debug)]
enum Cfg {
    Unset = 0x00,
    IdName = 0x01,
    IdSerial = 0x02,
    IdDevids = 0x03,
    PropBits = 0x10,
    EvBits = 0x11,
    AbsInfo = 0x12,
}

#[repr(C)]
#[derive(Debug)]
struct Config {
    select: Volatile<u8>,
    subsel: Volatile<u8>,
    size: u8,
    reversed: [u8; 5],
    data: [u8; 32],
}

#[repr(C)]
#[derive(Debug)]
struct AbsInfo {
    min: u32,
    max: u32,
    fuzz: u32,
    flat: u32,
    res: u32,
}

#[repr(C)]
#[derive(Debug)]
struct DevIDs {
    bustype: u16,
    vendor: u16,
    product: u16,
    version: u16,
}

/// Both queues use the same `virtio_input_event` struct. `type`, `code` and `value`
/// are filled according to the Linux input layer (evdev) interface.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct InputEvent {
    /// Event type.
    pub event_type: u16,
    /// Event code.
    pub code: u16,
    /// Event value.
    pub value: u32,
}

unsafe impl AsBuf for InputEvent {}

bitflags! {
    struct Feature: u64 {
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

const QUEUE_EVENT: usize = 0;
const QUEUE_STATUS: usize = 1;

// a parameter that can change
const QUEUE_SIZE: usize = 32;
