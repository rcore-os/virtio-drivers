use super::*;
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
    event_buf: &'a mut [Event],
    x: i32,
    y: i32,
}

impl<'a> VirtIOInput<'a> {
    /// Create a new VirtIO-Input driver.
    pub fn new(header: &'static mut VirtIOHeader, event_buf: &'a mut [u64]) -> Result<Self> {
        if event_buf.len() < QUEUE_SIZE {
            return Err(Error::BufferTooSmall);
        }
        let event_buf: &mut [Event] = unsafe { core::mem::transmute(event_buf) };
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
        for (i, event) in event_buf.iter_mut().enumerate() {
            let token = event_queue.add(&[], &[event.as_buf_mut()])?;
            assert_eq!(token, i as u16);
        }

        header.finish_init();

        Ok(VirtIOInput {
            header,
            event_queue,
            status_queue,
            event_buf,
            x: 0,
            y: 0,
        })
    }

    /// Acknowledge interrupt and process events.
    pub fn ack_interrupt(&mut self) -> Result<bool> {
        let ack = self.header.ack_interrupt();
        if !ack {
            return Ok(false);
        }
        while let Ok((token, _)) = self.event_queue.pop_used() {
            let event = &mut self.event_buf[token as usize];
            match EventRepr::from(*event) {
                EventRepr::RelX(dx) => self.x += dx,
                EventRepr::RelY(dy) => self.y += dy,
                r => warn!("{:?}", r),
            }
            // requeue
            self.event_queue.add(&[], &[event.as_buf_mut()])?;
        }
        Ok(true)
    }

    /// Get the coordinate of mouse.
    pub fn mouse_xy(&self) -> (i32, i32) {
        (self.x, self.y)
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

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct Event {
    event_type: u16,
    code: u16,
    value: u32,
}

#[derive(Debug)]
enum EventRepr {
    SynReport,
    SynUnknown(u16),
    RelX(i32),
    RelY(i32),
    RelUnknown(u16),
    Unknown(u16),
}

unsafe impl AsBuf for Event {}

impl From<Event> for EventRepr {
    fn from(e: Event) -> Self {
        // linux event codes
        match e.event_type {
            0 => match e.code {
                0 => EventRepr::SynReport,
                _ => EventRepr::SynUnknown(e.code),
            },
            2 => match e.code {
                0 => EventRepr::RelX(e.value as i32),
                1 => EventRepr::RelY(e.value as i32),
                _ => EventRepr::RelUnknown(e.code),
            },
            _ => EventRepr::Unknown(e.event_type),
        }
    }
}

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
