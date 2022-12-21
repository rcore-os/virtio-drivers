use super::*;
use crate::queue::VirtQueue;
use crate::transport::Transport;
use crate::volatile::{volread, ReadOnly, WriteOnly};
use bitflags::*;
use core::ptr::NonNull;
use log::*;

const QUEUE_RECEIVEQ_PORT_0: u16 = 0;
const QUEUE_TRANSMITQ_PORT_0: u16 = 1;
const QUEUE_SIZE: u16 = 2;

/// Driver for a VirtIO console device.
///
/// Only a single port is allowed since `alloc` is disabled. Emergency write and cols/rows are not
/// implemented.
///
/// # Example
///
/// ```
/// # use virtio_drivers::{Error, Hal, Transport};
/// use virtio_drivers::VirtIOConsole;
/// # fn example<HalImpl: Hal, T: Transport>(transport: T) -> Result<(), Error> {
/// let mut console = VirtIOConsole::<HalImpl, _>::new(transport)?;
///
/// let info = console.info();
/// println!("VirtIO console {}x{}", info.rows, info.columns);
///
/// for &c in b"Hello console!\n" {
///   console.send(c)?;
/// }
///
/// let c = console.recv(true)?;
/// println!("Read {:?} from console.", c);
/// # Ok(())
/// # }
/// ```
pub struct VirtIOConsole<'a, H: Hal, T: Transport> {
    transport: T,
    config_space: NonNull<Config>,
    receiveq: VirtQueue<H>,
    transmitq: VirtQueue<H>,
    queue_buf_dma: Dma<H>,
    queue_buf_rx: &'a mut [u8],
    cursor: usize,
    pending_len: usize,
    /// The token of the outstanding receive request, if there is one.
    receive_token: Option<u16>,
}

/// Information about a console device, read from its configuration space.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConsoleInfo {
    pub rows: u16,
    pub columns: u16,
    pub max_ports: u32,
}

impl<H: Hal, T: Transport> VirtIOConsole<'_, H, T> {
    /// Creates a new VirtIO console driver.
    pub fn new(mut transport: T) -> Result<Self> {
        transport.begin_init(|features| {
            let features = Features::from_bits_truncate(features);
            info!("Device features {:?}", features);
            let supported_features = Features::empty();
            (features & supported_features).bits()
        });
        let config_space = transport.config_space::<Config>()?;
        let receiveq = VirtQueue::new(&mut transport, QUEUE_RECEIVEQ_PORT_0, QUEUE_SIZE)?;
        let transmitq = VirtQueue::new(&mut transport, QUEUE_TRANSMITQ_PORT_0, QUEUE_SIZE)?;
        let queue_buf_dma = Dma::new(1)?;
        let queue_buf_rx = unsafe { &mut queue_buf_dma.as_buf()[0..] };
        transport.finish_init();
        let mut console = VirtIOConsole {
            transport,
            config_space,
            receiveq,
            transmitq,
            queue_buf_dma,
            queue_buf_rx,
            cursor: 0,
            pending_len: 0,
            receive_token: None,
        };
        console.poll_retrieve()?;
        Ok(console)
    }

    /// Returns a struct with information about the console device, such as the number of rows and columns.
    pub fn info(&self) -> ConsoleInfo {
        // Safe because config_space is a valid pointer to the device configuration space.
        unsafe {
            let columns = volread!(self.config_space, cols);
            let rows = volread!(self.config_space, rows);
            let max_ports = volread!(self.config_space, max_nr_ports);
            ConsoleInfo {
                rows,
                columns,
                max_ports,
            }
        }
    }

    /// Makes a request to the device to receive data, if there is not already an outstanding
    /// receive request or some data already received and not yet returned.
    fn poll_retrieve(&mut self) -> Result<()> {
        if self.receive_token.is_none() && self.cursor == self.pending_len {
            // Safe because the buffer lasts at least as long as the queue, and there are no other
            // outstanding requests using the buffer.
            self.receive_token = Some(unsafe { self.receiveq.add(&[], &[self.queue_buf_rx]) }?);
        }
        Ok(())
    }

    /// Acknowledges a pending interrupt, if any, and completes the outstanding finished read
    /// request if there is one.
    ///
    /// Returns true if new data has been received.
    pub fn ack_interrupt(&mut self) -> Result<bool> {
        if !self.transport.ack_interrupt() {
            return Ok(false);
        }

        Ok(self.finish_receive())
    }

    /// If there is an outstanding receive request and it has finished, completes it.
    ///
    /// Returns true if new data has been received.
    fn finish_receive(&mut self) -> bool {
        let mut flag = false;
        if let Some(receive_token) = self.receive_token {
            if let Ok((token, len)) = self.receiveq.pop_used() {
                assert_eq!(token, receive_token);
                flag = true;
                assert_ne!(len, 0);
                self.cursor = 0;
                self.pending_len = len as usize;
            }
        }
        flag
    }

    /// Returns the next available character from the console, if any.
    ///
    /// If no data has been received this will not block but immediately return `Ok<None>`.
    pub fn recv(&mut self, pop: bool) -> Result<Option<u8>> {
        self.finish_receive();
        if self.cursor == self.pending_len {
            return Ok(None);
        }
        let ch = self.queue_buf_rx[self.cursor];
        if pop {
            self.cursor += 1;
            self.poll_retrieve()?;
        }
        Ok(Some(ch))
    }

    /// Sends a character to the console.
    pub fn send(&mut self, chr: u8) -> Result<()> {
        let buf: [u8; 1] = [chr];
        // Safe because the buffer is valid until we pop_used below.
        self.transmitq
            .add_notify_wait_pop(&[&buf], &[], &mut self.transport)?;
        Ok(())
    }
}

impl<H: Hal, T: Transport> Drop for VirtIOConsole<'_, H, T> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(QUEUE_RECEIVEQ_PORT_0);
        self.transport.queue_unset(QUEUE_TRANSMITQ_PORT_0);
    }
}

#[repr(C)]
struct Config {
    cols: ReadOnly<u16>,
    rows: ReadOnly<u16>,
    max_nr_ports: ReadOnly<u32>,
    emerg_wr: WriteOnly<u32>,
}

bitflags! {
    struct Features: u64 {
        const SIZE                  = 1 << 0;
        const MULTIPORT             = 1 << 1;
        const EMERG_WRITE           = 1 << 2;

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        hal::fake::FakeHal,
        transport::fake::{FakeTransport, QueueStatus, State},
    };
    use alloc::{sync::Arc, vec};
    use core::ptr::NonNull;
    use std::sync::Mutex;

    #[test]
    fn receive() {
        let mut config_space = Config {
            cols: ReadOnly::new(0),
            rows: ReadOnly::new(0),
            max_nr_ports: ReadOnly::new(0),
            emerg_wr: WriteOnly::default(),
        };
        let state = Arc::new(Mutex::new(State {
            status: DeviceStatus::empty(),
            driver_features: 0,
            guest_page_size: 0,
            interrupt_pending: false,
            queues: vec![QueueStatus::default(); 2],
        }));
        let transport = FakeTransport {
            device_type: DeviceType::Console,
            max_queue_size: 2,
            device_features: 0,
            config_space: NonNull::from(&mut config_space),
            state: state.clone(),
        };
        let mut console = VirtIOConsole::<FakeHal, FakeTransport<Config>>::new(transport).unwrap();

        // Nothing is available to receive.
        assert_eq!(console.recv(false).unwrap(), None);
        assert_eq!(console.recv(true).unwrap(), None);

        // Still nothing after a spurious interrupt.
        assert_eq!(console.ack_interrupt(), Ok(false));
        assert_eq!(console.recv(false).unwrap(), None);

        // Make a character available, and simulate an interrupt.
        {
            let mut state = state.lock().unwrap();
            state.write_to_queue(QUEUE_SIZE, QUEUE_RECEIVEQ_PORT_0, &[42]);

            state.interrupt_pending = true;
        }
        assert_eq!(console.ack_interrupt(), Ok(true));
        assert_eq!(state.lock().unwrap().interrupt_pending, false);

        // Receive the character. If we don't pop it it is still there to read again.
        assert_eq!(console.recv(false).unwrap(), Some(42));
        assert_eq!(console.recv(true).unwrap(), Some(42));
        assert_eq!(console.recv(true).unwrap(), None);
    }
}
