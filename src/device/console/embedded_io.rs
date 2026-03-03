//! Implementation of `embedded-io` traits for `VirtIOConsole`.

use super::VirtIOConsole;
use crate::{Error, Hal, transport::Transport};
use core::cmp::min;
use embedded_io::{BufRead, ErrorType, Read, ReadReady, Write};

impl<H: Hal, T: Transport> ErrorType for VirtIOConsole<H, T> {
    type Error = Error;
}

impl<H: Hal, T: Transport> Write for VirtIOConsole<H, T> {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        if buf.is_empty() {
            Ok(0)
        } else {
            self.send_bytes(buf)?;
            Ok(buf.len())
        }
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        // We don't buffer writes, so nothing to do here.
        Ok(())
    }
}

impl<H: Hal, T: Transport> ReadReady for VirtIOConsole<H, T> {
    fn read_ready(&mut self) -> Result<bool, Self::Error> {
        self.finish_receive()?;
        Ok(self.cursor != self.pending_len)
    }
}

impl<H: Hal, T: Transport> Read for VirtIOConsole<H, T> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        if buf.is_empty() {
            Ok(0)
        } else {
            self.wait_for_receive()?;
            let read_length = min(buf.len(), self.pending_len - self.cursor);
            buf[..read_length]
                .copy_from_slice(&self.queue_buf_rx[self.cursor..self.cursor + read_length]);
            self.cursor += read_length;
            Ok(read_length)
        }
    }
}

impl<H: Hal, T: Transport> BufRead for VirtIOConsole<H, T> {
    fn fill_buf(&mut self) -> Result<&[u8], Self::Error> {
        self.wait_for_receive()?;
        Ok(&self.queue_buf_rx[self.cursor..self.pending_len])
    }

    fn consume(&mut self, amt: usize) {
        assert!(self.cursor + amt <= self.pending_len);
        self.cursor += amt;
    }
}

#[cfg(test)]
mod tests {
    use alloc::{sync::Arc, vec};
    use embedded_io::{BufRead, Read};
    use std::{sync::Mutex, thread};

    use crate::{
        config::{ReadOnly, WriteOnly},
        device::console::{Config, QUEUE_RECEIVEQ_PORT_0, QUEUE_SIZE, VirtIOConsole},
        hal::fake::FakeHal,
        transport::{
            DeviceType,
            fake::{FakeTransport, QueueStatus, State},
        },
    };

    fn setup_test() -> (
        VirtIOConsole<FakeHal, FakeTransport<Config>>,
        Arc<Mutex<State<Config>>>,
    ) {
        let config_space = Config {
            cols: ReadOnly::new(80),
            rows: ReadOnly::new(24),
            max_nr_ports: ReadOnly::new(4),
            emerg_wr: WriteOnly::default(),
        };
        let state = Arc::new(Mutex::new(State::new(
            vec![QueueStatus::default(), QueueStatus::default()],
            config_space,
        )));
        let transport = FakeTransport {
            device_type: DeviceType::Console,
            max_queue_size: 2,
            device_features: 0,
            state: state.clone(),
        };
        let console = VirtIOConsole::<FakeHal, FakeTransport<Config>>::new(transport).unwrap();
        (console, state)
    }

    #[test]
    fn read() {
        let (mut console, state) = setup_test();

        {
            let mut state = state.lock().unwrap();
            state.write_to_queue::<QUEUE_SIZE>(QUEUE_RECEIVEQ_PORT_0, &[42, 43, 44, 45, 46, 47]);
            state.interrupt_pending = true;
        }

        let mut buf = [0; 3];
        let n = console.read(&mut buf).unwrap();
        assert_eq!(n, 3);
        assert_eq!(&buf, &[42, 43, 44]);
        let n = console.read(&mut buf).unwrap();
        assert_eq!(n, 3);
        assert_eq!(&buf, &[45, 46, 47]);
    }

    #[test]
    fn bufread() {
        let (mut console, state) = setup_test();

        {
            let mut state = state.lock().unwrap();
            state.write_to_queue::<QUEUE_SIZE>(QUEUE_RECEIVEQ_PORT_0, &[42, 43, 44, 45, 46, 47]);
            state.interrupt_pending = true;
        }

        console.fill_buf().unwrap();
        console.consume(3);
        let mut buf = [0; 3];
        let n = console.read(&mut buf).unwrap();
        assert_eq!(n, 3);
        assert_eq!(&buf, &[45, 46, 47]);
    }

    #[test]
    fn read_exact() {
        let (mut console, state) = setup_test();

        let mut recv_buf = [0; 100];

        let data = {
            let mut data = Vec::new();
            for i in 0..recv_buf.len() {
                data.push((42 + i % 256) as u8);
            }
            data
        };
        let expect = data.clone();

        thread::spawn(move || {
            // Make a character available, and simulate an interrupt.
            for chunk in data.chunks(5) {
                thread::sleep(std::time::Duration::from_millis(10));
                let mut state = state.lock().unwrap();
                state.write_to_queue::<QUEUE_SIZE>(QUEUE_RECEIVEQ_PORT_0, chunk);
                state.interrupt_pending = true;
            }
        });

        console.read_exact(&mut recv_buf).unwrap();
        assert_eq!(&recv_buf, expect.as_slice());
    }
}
