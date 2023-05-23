use super::{
    protocol::VsockAddr, vsock::ConnectionInfo, SocketError, VirtIOSocket, VsockEvent,
    VsockEventType,
};
use crate::{transport::Transport, Hal, Result};
use alloc::{boxed::Box, vec::Vec};
use core::cmp::min;
use core::convert::TryInto;
use core::hint::spin_loop;
use log::debug;
use zerocopy::FromBytes;

const PER_CONNECTION_BUFFER_CAPACITY: usize = 1024;

/// A higher level interface for vsock devices.
///
/// This keeps track of a single vsock connection.
pub struct VsockConnectionManager<H: Hal, T: Transport> {
    driver: VirtIOSocket<H, T>,
    connections: Vec<Connection>,
}

#[derive(Debug)]
struct Connection {
    info: ConnectionInfo,
    buffer: RingBuffer,
}

impl<H: Hal, T: Transport> VsockConnectionManager<H, T> {
    /// Construct a new connection manager wrapping the given low-level VirtIO socket driver.
    pub fn new(driver: VirtIOSocket<H, T>) -> Self {
        Self {
            driver,
            connections: Vec::new(),
        }
    }

    /// Returns the CID which has been assigned to this guest.
    pub fn guest_cid(&self) -> u64 {
        self.driver.guest_cid()
    }

    /// Sends a request to connect to the given destination.
    ///
    /// This returns as soon as the request is sent; you should wait until `poll` returns a
    /// `VsockEventType::Connected` event indicating that the peer has accepted the connection
    /// before sending data.
    pub fn connect(&mut self, destination: VsockAddr, src_port: u32) -> Result {
        if self.connections.iter().any(|connection| {
            connection.info.dst == destination && connection.info.src_port == src_port
        }) {
            return Err(SocketError::ConnectionExists.into());
        }

        let mut new_connection_info = ConnectionInfo::new(destination, src_port);
        new_connection_info.buf_alloc = PER_CONNECTION_BUFFER_CAPACITY.try_into().unwrap();

        self.driver.connect(destination, src_port)?;
        debug!("Connection requested: {:?}", new_connection_info);
        self.connections.push(Connection {
            info: new_connection_info,
            buffer: RingBuffer::new(PER_CONNECTION_BUFFER_CAPACITY),
        });
        Ok(())
    }

    /// Sends the buffer to the destination.
    pub fn send(&mut self, destination: VsockAddr, src_port: u32, buffer: &[u8]) -> Result {
        let connection = self
            .connections
            .iter_mut()
            .find(|connection| {
                connection.info.dst == destination && connection.info.src_port == src_port
            })
            .ok_or(SocketError::NotConnected)?;

        self.driver.send(buffer, &mut connection.info)
    }

    /// Polls the vsock device to receive data or other updates.
    pub fn poll(&mut self) -> Result<Option<VsockEvent>> {
        let guest_cid = self.driver.guest_cid();
        let connections = &mut self.connections;

        self.driver.poll_recv(|event, body| {
            let connection = connections
                .iter_mut()
                .find(|connection| event.matches_connection(&connection.info, guest_cid));

            let Some(connection) = connection else {
                // Skip events which don't match any connection we know about.
                return Ok(None);
            };

            // Update stored connection info.
            connection.info.update_for_event(&event);

            match event.event_type {
                VsockEventType::Connected => {}
                VsockEventType::Disconnected { .. } => {
                    // TODO: Wait until client reads all data before removing connection.
                    //self.connection_info = None;
                }
                VsockEventType::Received { length } => {
                    // Copy to buffer
                    if !connection.buffer.write(body) {
                        return Err(SocketError::OutputBufferTooShort(length).into());
                    }
                }
                VsockEventType::CreditRequest => {
                    // TODO: Send a credit update.
                }
                VsockEventType::CreditUpdate => {}
            }

            Ok(Some(event))
        })
    }

    /// Reads data received from the given connection.
    pub fn recv(&mut self, peer: VsockAddr, src_port: u32, buffer: &mut [u8]) -> Result<usize> {
        let connection = self
            .connections
            .iter_mut()
            .find(|connection| connection.info.dst == peer && connection.info.src_port == src_port)
            .ok_or(SocketError::NotConnected)?;

        // Copy from ring buffer
        let bytes_read = connection.buffer.read(buffer);

        connection.info.done_forwarding(bytes_read);

        Ok(bytes_read)
    }

    /// Blocks until we get some event from the vsock device.
    pub fn wait_for_event(&mut self) -> Result<VsockEvent> {
        loop {
            if let Some(event) = self.poll()? {
                return Ok(event);
            } else {
                spin_loop();
            }
        }
    }

    /// Requests to shut down the connection cleanly.
    ///
    /// This returns as soon as the request is sent; you should wait until `poll` returns a
    /// `VsockEventType::Disconnected` event if you want to know that the peer has acknowledged the
    /// shutdown.
    pub fn shutdown(&mut self, destination: VsockAddr, src_port: u32) -> Result {
        let connection = self
            .connections
            .iter()
            .find(|connection| {
                connection.info.dst == destination && connection.info.src_port == src_port
            })
            .ok_or(SocketError::NotConnected)?;

        self.driver.shutdown(&connection.info)
    }

    /// Forcibly closes the connection without waiting for the peer.
    pub fn force_close(&mut self, destination: VsockAddr, src_port: u32) -> Result {
        let (index, connection) = self
            .connections
            .iter()
            .enumerate()
            .find(|(_, connection)| {
                connection.info.dst == destination && connection.info.src_port == src_port
            })
            .ok_or(SocketError::NotConnected)?;

        self.driver.force_close(&connection.info)?;

        self.connections.swap_remove(index);
        Ok(())
    }
}

#[derive(Debug)]
struct RingBuffer {
    buffer: Box<[u8]>,
    /// The number of bytes currently in the buffer.
    used: usize,
    /// The index of the first used byte in the buffer.
    start: usize,
}

impl RingBuffer {
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: FromBytes::new_box_slice_zeroed(capacity),
            used: 0,
            start: 0,
        }
    }

    /// Returns the number of bytes currently used in the buffer.
    pub fn used(&self) -> usize {
        self.used
    }

    /// Returns the number of bytes currently free in the buffer.
    pub fn available(&self) -> usize {
        self.buffer.len() - self.used
    }

    /// Adds the given bytes to the buffer if there is enough capacity for them all.
    ///
    /// Returns true if they were added, or false if they were not.
    pub fn write(&mut self, bytes: &[u8]) -> bool {
        if bytes.len() > self.available() {
            return false;
        }

        let end = (self.start + self.used) % self.buffer.len();
        let write_before_wraparound = min(bytes.len(), self.buffer.len() - end);
        let write_after_wraparound = bytes
            .len()
            .checked_sub(write_before_wraparound)
            .unwrap_or_default();
        self.buffer[end..end + write_before_wraparound]
            .copy_from_slice(&bytes[0..write_before_wraparound]);
        self.buffer[0..write_after_wraparound].copy_from_slice(&bytes[write_before_wraparound..]);
        self.used += bytes.len();

        true
    }

    /// Reads and removes as many bytes as possible from the buffer, up to the length of the given
    /// buffer.
    pub fn read(&mut self, out: &mut [u8]) -> usize {
        let bytes_read = min(self.used, out.len());

        // The number of bytes to copy out between `start` and the end of the buffer.
        let read_before_wraparound = min(bytes_read, self.buffer.len() - self.start);
        // The number of bytes to copy out from the beginning of the buffer after wrapping around.
        let read_after_wraparound = bytes_read
            .checked_sub(read_before_wraparound)
            .unwrap_or_default();

        out[0..read_before_wraparound]
            .copy_from_slice(&self.buffer[self.start..self.start + read_before_wraparound]);
        out[read_before_wraparound..bytes_read]
            .copy_from_slice(&self.buffer[0..read_after_wraparound]);

        self.used -= bytes_read;
        self.start = (self.start + bytes_read) % self.buffer.len();

        bytes_read
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        device::socket::{
            protocol::{SocketType, VirtioVsockConfig, VirtioVsockHdr, VirtioVsockOp},
            vsock::{VsockBufferStatus, QUEUE_SIZE, RX_QUEUE_IDX, TX_QUEUE_IDX},
        },
        hal::fake::FakeHal,
        transport::{
            fake::{FakeTransport, QueueStatus, State},
            DeviceStatus, DeviceType,
        },
        volatile::ReadOnly,
    };
    use alloc::{sync::Arc, vec};
    use core::{mem::size_of, ptr::NonNull};
    use std::{sync::Mutex, thread};
    use zerocopy::{AsBytes, FromBytes};

    #[test]
    fn send_recv() {
        let host_cid = 2;
        let guest_cid = 66;
        let host_port = 1234;
        let guest_port = 4321;
        let host_address = VsockAddr {
            cid: host_cid,
            port: host_port,
        };
        let hello_from_guest = "Hello from guest";
        let hello_from_host = "Hello from host";

        let mut config_space = VirtioVsockConfig {
            guest_cid_low: ReadOnly::new(66),
            guest_cid_high: ReadOnly::new(0),
        };
        let state = Arc::new(Mutex::new(State {
            status: DeviceStatus::empty(),
            driver_features: 0,
            guest_page_size: 0,
            interrupt_pending: false,
            queues: vec![
                QueueStatus::default(),
                QueueStatus::default(),
                QueueStatus::default(),
            ],
        }));
        let transport = FakeTransport {
            device_type: DeviceType::Socket,
            max_queue_size: 32,
            device_features: 0,
            config_space: NonNull::from(&mut config_space),
            state: state.clone(),
        };
        let mut socket = VsockConnectionManager::new(
            VirtIOSocket::<FakeHal, FakeTransport<VirtioVsockConfig>>::new(transport).unwrap(),
        );

        // Start a thread to simulate the device.
        let handle = thread::spawn(move || {
            // Wait for connection request.
            State::wait_until_queue_notified(&state, TX_QUEUE_IDX);
            assert_eq!(
                VirtioVsockHdr::read_from(
                    state
                        .lock()
                        .unwrap()
                        .read_from_queue::<QUEUE_SIZE>(TX_QUEUE_IDX)
                        .as_slice()
                )
                .unwrap(),
                VirtioVsockHdr {
                    op: VirtioVsockOp::Request.into(),
                    src_cid: guest_cid.into(),
                    dst_cid: host_cid.into(),
                    src_port: guest_port.into(),
                    dst_port: host_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 0.into(),
                    fwd_cnt: 0.into(),
                }
            );

            // Accept connection and give the peer enough credit to send the message.
            state.lock().unwrap().write_to_queue::<QUEUE_SIZE>(
                RX_QUEUE_IDX,
                VirtioVsockHdr {
                    op: VirtioVsockOp::Response.into(),
                    src_cid: host_cid.into(),
                    dst_cid: guest_cid.into(),
                    src_port: host_port.into(),
                    dst_port: guest_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 50.into(),
                    fwd_cnt: 0.into(),
                }
                .as_bytes(),
            );

            // Expect the guest to send some data.
            State::wait_until_queue_notified(&state, TX_QUEUE_IDX);
            let request = state
                .lock()
                .unwrap()
                .read_from_queue::<QUEUE_SIZE>(TX_QUEUE_IDX);
            assert_eq!(
                request.len(),
                size_of::<VirtioVsockHdr>() + hello_from_guest.len()
            );
            assert_eq!(
                VirtioVsockHdr::read_from_prefix(request.as_slice()).unwrap(),
                VirtioVsockHdr {
                    op: VirtioVsockOp::Rw.into(),
                    src_cid: guest_cid.into(),
                    dst_cid: host_cid.into(),
                    src_port: guest_port.into(),
                    dst_port: host_port.into(),
                    len: (hello_from_guest.len() as u32).into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 1024.into(),
                    fwd_cnt: 0.into(),
                }
            );
            assert_eq!(
                &request[size_of::<VirtioVsockHdr>()..],
                hello_from_guest.as_bytes()
            );

            println!("Host sending");

            // Send a response.
            let mut response = vec![0; size_of::<VirtioVsockHdr>() + hello_from_host.len()];
            VirtioVsockHdr {
                op: VirtioVsockOp::Rw.into(),
                src_cid: host_cid.into(),
                dst_cid: guest_cid.into(),
                src_port: host_port.into(),
                dst_port: guest_port.into(),
                len: (hello_from_host.len() as u32).into(),
                socket_type: SocketType::Stream.into(),
                flags: 0.into(),
                buf_alloc: 50.into(),
                fwd_cnt: (hello_from_guest.len() as u32).into(),
            }
            .write_to_prefix(response.as_mut_slice());
            response[size_of::<VirtioVsockHdr>()..].copy_from_slice(hello_from_host.as_bytes());
            state
                .lock()
                .unwrap()
                .write_to_queue::<QUEUE_SIZE>(RX_QUEUE_IDX, &response);

            // Expect a shutdown.
            State::wait_until_queue_notified(&state, TX_QUEUE_IDX);
            assert_eq!(
                VirtioVsockHdr::read_from(
                    state
                        .lock()
                        .unwrap()
                        .read_from_queue::<QUEUE_SIZE>(TX_QUEUE_IDX)
                        .as_slice()
                )
                .unwrap(),
                VirtioVsockHdr {
                    op: VirtioVsockOp::Shutdown.into(),
                    src_cid: guest_cid.into(),
                    dst_cid: host_cid.into(),
                    src_port: guest_port.into(),
                    dst_port: host_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 1024.into(),
                    fwd_cnt: (hello_from_host.len() as u32).into(),
                }
            );
        });

        socket.connect(host_address, guest_port).unwrap();
        assert_eq!(
            socket.wait_for_event().unwrap(),
            VsockEvent {
                source: host_address,
                destination: VsockAddr {
                    cid: guest_cid,
                    port: guest_port,
                },
                event_type: VsockEventType::Connected,
                buffer_status: VsockBufferStatus {
                    buffer_allocation: 50,
                    forward_count: 0,
                },
            }
        );
        println!("Guest sending");
        socket
            .send(host_address, guest_port, "Hello from guest".as_bytes())
            .unwrap();
        println!("Guest waiting to receive.");
        assert_eq!(
            socket.wait_for_event().unwrap(),
            VsockEvent {
                source: host_address,
                destination: VsockAddr {
                    cid: guest_cid,
                    port: guest_port,
                },
                event_type: VsockEventType::Received {
                    length: hello_from_host.len()
                },
                buffer_status: VsockBufferStatus {
                    buffer_allocation: 50,
                    forward_count: hello_from_guest.len() as u32,
                },
            }
        );
        println!("Guest getting received data.");
        let mut buffer = [0u8; 64];
        assert_eq!(
            socket.recv(host_address, guest_port, &mut buffer).unwrap(),
            hello_from_host.len()
        );
        assert_eq!(
            &buffer[0..hello_from_host.len()],
            hello_from_host.as_bytes()
        );
        socket.shutdown(host_address, guest_port).unwrap();

        handle.join().unwrap();
    }
}
