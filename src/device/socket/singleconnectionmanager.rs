use super::{
    protocol::VsockAddr, vsock::ConnectionInfo, SocketError, VirtIOSocket, VsockEvent,
    VsockEventType,
};
use crate::{transport::Transport, Hal, Result};
use core::hint::spin_loop;
use log::debug;

/// A higher level interface for VirtIO socket (vsock) devices.
///
/// This can only keep track of a single vsock connection. If you want to support multiple
/// simultaneous connections, try [`VsockConnectionManager`](super::VsockConnectionManager).
pub struct SingleConnectionManager<H: Hal, T: Transport> {
    driver: VirtIOSocket<H, T>,
    connection_info: Option<ConnectionInfo>,
}

impl<H: Hal, T: Transport> SingleConnectionManager<H, T> {
    /// Construct a new connection manager wrapping the given low-level VirtIO socket driver.
    pub fn new(driver: VirtIOSocket<H, T>) -> Self {
        Self {
            driver,
            connection_info: None,
        }
    }

    /// Returns the CID which has been assigned to this guest.
    pub fn guest_cid(&self) -> u64 {
        self.driver.guest_cid()
    }

    /// Sends a request to connect to the given destination.
    ///
    /// This returns as soon as the request is sent; you should wait until `poll_recv` returns a
    /// `VsockEventType::Connected` event indicating that the peer has accepted the connection
    /// before sending data.
    pub fn connect(&mut self, destination: VsockAddr, src_port: u32) -> Result {
        if self.connection_info.is_some() {
            return Err(SocketError::ConnectionExists.into());
        }

        let new_connection_info = ConnectionInfo::new(destination, src_port);

        self.driver.connect(&new_connection_info)?;
        debug!("Connection requested: {:?}", new_connection_info);
        self.connection_info = Some(new_connection_info);
        Ok(())
    }

    /// Sends the buffer to the destination.
    pub fn send(&mut self, buffer: &[u8]) -> Result {
        let connection_info = self
            .connection_info
            .as_mut()
            .ok_or(SocketError::NotConnected)?;
        connection_info.buf_alloc = 0;
        self.driver.send(buffer, connection_info)
    }

    /// Polls the vsock device to receive data or other updates.
    ///
    /// A buffer must be provided to put the data in if there is some to
    /// receive.
    pub fn poll_recv(&mut self, buffer: &mut [u8]) -> Result<Option<VsockEvent>> {
        let Some(connection_info) = &mut self.connection_info else {
            return Err(SocketError::NotConnected.into());
        };

        // Tell the peer that we have space to receive some data.
        connection_info.buf_alloc = buffer.len() as u32;
        self.driver.credit_update(connection_info)?;

        self.poll_rx_queue(buffer)
    }

    /// Blocks until we get some event from the vsock device.
    ///
    /// A buffer must be provided to put the data in if there is some to
    /// receive.
    pub fn wait_for_recv(&mut self, buffer: &mut [u8]) -> Result<VsockEvent> {
        loop {
            if let Some(event) = self.poll_recv(buffer)? {
                return Ok(event);
            } else {
                spin_loop();
            }
        }
    }

    fn poll_rx_queue(&mut self, body: &mut [u8]) -> Result<Option<VsockEvent>> {
        let guest_cid = self.driver.guest_cid();
        let self_connection_info = &mut self.connection_info;

        self.driver.poll(|event, borrowed_body| {
            let Some(connection_info) = self_connection_info else {
                return Ok(None);
            };

            // Skip packets which don't match our current connection.
            if !event.matches_connection(connection_info, guest_cid) {
                debug!(
                    "Skipping {:?} as connection is {:?}",
                    event, connection_info
                );
                return Ok(None);
            }

            // Update stored connection info.
            connection_info.update_for_event(&event);

            match event.event_type {
                VsockEventType::ConnectionRequest => {
                    // TODO: Send Rst or handle incoming connections.
                }
                VsockEventType::Connected => {}
                VsockEventType::Disconnected { .. } => {
                    *self_connection_info = None;
                }
                VsockEventType::Received { length } => {
                    body.get_mut(0..length)
                        .ok_or(SocketError::OutputBufferTooShort(length))?
                        .copy_from_slice(borrowed_body);
                    connection_info.done_forwarding(length);
                }
                VsockEventType::CreditRequest => {
                    // No point sending a credit update until `poll_recv` is called with a buffer,
                    // as otherwise buf_alloc would just be 0 anyway.
                }
                VsockEventType::CreditUpdate => {}
            }

            Ok(Some(event))
        })
    }

    /// Requests to shut down the connection cleanly.
    ///
    /// This returns as soon as the request is sent; you should wait until `poll_recv` returns a
    /// `VsockEventType::Disconnected` event if you want to know that the peer has acknowledged the
    /// shutdown.
    pub fn shutdown(&mut self) -> Result {
        let connection_info = self
            .connection_info
            .as_mut()
            .ok_or(SocketError::NotConnected)?;
        connection_info.buf_alloc = 0;

        self.driver.shutdown(connection_info)
    }

    /// Forcibly closes the connection without waiting for the peer.
    pub fn force_close(&mut self) -> Result {
        let connection_info = self
            .connection_info
            .as_mut()
            .ok_or(SocketError::NotConnected)?;
        connection_info.buf_alloc = 0;

        self.driver.force_close(connection_info)?;
        self.connection_info = None;
        Ok(())
    }

    /// Blocks until the peer either accepts our connection request (with a
    /// `VIRTIO_VSOCK_OP_RESPONSE`) or rejects it (with a
    /// `VIRTIO_VSOCK_OP_RST`).
    pub fn wait_for_connect(&mut self) -> Result {
        loop {
            match self.wait_for_recv(&mut [])?.event_type {
                VsockEventType::Connected => return Ok(()),
                VsockEventType::Disconnected { .. } => {
                    return Err(SocketError::ConnectionFailed.into())
                }
                VsockEventType::Received { .. } => return Err(SocketError::InvalidOperation.into()),
                VsockEventType::ConnectionRequest
                | VsockEventType::CreditRequest
                | VsockEventType::CreditUpdate => {}
            }
        }
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
            DeviceType,
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
            queues: vec![
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
        let mut socket = SingleConnectionManager::new(
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

            // Expect a credit update.
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
                    op: VirtioVsockOp::CreditUpdate.into(),
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
                    buf_alloc: 0.into(),
                    fwd_cnt: 0.into(),
                }
            );
            assert_eq!(
                &request[size_of::<VirtioVsockHdr>()..],
                hello_from_guest.as_bytes()
            );

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

            // Expect a credit update.
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
                    op: VirtioVsockOp::CreditUpdate.into(),
                    src_cid: guest_cid.into(),
                    dst_cid: host_cid.into(),
                    src_port: guest_port.into(),
                    dst_port: host_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 64.into(),
                    fwd_cnt: 0.into(),
                }
            );

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
                    buf_alloc: 0.into(),
                    fwd_cnt: (hello_from_host.len() as u32).into(),
                }
            );
        });

        socket.connect(host_address, guest_port).unwrap();
        socket.wait_for_connect().unwrap();
        socket.send(hello_from_guest.as_bytes()).unwrap();
        let mut buffer = [0u8; 64];
        let event = socket.wait_for_recv(&mut buffer).unwrap();
        assert_eq!(
            event,
            VsockEvent {
                source: VsockAddr {
                    cid: host_cid,
                    port: host_port,
                },
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
        assert_eq!(
            &buffer[0..hello_from_host.len()],
            hello_from_host.as_bytes()
        );
        socket.shutdown().unwrap();

        handle.join().unwrap();
    }
}
