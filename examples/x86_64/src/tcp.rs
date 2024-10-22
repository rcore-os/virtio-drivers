//! Simple echo server over TCP.
//!
//! Ref: <https://github.com/smoltcp-rs/smoltcp/blob/master/examples/server.rs>

use alloc::{borrow::ToOwned, rc::Rc, vec, vec::Vec};
use core::{cell::RefCell, str::FromStr};

use smoltcp::iface::{Config, Interface, SocketSet};
use smoltcp::phy::{Device, DeviceCapabilities, Medium, RxToken, TxToken};
use smoltcp::wire::{EthernetAddress, IpAddress, IpCidr, Ipv4Address};
use smoltcp::{socket::tcp, time::Instant};
use virtio_drivers::device::net::{RxBuffer, VirtIONet};
use virtio_drivers::{transport::Transport, Error};

use super::{HalImpl, NET_QUEUE_SIZE};

type DeviceImpl<T> = VirtIONet<HalImpl, T, NET_QUEUE_SIZE>;

const IP: &str = "10.0.2.15"; // QEMU user networking default IP
const GATEWAY: &str = "10.0.2.2"; // QEMU user networking gateway
const PORT: u16 = 5555;

struct DeviceWrapper<T: Transport> {
    inner: Rc<RefCell<DeviceImpl<T>>>,
}

impl<T: Transport> DeviceWrapper<T> {
    fn new(dev: DeviceImpl<T>) -> Self {
        DeviceWrapper {
            inner: Rc::new(RefCell::new(dev)),
        }
    }

    fn mac_address(&self) -> EthernetAddress {
        EthernetAddress(self.inner.borrow().mac_address())
    }
}

impl<T: Transport> Device for DeviceWrapper<T> {
    type RxToken<'a>
        = VirtioRxToken<T>
    where
        Self: 'a;
    type TxToken<'a>
        = VirtioTxToken<T>
    where
        Self: 'a;

    fn receive(&mut self, _timestamp: Instant) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        match self.inner.borrow_mut().receive() {
            Ok(buf) => Some((
                VirtioRxToken(self.inner.clone(), buf),
                VirtioTxToken(self.inner.clone()),
            )),
            Err(Error::NotReady) => None,
            Err(err) => panic!("receive failed: {}", err),
        }
    }

    fn transmit(&mut self, _timestamp: Instant) -> Option<Self::TxToken<'_>> {
        Some(VirtioTxToken(self.inner.clone()))
    }

    fn capabilities(&self) -> DeviceCapabilities {
        let mut caps = DeviceCapabilities::default();
        caps.max_transmission_unit = 1536;
        caps.max_burst_size = Some(1);
        caps.medium = Medium::Ethernet;
        caps
    }
}

struct VirtioRxToken<T: Transport>(Rc<RefCell<DeviceImpl<T>>>, RxBuffer);
struct VirtioTxToken<T: Transport>(Rc<RefCell<DeviceImpl<T>>>);

impl<T: Transport> RxToken for VirtioRxToken<T> {
    fn consume<R, F>(self, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let mut rx_buf = self.1;
        trace!(
            "RECV {} bytes: {:02X?}",
            rx_buf.packet_len(),
            rx_buf.packet()
        );
        let result = f(rx_buf.packet_mut());
        self.0.borrow_mut().recycle_rx_buffer(rx_buf).unwrap();
        result
    }
}

impl<T: Transport> TxToken for VirtioTxToken<T> {
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let mut dev = self.0.borrow_mut();
        let mut tx_buf = dev.new_tx_buffer(len);
        let result = f(tx_buf.packet_mut());
        trace!("SEND {} bytes: {:02X?}", len, tx_buf.packet());
        dev.send(tx_buf).unwrap();
        result
    }
}

pub fn test_echo_server<T: Transport>(dev: DeviceImpl<T>) {
    let mut device = DeviceWrapper::new(dev);

    // Create interface
    let mut config = Config::new();
    config.random_seed = 0x2333;
    if device.capabilities().medium == Medium::Ethernet {
        config.hardware_addr = Some(device.mac_address().into());
    }

    let mut iface = Interface::new(config, &mut device);
    iface.update_ip_addrs(|ip_addrs| {
        ip_addrs
            .push(IpCidr::new(IpAddress::from_str(IP).unwrap(), 24))
            .unwrap();
    });

    iface
        .routes_mut()
        .add_default_ipv4_route(Ipv4Address::from_str(GATEWAY).unwrap())
        .unwrap();

    // Create sockets
    let tcp_rx_buffer = tcp::SocketBuffer::new(vec![0; 1024]);
    let tcp_tx_buffer = tcp::SocketBuffer::new(vec![0; 1024]);
    let tcp_socket = tcp::Socket::new(tcp_rx_buffer, tcp_tx_buffer);

    let mut sockets = SocketSet::new(vec![]);
    let tcp_handle = sockets.add(tcp_socket);

    info!("start a reverse echo server...");
    let mut tcp_active = false;
    loop {
        let timestamp =
            unsafe { Instant::from_micros_const(core::arch::x86_64::_rdtsc() as i64 / 2_500) };
        iface.poll(timestamp, &mut device, &mut sockets);

        // tcp:PORT: echo with reverse
        let socket = sockets.get_mut::<tcp::Socket>(tcp_handle);
        if !socket.is_open() {
            info!("listening on port {}...", PORT);
            socket.listen(PORT).unwrap();
        }

        if socket.is_active() && !tcp_active {
            info!("tcp:{} connected", PORT);
        } else if !socket.is_active() && tcp_active {
            info!("tcp:{} disconnected", PORT);
        }
        tcp_active = socket.is_active();

        if socket.may_recv() {
            let data = socket
                .recv(|buffer| {
                    let recvd_len = buffer.len();
                    if !buffer.is_empty() {
                        debug!("tcp:{} recv {} bytes: {:?}", PORT, recvd_len, buffer);
                        let mut lines = buffer
                            .split(|&b| b == b'\n')
                            .map(ToOwned::to_owned)
                            .collect::<Vec<_>>();
                        for line in lines.iter_mut() {
                            line.reverse();
                        }
                        let data = lines.join(&b'\n');
                        (recvd_len, data)
                    } else {
                        (0, vec![])
                    }
                })
                .unwrap();
            if socket.can_send() && !data.is_empty() {
                debug!("tcp:{} send data: {:?}", PORT, data);
                socket.send_slice(&data[..]).unwrap();
            }
        } else if socket.may_send() {
            info!("tcp:{} close", PORT);
            socket.close();
            break;
        }
    }
}
