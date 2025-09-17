#![no_std]
#![no_main]
#![feature(asm_experimental_arch)]

extern crate alloc;

mod hal;
mod hex_sys;
mod logger;
use arm_pl011_uart as uart;
use arm_pl011_uart::{DataBits, LineConfig, PL011Registers, Parity, StopBits};
pub const UART_BASE_ADDRESS: *mut PL011Registers = 0x1000_0000 as _;
use buddy_system_allocator::{Heap, LockedHeap};

#[global_allocator]
static HEAP_ALLOCATOR: LockedHeap<32> = LockedHeap::new();
static HEAP: SpinMutex<[u8; 0x1000000]> = SpinMutex::new([0; 0x1000000]);

use core::{
    mem::size_of,
    panic::PanicInfo,
    ptr::{self, NonNull},
};
use flat_device_tree::{Fdt, node::FdtNode, standard_nodes::Compatible};
use hal::HalImpl;
use log::{LevelFilter, Log, Metadata, Record, SetLoggerError};
use log::{debug, error, info, trace, warn};
use safe_mmio::UniqueMmioPointer;
use spin::mutex::{SpinMutex, SpinMutexGuard};
use uart::Uart;
use virtio_drivers::{
    device::{
        blk::VirtIOBlk,
        console::VirtIOConsole,
        net::VirtIONetRaw,
        rng::VirtIORng,
        socket::{
            VMADDR_CID_HOST, VirtIOSocket, VsockAddr, VsockConnectionManager, VsockEventType,
        },
    },
    transport::{
        DeviceType, Transport,
        mmio::{MmioTransport, VirtIOHeader},
        pci::{
            PciTransport,
            bus::{
                BarInfo, Cam, Command, ConfigurationAccess, DeviceFunction, MemoryBarType, MmioCam,
                PciRoot,
            },
            virtio_device_type,
        },
    },
};

const FDT_BASE: u64 = 0x9990_0000;

#[link(name = "startup", kind = "static")]
unsafe extern "C" {
    fn _start();
}
#[unsafe(no_mangle)]
extern "C" fn main(_dtb_loc: u64) -> ! {
    let mut uart =
        Uart::new(unsafe { UniqueMmioPointer::new(NonNull::new(UART_BASE_ADDRESS).unwrap()) });
    uart.enable(
        LineConfig {
            data_bits: DataBits::Bits8,
            parity: Parity::None,
            stop_bits: StopBits::One,
        },
        115200,
        50000000,
    )
    .unwrap();
    logger::init(uart, LevelFilter::Debug).unwrap();

    add_to_heap(
        &mut HEAP_ALLOCATOR.lock(),
        SpinMutexGuard::leak(HEAP.try_lock().unwrap()).as_mut_slice(),
    );

    info!("main() received _dtb_loc parameter: {:#018x}", _dtb_loc);
    let fdt_location: u64 = {
        if _dtb_loc != 0 { _dtb_loc }
        else { FDT_BASE }
    };
    info!("Loading FDT from {:#018x}", fdt_location);
    // Safe because the pointer is a valid pointer to unaliased memory.
    let fdt = match unsafe { Fdt::from_ptr(fdt_location as *const u8) } {
        Ok(fdt) => {
            info!("Loaded FDT, {} bytes", fdt.total_size());
            fdt
        }
        Err(e) => {
            error!("Failed to parse FDT at {:#018x}: {:?}", fdt_location, e);
            info!("Trying fallback FDT_BASE location: {:#018x}", FDT_BASE);
            match unsafe { Fdt::from_ptr(FDT_BASE as *const u8) } {
                Ok(fdt) => {
                    info!("Loaded FDT from fallback, {} bytes", fdt.total_size());
                    fdt
                }
                Err(e2) => {
                    error!("Failed to parse FDT at fallback location: {:?}", e2);
                    panic!("Cannot load FDT from any location");
                }
            }
        }
    };

    for node in fdt.all_nodes() {
        // Dump information about the node for debugging.
        trace!(
            "{}: {:?}",
            node.name,
            node.compatible().map(Compatible::first),
        );
        for range in node.reg() {
            trace!(
                "  {:#018x?}, length {:?}",
                range.starting_address, range.size
            );
        }

        // Check whether it is a VirtIO MMIO device.
        if let (Some(compatible), Some(region)) = (node.compatible(), node.reg().next()) {
            if compatible.all().any(|s| s == "virtio,mmio")
                && region.size.unwrap_or(0) > size_of::<VirtIOHeader>()
            {
                debug!("Found VirtIO MMIO device at {:?}", region);

                let header = NonNull::new(region.starting_address as *mut VirtIOHeader).unwrap();
                match unsafe { MmioTransport::new(header, region.size.unwrap()) } {
                    Err(e) => warn!("Error creating VirtIO MMIO transport: {}", e),
                    Ok(transport) => {
                        info!(
                            "Detected virtio MMIO device with vendor id {:#X}, device type {:?}, version {:?}",
                            transport.vendor_id(),
                            transport.device_type(),
                            transport.version(),
                        );
                        virtio_device(transport);
                    }
                }
            }
        }
    }
    hex_sys::shutdown();
    panic!("shutdown returned");
}

fn virtio_device(transport: impl Transport) {
    match transport.device_type() {
        DeviceType::Block => virtio_blk(transport),
        DeviceType::Network => virtio_net(transport),
        DeviceType::Console => virtio_console(transport),
        DeviceType::Socket => match virtio_socket(transport) {
            Ok(()) => info!("virtio-socket test finished successfully"),
            Err(e) => error!("virtio-socket test finished with error '{e:?}'"),
        },
        DeviceType::EntropySource => virtio_rng(transport),
        t => error!("unsupported virtio device for hexagon: '{t:?}'"),
    }
}

fn virtio_rng<T: Transport>(transport: T) {
    let mut bytes = [0u8; 8];
    let mut rng = VirtIORng::<HalImpl, T>::new(transport).expect("failed to create rng driver");
    let len = rng
        .request_entropy(&mut bytes)
        .expect("failed to receive entropy");
    info!("received {len} random bytes: {:?}", &bytes[..len]);
    info!("virtio-rng test finished");
}

fn virtio_blk<T: Transport>(transport: T) {
    let mut blk = VirtIOBlk::<HalImpl, T>::new(transport).expect("failed to create blk driver");
    assert!(!blk.readonly());
    let mut input = [0xffu8; 512];
    let mut output = [0; 512];
    for i in 0..32 {
        for x in input.iter_mut() {
            *x = i as u8;
        }
        blk.write_blocks(i, &input).expect("failed to write");
        blk.read_blocks(i, &mut output).expect("failed to read");
        assert_eq!(input, output);
    }
    info!("virtio-blk test finished");
}

fn virtio_net<T: Transport>(transport: T) {
    info!("starting virtio-net test");
    let mut net =
        VirtIONetRaw::<HalImpl, T, 16>::new(transport).expect("failed to create net driver");
    let mut buf = [0u8; 2048];
    info!("virtio-net test: about to receive");
    let (hdr_len, pkt_len) = net.receive_wait(&mut buf).expect("failed to recv");
    info!(
        "recv {} bytes: {:02x?}",
        pkt_len,
        &buf[hdr_len..hdr_len + pkt_len]
    );
    net.send(&buf[..hdr_len + pkt_len]).expect("failed to send");
    info!("virtio-net test finished");
}

fn virtio_console<T: Transport>(transport: T) {
    let mut console =
        VirtIOConsole::<HalImpl, T>::new(transport).expect("Failed to create console driver");
    if let Some(size) = console.size().unwrap() {
        info!("VirtIO console {}", size);
    }
    for &c in b"Hello world on console!\n" {
        console.send(c).expect("Failed to send character");
    }
    let c = console.recv(true).expect("Failed to read from console");
    info!("Read {:?}", c);
    info!("virtio-console test finished");
}

fn virtio_socket<T: Transport>(transport: T) -> virtio_drivers::Result<()> {
    let mut socket = VsockConnectionManager::new(
        VirtIOSocket::<HalImpl, T>::new(transport).expect("Failed to create socket driver"),
    );
    let port = 1221;
    let host_address = VsockAddr {
        cid: VMADDR_CID_HOST,
        port,
    };
    info!("Connecting to host on port {port}...");
    socket.connect(host_address, port)?;
    let event = socket.wait_for_event()?;
    assert_eq!(event.source, host_address);
    assert_eq!(event.destination.port, port);
    assert_eq!(event.event_type, VsockEventType::Connected);
    info!("Connected to the host");

    const EXCHANGE_NUM: usize = 2;
    let messages = ["0-Ack. Hello from guest.", "1-Ack. Received again."];
    for k in 0..EXCHANGE_NUM {
        let mut buffer = [0u8; 24];
        let socket_event = socket.wait_for_event()?;
        let VsockEventType::Received { length, .. } = socket_event.event_type else {
            panic!("Received unexpected socket event {:?}", socket_event);
        };
        let read_length = socket.recv(host_address, port, &mut buffer)?;
        assert_eq!(length, read_length);
        info!(
            "Received message: {:?}({:?}), len: {:?}",
            buffer,
            core::str::from_utf8(&buffer[..length]),
            length
        );

        let message = messages[k % messages.len()];
        socket.send(host_address, port, message.as_bytes())?;
        info!("Sent message: {:?}", message);
    }
    socket.shutdown(host_address, port)?;
    info!("Shutdown the connection");
    Ok(())
}

fn add_to_heap<const ORDER: usize>(heap: &mut Heap<ORDER>, range: &'static mut [u8]) {
    // SAFETY: The range we pass is valid because it comes from a mutable static reference, which it
    // effectively takes ownership of.
    unsafe {
        heap.init(range.as_mut_ptr() as usize, range.len());
    }
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    error!("panicked: {}", info.message());
    if let Some(location) = info.location() {
        error!(
            "panic occurred in file '{}' at line {}",
            location.file(),
            location.line(),
        );
    }

    loop {}
}
