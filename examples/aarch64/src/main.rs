#![no_std]
#![no_main]

extern crate alloc;

mod exceptions;
mod hal;
mod logger;
#[cfg(platform = "qemu")]
mod pl011;
#[cfg(platform = "qemu")]
use pl011 as uart;
#[cfg(platform = "crosvm")]
mod uart8250;
#[cfg(platform = "crosvm")]
use uart8250 as uart;

use buddy_system_allocator::LockedHeap;
use core::{
    mem::size_of,
    panic::PanicInfo,
    ptr::{self, NonNull},
};
use flat_device_tree::{node::FdtNode, standard_nodes::Compatible, Fdt};
use hal::HalImpl;
use log::{debug, error, info, trace, warn, LevelFilter};
use smccc::{psci::system_off, Hvc};
use virtio_drivers::{
    device::{
        blk::VirtIOBlk,
        console::VirtIOConsole,
        gpu::VirtIOGpu,
        net::VirtIONetRaw,
        socket::{
            VirtIOSocket, VsockAddr, VsockConnectionManager, VsockEventType, VMADDR_CID_HOST,
        },
    },
    transport::{
        mmio::{MmioTransport, VirtIOHeader},
        pci::{
            bus::{BarInfo, Cam, Command, DeviceFunction, MemoryBarType, PciRoot},
            virtio_device_type, PciTransport,
        },
        DeviceType, Transport,
    },
};

/// Base memory-mapped address of the primary PL011 UART device.
#[cfg(platform = "qemu")]
pub const UART_BASE_ADDRESS: usize = 0x900_0000;

/// The base address of the first 8250 UART.
#[cfg(platform = "crosvm")]
pub const UART_BASE_ADDRESS: usize = 0x3f8;

#[global_allocator]
static HEAP_ALLOCATOR: LockedHeap<32> = LockedHeap::new();

static mut HEAP: [u8; 0x1000000] = [0; 0x1000000];

#[no_mangle]
extern "C" fn main(x0: u64, x1: u64, x2: u64, x3: u64) {
    logger::init(LevelFilter::Debug).unwrap();
    info!("virtio-drivers example started.");
    debug!(
        "x0={:#018x}, x1={:#018x}, x2={:#018x}, x3={:#018x}",
        x0, x1, x2, x3
    );

    // Safe because `HEAP` is only used here and `entry` is only called once.
    unsafe {
        // Give the allocator some memory to allocate.
        HEAP_ALLOCATOR
            .lock()
            .init(HEAP.as_mut_ptr() as usize, HEAP.len());
    }

    info!("Loading FDT from {:#018x}", x0);
    // Safe because the pointer is a valid pointer to unaliased memory.
    let fdt = unsafe { Fdt::from_ptr(x0 as *const u8).unwrap() };

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
                range.starting_address,
                range.size
            );
        }

        // Check whether it is a VirtIO MMIO device.
        if let (Some(compatible), Some(region)) = (node.compatible(), node.reg().next()) {
            if compatible.all().any(|s| s == "virtio,mmio")
                && region.size.unwrap_or(0) > size_of::<VirtIOHeader>()
            {
                debug!("Found VirtIO MMIO device at {:?}", region);

                let header = NonNull::new(region.starting_address as *mut VirtIOHeader).unwrap();
                match unsafe { MmioTransport::new(header) } {
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

    if let Some(pci_node) = fdt.find_compatible(&["pci-host-cam-generic"]) {
        info!("Found PCI node: {}", pci_node.name);
        enumerate_pci(pci_node, Cam::MmioCam);
    }
    if let Some(pcie_node) = fdt.find_compatible(&["pci-host-ecam-generic"]) {
        info!("Found PCIe node: {}", pcie_node.name);
        enumerate_pci(pcie_node, Cam::Ecam);
    }

    system_off::<Hvc>().unwrap();
}

fn virtio_device(transport: impl Transport) {
    match transport.device_type() {
        DeviceType::Block => virtio_blk(transport),
        DeviceType::GPU => virtio_gpu(transport),
        DeviceType::Network => virtio_net(transport),
        DeviceType::Console => virtio_console(transport),
        DeviceType::Socket => match virtio_socket(transport) {
            Ok(()) => info!("virtio-socket test finished successfully"),
            Err(e) => error!("virtio-socket test finished with error '{e:?}'"),
        },
        t => warn!("Unrecognized virtio device: {:?}", t),
    }
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

fn virtio_gpu<T: Transport>(transport: T) {
    let mut gpu = VirtIOGpu::<HalImpl, T>::new(transport).expect("failed to create gpu driver");
    let (width, height) = gpu.resolution().expect("failed to get resolution");
    let width = width as usize;
    let height = height as usize;
    info!("GPU resolution is {}x{}", width, height);
    let fb = gpu.setup_framebuffer().expect("failed to get fb");
    for y in 0..height {
        for x in 0..width {
            let idx = (y * width + x) * 4;
            fb[idx] = x as u8;
            fb[idx + 1] = y as u8;
            fb[idx + 2] = (x + y) as u8;
        }
    }
    gpu.flush().expect("failed to flush");
    //delay some time
    info!("virtio-gpu show graphics....");
    for _ in 0..1000 {
        for _ in 0..100000 {
            unsafe {
                core::arch::asm!("nop");
            }
        }
    }

    info!("virtio-gpu test finished");
}

fn virtio_net<T: Transport>(transport: T) {
    let mut net =
        VirtIONetRaw::<HalImpl, T, 16>::new(transport).expect("failed to create net driver");
    let mut buf = [0u8; 2048];
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
    if let Some(size) = console.size() {
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

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum PciRangeType {
    ConfigurationSpace,
    IoSpace,
    Memory32,
    Memory64,
}

impl From<u32> for PciRangeType {
    fn from(value: u32) -> Self {
        match value {
            0 => Self::ConfigurationSpace,
            1 => Self::IoSpace,
            2 => Self::Memory32,
            3 => Self::Memory64,
            _ => panic!("Tried to convert invalid range type {}", value),
        }
    }
}

fn enumerate_pci(pci_node: FdtNode, cam: Cam) {
    let reg = pci_node.reg();
    let mut allocator = PciMemory32Allocator::for_pci_ranges(&pci_node);

    for region in reg {
        info!(
            "Reg: {:?}-{:#x}",
            region.starting_address,
            region.starting_address as usize + region.size.unwrap()
        );
        assert_eq!(region.size.unwrap(), cam.size() as usize);
        // Safe because we know the pointer is to a valid MMIO region.
        let mut pci_root = unsafe { PciRoot::new(region.starting_address as *mut u8, cam) };
        for (device_function, info) in pci_root.enumerate_bus(0) {
            let (status, command) = pci_root.get_status_command(device_function);
            info!(
                "Found {} at {}, status {:?} command {:?}",
                info, device_function, status, command
            );
            if let Some(virtio_type) = virtio_device_type(&info) {
                info!("  VirtIO {:?}", virtio_type);
                allocate_bars(&mut pci_root, device_function, &mut allocator);
                dump_bar_contents(&mut pci_root, device_function, 4);
                let mut transport =
                    PciTransport::new::<HalImpl>(&mut pci_root, device_function).unwrap();
                info!(
                    "Detected virtio PCI device with device type {:?}, features {:#018x}",
                    transport.device_type(),
                    transport.read_device_features(),
                );
                virtio_device(transport);
            }
        }
    }
}

/// Allocates 32-bit memory addresses for PCI BARs.
struct PciMemory32Allocator {
    start: u32,
    end: u32,
}

impl PciMemory32Allocator {
    /// Creates a new allocator based on the ranges property of the given PCI node.
    pub fn for_pci_ranges(pci_node: &FdtNode) -> Self {
        let mut memory_32_address = 0;
        let mut memory_32_size = 0;
        for range in pci_node.ranges() {
            let prefetchable = range.child_bus_address_hi & 0x4000_0000 != 0;
            let range_type = PciRangeType::from((range.child_bus_address_hi & 0x0300_0000) >> 24);
            let bus_address = range.child_bus_address as u64;
            let cpu_physical = range.parent_bus_address as u64;
            let size = range.size as u64;
            info!(
                "range: {:?} {}prefetchable bus address: {:#018x} host physical address: {:#018x} size: {:#018x}",
                range_type,
                if prefetchable { "" } else { "non-" },
                bus_address,
                cpu_physical,
                size,
            );
            // Use the largest range within the 32-bit address space for 32-bit memory, even if it
            // is marked as a 64-bit range. This is necessary because crosvm doesn't currently
            // provide any 32-bit ranges.
            if !prefetchable
                && matches!(range_type, PciRangeType::Memory32 | PciRangeType::Memory64)
                && size > memory_32_size.into()
                && bus_address + size < u32::MAX.into()
            {
                assert_eq!(bus_address, cpu_physical);
                memory_32_address = u32::try_from(cpu_physical).unwrap();
                memory_32_size = u32::try_from(size).unwrap();
            }
        }
        if memory_32_size == 0 {
            panic!("No 32-bit PCI memory region found.");
        }
        Self {
            start: memory_32_address,
            end: memory_32_address + memory_32_size,
        }
    }

    /// Allocates a 32-bit memory address region for a PCI BAR of the given power-of-2 size.
    ///
    /// It will have alignment matching the size. The size must be a power of 2.
    pub fn allocate_memory_32(&mut self, size: u32) -> u32 {
        assert!(size.is_power_of_two());
        let allocated_address = align_up(self.start, size);
        assert!(allocated_address + size <= self.end);
        self.start = allocated_address + size;
        allocated_address
    }
}

const fn align_up(value: u32, alignment: u32) -> u32 {
    ((value - 1) | (alignment - 1)) + 1
}

fn dump_bar_contents(root: &mut PciRoot, device_function: DeviceFunction, bar_index: u8) {
    let bar_info = root.bar_info(device_function, bar_index).unwrap();
    trace!("Dumping bar {}: {:#x?}", bar_index, bar_info);
    if let BarInfo::Memory { address, size, .. } = bar_info {
        let start = address as *const u8;
        unsafe {
            let mut buf = [0u8; 32];
            for i in 0..size / 32 {
                let ptr = start.add(i as usize * 32);
                ptr::copy(ptr, buf.as_mut_ptr(), 32);
                if buf.iter().any(|b| *b != 0xff) {
                    trace!("  {:?}: {:x?}", ptr, buf);
                }
            }
        }
    }
    trace!("End of dump");
}

/// Allocates appropriately-sized memory regions and assigns them to the device's BARs.
fn allocate_bars(
    root: &mut PciRoot,
    device_function: DeviceFunction,
    allocator: &mut PciMemory32Allocator,
) {
    for (bar_index, info) in root.bars(device_function).unwrap().into_iter().enumerate() {
        let Some(info) = info else { continue };
        debug!("BAR {}: {}", bar_index, info);
        // Ignore I/O bars, as they aren't required for the VirtIO driver.
        if let BarInfo::Memory {
            address_type, size, ..
        } = info
        {
            match address_type {
                MemoryBarType::Width32 => {
                    if size > 0 {
                        let address = allocator.allocate_memory_32(size);
                        debug!("Allocated address {:#010x}", address);
                        root.set_bar_32(device_function, bar_index as u8, address);
                    }
                }
                MemoryBarType::Width64 => {
                    if size > 0 {
                        let address = allocator.allocate_memory_32(size);
                        debug!("Allocated address {:#010x}", address);
                        root.set_bar_64(device_function, bar_index as u8, address.into());
                    }
                }

                _ => panic!("Memory BAR address type {:?} not supported.", address_type),
            }
        }
    }

    // Enable the device to use its BARs.
    root.set_command(
        device_function,
        Command::IO_SPACE | Command::MEMORY_SPACE | Command::BUS_MASTER,
    );
    let (status, command) = root.get_status_command(device_function);
    debug!(
        "Allocated BARs and enabled device, status {:?} command {:?}",
        status, command
    );
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    error!("{}", info);
    system_off::<Hvc>().unwrap();
    loop {}
}
