#![no_std]
#![no_main]

mod exceptions;
mod hal;
mod logger;
mod pl011;

use core::{mem::size_of, panic::PanicInfo, ptr::NonNull};
use fdt::{node::FdtNode, standard_nodes::Compatible, Fdt};
use hal::HalImpl;
use log::{debug, error, info, trace, warn, LevelFilter};
use psci::system_off;
use virtio_drivers::{
    pci::{
        bus::{Cam, PciRoot},
        virtio_device_type, PciTransport,
    },
    DeviceType, MmioTransport, Transport, VirtIOBlk, VirtIOGpu, VirtIOHeader, VirtIONet,
};

#[no_mangle]
extern "C" fn main(x0: u64, x1: u64, x2: u64, x3: u64) {
    logger::init(LevelFilter::Debug).unwrap();
    info!("virtio-drivers example started.");
    debug!(
        "x0={:#018x}, x1={:#018x}, x2={:#018x}, x3={:#018x}",
        x0, x1, x2, x3
    );

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
        if let Some(reg) = node.reg() {
            for range in reg {
                trace!(
                    "  {:#018x?}, length {:?}",
                    range.starting_address,
                    range.size
                );
            }
        }

        // Check whether it is a VirtIO MMIO device.
        if let (Some(compatible), Some(region)) =
            (node.compatible(), node.reg().and_then(|mut reg| reg.next()))
        {
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

    system_off().unwrap();
}

fn virtio_device(transport: impl Transport) {
    match transport.device_type() {
        DeviceType::Block => virtio_blk(transport),
        DeviceType::GPU => virtio_gpu(transport),
        DeviceType::Network => virtio_net(transport),
        t => warn!("Unrecognized virtio device: {:?}", t),
    }
}

fn virtio_blk<T: Transport>(transport: T) {
    let mut blk = VirtIOBlk::<HalImpl, T>::new(transport).expect("failed to create blk driver");
    let mut input = [0xffu8; 512];
    let mut output = [0; 512];
    for i in 0..32 {
        for x in input.iter_mut() {
            *x = i as u8;
        }
        blk.write_block(i, &input).expect("failed to write");
        blk.read_block(i, &mut output).expect("failed to read");
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
    info!("virtio-gpu test finished");
}

fn virtio_net<T: Transport>(transport: T) {
    let mut net = VirtIONet::<HalImpl, T>::new(transport).expect("failed to create net driver");
    let mut buf = [0u8; 0x100];
    let len = net.recv(&mut buf).expect("failed to recv");
    info!("recv: {:?}", &buf[..len]);
    net.send(&buf[..len]).expect("failed to send");
    info!("virtio-net test finished");
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum PciRangeType {
    ConfigurationSpace,
    IoSpace,
    Memory32,
    Memory64,
}

impl From<u8> for PciRangeType {
    fn from(value: u8) -> Self {
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
    let reg = pci_node.reg().expect("PCI node missing reg property.");
    let ranges = pci_node
        .property("ranges")
        .expect("PCI node missing ranges property.");
    for i in 0..ranges.value.len() / 28 {
        let range = &ranges.value[i * 28..(i + 1) * 28];
        let prefetchable = range[0] & 0x80 != 0;
        let range_type = PciRangeType::from(range[0] & 0x3);
        let bus_address = u64::from_be_bytes(range[4..12].try_into().unwrap());
        let cpu_physical = u64::from_be_bytes(range[12..20].try_into().unwrap());
        let size = u64::from_be_bytes(range[20..28].try_into().unwrap());
        info!(
            "range: {:?} {}prefetchable bus address: {:#018x} host physical address: {:#018x} size: {:#018x}",
            range_type,
            if prefetchable { "" } else { "non-" },
            bus_address,
            cpu_physical,
            size
        );
    }

    for region in reg {
        info!(
            "Reg: {:?}-{:#x}",
            region.starting_address,
            region.starting_address as usize + region.size.unwrap()
        );
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
                let mut transport =
                    PciTransport::new::<HalImpl>(pci_root.clone(), device_function).unwrap();
                info!("  Features: {:#018x}", transport.read_device_features());
            }
        }
    }
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    error!("{}", info);
    system_off().unwrap();
    loop {}
}
