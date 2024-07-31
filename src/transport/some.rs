use zerocopy::{FromBytes, IntoBytes};

use super::{mmio::MmioTransport, pci::PciTransport, DeviceStatus, DeviceType, Transport};
use crate::{PhysAddr, Result};

/// A wrapper for an arbitrary VirtIO transport, either MMIO or PCI.
#[derive(Debug)]
pub enum SomeTransport {
    /// An MMIO transport.
    Mmio(MmioTransport),
    /// A PCI transport.
    Pci(PciTransport),
}

impl From<MmioTransport> for SomeTransport {
    fn from(mmio: MmioTransport) -> Self {
        Self::Mmio(mmio)
    }
}

impl From<PciTransport> for SomeTransport {
    fn from(pci: PciTransport) -> Self {
        Self::Pci(pci)
    }
}

impl Transport for SomeTransport {
    fn device_type(&self) -> DeviceType {
        match self {
            Self::Mmio(mmio) => mmio.device_type(),
            Self::Pci(pci) => pci.device_type(),
        }
    }

    fn read_device_features(&mut self) -> u64 {
        match self {
            Self::Mmio(mmio) => mmio.read_device_features(),
            Self::Pci(pci) => pci.read_device_features(),
        }
    }

    fn write_driver_features(&mut self, driver_features: u64) {
        match self {
            Self::Mmio(mmio) => mmio.write_driver_features(driver_features),
            Self::Pci(pci) => pci.write_driver_features(driver_features),
        }
    }

    fn max_queue_size(&mut self, queue: u16) -> u32 {
        match self {
            Self::Mmio(mmio) => mmio.max_queue_size(queue),
            Self::Pci(pci) => pci.max_queue_size(queue),
        }
    }

    fn notify(&mut self, queue: u16) {
        match self {
            Self::Mmio(mmio) => mmio.notify(queue),
            Self::Pci(pci) => pci.notify(queue),
        }
    }

    fn get_status(&self) -> DeviceStatus {
        match self {
            Self::Mmio(mmio) => mmio.get_status(),
            Self::Pci(pci) => pci.get_status(),
        }
    }

    fn set_status(&mut self, status: DeviceStatus) {
        match self {
            Self::Mmio(mmio) => mmio.set_status(status),
            Self::Pci(pci) => pci.set_status(status),
        }
    }

    fn set_guest_page_size(&mut self, guest_page_size: u32) {
        match self {
            Self::Mmio(mmio) => mmio.set_guest_page_size(guest_page_size),
            Self::Pci(pci) => pci.set_guest_page_size(guest_page_size),
        }
    }

    fn requires_legacy_layout(&self) -> bool {
        match self {
            Self::Mmio(mmio) => mmio.requires_legacy_layout(),
            Self::Pci(pci) => pci.requires_legacy_layout(),
        }
    }

    fn queue_set(
        &mut self,
        queue: u16,
        size: u32,
        descriptors: PhysAddr,
        driver_area: PhysAddr,
        device_area: PhysAddr,
    ) {
        match self {
            Self::Mmio(mmio) => mmio.queue_set(queue, size, descriptors, driver_area, device_area),
            Self::Pci(pci) => pci.queue_set(queue, size, descriptors, driver_area, device_area),
        }
    }

    fn queue_unset(&mut self, queue: u16) {
        match self {
            Self::Mmio(mmio) => mmio.queue_unset(queue),
            Self::Pci(pci) => pci.queue_unset(queue),
        }
    }

    fn queue_used(&mut self, queue: u16) -> bool {
        match self {
            Self::Mmio(mmio) => mmio.queue_used(queue),
            Self::Pci(pci) => pci.queue_used(queue),
        }
    }

    fn ack_interrupt(&mut self) -> bool {
        match self {
            Self::Mmio(mmio) => mmio.ack_interrupt(),
            Self::Pci(pci) => pci.ack_interrupt(),
        }
    }

    fn read_config_space<T: FromBytes>(&self, offset: usize) -> Result<T> {
        match self {
            Self::Mmio(mmio) => mmio.read_config_space(offset),
            Self::Pci(pci) => pci.read_config_space(offset),
        }
    }

    fn write_config_space<T: IntoBytes>(&mut self, offset: usize, value: T) -> Result<()> {
        match self {
            Self::Mmio(mmio) => mmio.write_config_space(offset, value),
            Self::Pci(pci) => pci.write_config_space(offset, value),
        }
    }
}
