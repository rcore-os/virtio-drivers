use zerocopy::{FromBytes, Immutable, IntoBytes};

use super::{DeviceStatus, DeviceType, Transport, mmio::MmioTransport, pci::PciTransport};
use crate::{PhysAddr, Result, transport::InterruptStatus};

/// A wrapper for an arbitrary VirtIO transport, either MMIO or PCI.
#[derive(Debug)]
pub enum SomeTransport<'a> {
    /// An MMIO transport.
    Mmio(MmioTransport<'a>),
    /// A PCI transport.
    Pci(PciTransport),
    /// An x86-64 pKVM PCI transport.
    #[cfg(target_arch = "x86_64")]
    HypPci(super::x86_64::HypPciTransport),
}

macro_rules! dispatch {
    ($self:expr, $method:ident $(, $arg:expr)*) => {
        match $self {
            Self::Mmio(t) => t.$method($($arg),*),
            Self::Pci(t) => t.$method($($arg),*),
            #[cfg(target_arch = "x86_64")]
            Self::HypPci(t) => t.$method($($arg),*),
        }
    };
}

impl<'a> From<MmioTransport<'a>> for SomeTransport<'a> {
    fn from(mmio: MmioTransport<'a>) -> Self {
        Self::Mmio(mmio)
    }
}

impl From<PciTransport> for SomeTransport<'_> {
    fn from(pci: PciTransport) -> Self {
        Self::Pci(pci)
    }
}

impl Transport for SomeTransport<'_> {
    fn device_type(&self) -> DeviceType {
        dispatch!(self, device_type)
    }

    fn read_device_features(&mut self) -> u64 {
        dispatch!(self, read_device_features)
    }

    fn write_driver_features(&mut self, driver_features: u64) {
        dispatch!(self, write_driver_features, driver_features)
    }

    fn max_queue_size(&mut self, queue: u16) -> u32 {
        dispatch!(self, max_queue_size, queue)
    }

    fn notify(&mut self, queue: u16) {
        dispatch!(self, notify, queue)
    }

    fn get_status(&self) -> DeviceStatus {
        dispatch!(self, get_status)
    }

    fn set_status(&mut self, status: DeviceStatus) {
        dispatch!(self, set_status, status)
    }

    fn set_guest_page_size(&mut self, guest_page_size: u32) {
        dispatch!(self, set_guest_page_size, guest_page_size)
    }

    fn requires_legacy_layout(&self) -> bool {
        dispatch!(self, requires_legacy_layout)
    }

    fn queue_set(
        &mut self,
        queue: u16,
        size: u32,
        descriptors: PhysAddr,
        driver_area: PhysAddr,
        device_area: PhysAddr,
    ) {
        dispatch!(self, queue_set, queue, size, descriptors, driver_area, device_area)
    }

    fn queue_unset(&mut self, queue: u16) {
        dispatch!(self, queue_unset, queue)
    }

    fn queue_used(&mut self, queue: u16) -> bool {
        dispatch!(self, queue_used, queue)
    }

    fn ack_interrupt(&mut self) -> InterruptStatus {
        dispatch!(self, ack_interrupt)
    }

    fn read_config_generation(&self) -> u32 {
        dispatch!(self, read_config_generation)
    }

    fn read_config_space<T: FromBytes + IntoBytes>(&self, offset: usize) -> Result<T> {
        dispatch!(self, read_config_space, offset)
    }

    fn write_config_space<T: IntoBytes + Immutable>(
        &mut self,
        offset: usize,
        value: T,
    ) -> Result<()> {
        dispatch!(self, write_config_space, offset, value)
    }
}
