//! PCI transport for VirtIO.

pub mod bus;

use self::bus::DeviceFunctionInfo;
use super::DeviceType;

/// The PCI vendor ID for VirtIO devices.
const VIRTIO_VENDOR_ID: u16 = 0x1af4;

/// The offset to add to a VirtIO device ID to get the corresponding PCI device ID.
const PCI_DEVICE_ID_OFFSET: u16 = 0x1040;

const TRANSITIONAL_NETWORK: u16 = 0x1000;
const TRANSITIONAL_BLOCK: u16 = 0x1001;
const TRANSITIONAL_MEMORY_BALLOONING: u16 = 0x1002;
const TRANSITIONAL_CONSOLE: u16 = 0x1003;
const TRANSITIONAL_SCSI_HOST: u16 = 0x1004;
const TRANSITIONAL_ENTROPY_SOURCE: u16 = 0x1005;
const TRANSITIONAL_9P_TRANSPORT: u16 = 0x1009;

fn device_type(pci_device_id: u16) -> DeviceType {
    match pci_device_id {
        TRANSITIONAL_NETWORK => DeviceType::Network,
        TRANSITIONAL_BLOCK => DeviceType::Block,
        TRANSITIONAL_MEMORY_BALLOONING => DeviceType::MemoryBalloon,
        TRANSITIONAL_CONSOLE => DeviceType::Console,
        TRANSITIONAL_SCSI_HOST => DeviceType::ScsiHost,
        TRANSITIONAL_ENTROPY_SOURCE => DeviceType::EntropySource,
        TRANSITIONAL_9P_TRANSPORT => DeviceType::_9P,
        id if id >= PCI_DEVICE_ID_OFFSET => DeviceType::from(id - PCI_DEVICE_ID_OFFSET),
        _ => DeviceType::Invalid,
    }
}

/// Returns the type of VirtIO device to which the given PCI vendor and device ID corresponds, or
/// `None` if it is not a recognised VirtIO device.
pub fn virtio_device_type(device_function_info: &DeviceFunctionInfo) -> Option<DeviceType> {
    if device_function_info.vendor_id == VIRTIO_VENDOR_ID {
        let device_type = device_type(device_function_info.device_id);
        if device_type != DeviceType::Invalid {
            return Some(device_type);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transitional_device_ids() {
        assert_eq!(device_type(0x1000), DeviceType::Network);
        assert_eq!(device_type(0x1002), DeviceType::MemoryBalloon);
        assert_eq!(device_type(0x1009), DeviceType::_9P);
    }

    #[test]
    fn offset_device_ids() {
        assert_eq!(device_type(0x1045), DeviceType::MemoryBalloon);
        assert_eq!(device_type(0x1049), DeviceType::_9P);
        assert_eq!(device_type(0x1058), DeviceType::Memory);
        assert_eq!(device_type(0x1040), DeviceType::Invalid);
        assert_eq!(device_type(0x1059), DeviceType::Invalid);
    }

    #[test]
    fn virtio_device_type_valid() {
        assert_eq!(
            virtio_device_type(&DeviceFunctionInfo {
                vendor_id: VIRTIO_VENDOR_ID,
                device_id: TRANSITIONAL_BLOCK,
                class: 0,
                subclass: 0,
                prog_if: 0,
                revision: 0,
                header_type: bus::HeaderType::Standard,
            }),
            Some(DeviceType::Block)
        );
    }

    #[test]
    fn virtio_device_type_invalid() {
        // Non-VirtIO vendor ID.
        assert_eq!(
            virtio_device_type(&DeviceFunctionInfo {
                vendor_id: 0x1234,
                device_id: TRANSITIONAL_BLOCK,
                class: 0,
                subclass: 0,
                prog_if: 0,
                revision: 0,
                header_type: bus::HeaderType::Standard,
            }),
            None
        );

        // Invalid device ID.
        assert_eq!(
            virtio_device_type(&DeviceFunctionInfo {
                vendor_id: VIRTIO_VENDOR_ID,
                device_id: 0x1040,
                class: 0,
                subclass: 0,
                prog_if: 0,
                revision: 0,
                header_type: bus::HeaderType::Standard,
            }),
            None
        );
    }
}
