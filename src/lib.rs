//! VirtIO guest drivers.

#![no_std]
#![deny(unused_must_use, missing_docs)]

mod blk;
mod header;
mod queue;

pub use self::blk::VirtIOBlk;

const PAGE_SIZE: usize = 0x1000;

type VirtAddr = usize;
type PhysAddr = usize;

fn alloc_dma(_pages: usize) -> Result<(VirtAddr, PhysAddr)> {
    unimplemented!()
}

fn dealloc_dma(_paddr: PhysAddr, _pages: usize) -> Result {
    unimplemented!()
}

fn phys_to_virt(_paddr: PhysAddr) -> VirtAddr {
    unimplemented!()
}

fn virt_to_phys(_vaddr: VirtAddr) -> PhysAddr {
    unimplemented!()
}

/// The type returned by driver methods.
pub type Result<T = ()> = core::result::Result<T, Error>;

// pub struct Error {
//     kind: ErrorKind,
//     reason: &'static str,
// }

/// The error type of VirtIO drivers.
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    /// The buffer is too small.
    BufferTooSmall,
    /// The device is not ready.
    NotReady,
    /// The queue is already in use.
    AlreadyUsed,
    /// Invalid parameter.
    InvalidParam,
}

/// Types of virtio devices.
enum DeviceType {
    Invalid = 0,
    Network = 1,
    Block = 2,
    Console = 3,
    EntropySource = 4,
    MemoryBallooning = 5,
    IoMemory = 6,
    Rpmsg = 7,
    ScsiHost = 8,
    _9P = 9,
    Mac80211 = 10,
    RprocSerial = 11,
    VirtioCAIF = 12,
    MemoryBalloon = 13,
    GPU = 16,
    Timer = 17,
    Input = 18,
    Socket = 19,
    Crypto = 20,
    SignalDistributionModule = 21,
    Pstore = 22,
    IOMMU = 23,
    Memory = 24,
}
