use core::arch::global_asm;

use x86_64::registers::control::{Cr0Flags, Cr4Flags};
use x86_64::registers::model_specific::EferFlags;

const BOOT_STACK_SIZE: usize = 0x4000; // 16K

/// Flags set in the ’flags’ member of the multiboot header.
///
/// (bits 1, 16: memory information, address fields in header)
const MULTIBOOT_HEADER_FLAGS: usize = 0x0001_0002;

/// The magic field should contain this.
const MULTIBOOT_HEADER_MAGIC: usize = 0x1BADB002;

/// This should be in EAX.
const MULTIBOOT_BOOTLOADER_MAGIC: usize = 0x2BADB002;

const CR0: u64 = Cr0Flags::PROTECTED_MODE_ENABLE.bits()
    | Cr0Flags::MONITOR_COPROCESSOR.bits()
    | Cr0Flags::NUMERIC_ERROR.bits()
    | Cr0Flags::WRITE_PROTECT.bits()
    | Cr0Flags::PAGING.bits();

const CR4: u64 = Cr4Flags::PHYSICAL_ADDRESS_EXTENSION.bits() | Cr4Flags::PAGE_GLOBAL.bits();

const EFER: u64 = EferFlags::LONG_MODE_ENABLE.bits() | EferFlags::NO_EXECUTE_ENABLE.bits();

global_asm!(
    include_str!("multiboot.S"),
    mb_magic = const MULTIBOOT_BOOTLOADER_MAGIC,
    mb_hdr_magic = const MULTIBOOT_HEADER_MAGIC,
    mb_hdr_flags = const MULTIBOOT_HEADER_FLAGS,
    entry = sym super::main,

    offset = const 0, // virt_addr == phys_addr
    boot_stack_size = const BOOT_STACK_SIZE,

    cr0 = const CR0,
    cr4 = const CR4,
    efer_msr = const 0xC000_0080u32,
    efer = const EFER,
);
