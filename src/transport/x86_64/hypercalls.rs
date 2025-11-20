//! Hypercalls for x86-64 pKVM.

use core::arch::asm;
use zerocopy::{FromBytes, Immutable, IntoBytes};

/// This CPUID returns the signature and should be used to determine if VM is running under pKVM,
/// KVM or not. See the Linux header `arch/x86/include/uapi/asm/kvm_para.h`.
const KVM_CPUID_SIGNATURE: u32 = 0x40000000;

// See `include/uapi/linux/kvm_para.h`. (These hypercalls numbers can change depending on the
// upstream progress.)
const KVM_HC_PKVM_OP: u64 = 20;
const PKVM_GHC_IOREAD: u64 = KVM_HC_PKVM_OP + 3;
const PKVM_GHC_IOWRITE: u64 = KVM_HC_PKVM_OP + 4;

/// The maximum number of bytes that can be read or written by a single IO hypercall.
const HYP_IO_MAX: usize = 8;

/// Gets the signature CPU ID.
pub fn cpuid_signature() -> [u8; 4] {
    let signature: u32;

    // SAFETY: Assembly call. The argument for cpuid is passed via rax and in case of
    // KVM_CPUID_SIGNATURE returned via rbx, rcx and rdx. Ideally using a named argument in
    // inline asm for rbx would be more straightforward, but when "rbx" is directly used
    // LLVM complains that it is used internally.
    //
    // Therefore use r8 instead and push rbx to the stack before making cpuid call, store
    // rbx content to r8 as use it as inline asm output and pop the rbx.
    unsafe {
        asm!(
            "push rbx",
            "cpuid",
            "mov r8, rbx",
            "pop rbx",
            in("eax") KVM_CPUID_SIGNATURE,
            out("r8") signature,
            out("rcx") _,
            out("rdx") _,
        );
    };
    signature.to_le_bytes()
}

fn __vmcall_impl(hypcall: u64, a1: u64, a2: u64, a3: u64, a4: u64) -> u64 {
    let ret: u64;

    // SAFETY: Assembly call. Arguments for vmcall are passed via rax, rbx, rcx, rdx and rsi.
    // Ideally using a named argument in the inline asm for rbx would be more straightforward,
    // but when "rbx" is used directly LLVM complains that it is used internally.
    //
    // Therefore use temp register to store rbx content and restore it back afterwards.
    unsafe {
        asm!(
            "xchg %rbx, {0:r}",
            "vmcall",
            "xchg %rbx, {0:r}",
            in(reg) a1,
            inout("rax") hypcall => ret,
            in("rcx") a2,
            in("rdx") a3,
            in("rsi") a4,
            options(att_syntax)
        );
    };
    ret
}

// This block uses inline assembly to perform a vmcall, interacting directly with the hypervisor.
// The pKVM hypervisor can share RAX/RBX/RCX/RDX/RSI with pKVM host during hypercall
// handling.
macro_rules! vmcall {
    ($hypcall:expr) => {
        __vmcall_impl($hypcall, 0, 0, 0, 0)
    };
    ($hypcall:expr, $a1:expr) => {
        __vmcall_impl($hypcall, $a1, 0, 0, 0)
    };
    ($hypcall:expr, $a1:expr, $a2:expr) => {
        __vmcall_impl($hypcall, $a1, $a2, 0, 0)
    };
    ($hypcall:expr, $a1:expr, $a2:expr, $a3:expr) => {
        __vmcall_impl($hypcall, $a1, $a2, $a3, 0)
    };
    ($hypcall:expr, $a1:expr, $a2:expr, $a3:expr, $a4:expr) => {
        __vmcall_impl($hypcall, $a1, $a2, $a3, $a4)
    };
}

/// Asks the hypervisor to perform an IO read at the given physical address.
pub fn hyp_io_read(address: u64, size: usize) -> u64 {
    vmcall!(PKVM_GHC_IOREAD, address, size as u64)
}

/// Asks the hypervisor to perform an IO write at the given physical address.
pub fn hyp_io_write(address: u64, size: usize, data: u64) {
    vmcall!(PKVM_GHC_IOWRITE, address, size as u64, data);
}

/// A region of physical address space which may be accessed by IO read and/or write hypercalls.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HypIoRegion {
    /// The physical address of the start of the IO region.
    pub paddr: u64,
    /// The size of the IO region in bytes.
    pub size: usize,
}

impl HypIoRegion {
    pub fn read<T: FromBytes>(self, offset: usize) -> T {
        assert!(offset + size_of::<T>() <= self.size);
        assert!(size_of::<T>() <= HYP_IO_MAX);

        let data = hyp_io_read(self.paddr + offset as u64, size_of::<T>());
        T::read_from_prefix(data.as_bytes()).unwrap().0
    }

    pub fn write<T: IntoBytes + Immutable>(self, offset: usize, value: T) {
        assert!(offset + size_of::<T>() <= self.size);
        assert!(size_of::<T>() <= HYP_IO_MAX);

        let mut data = 0;
        data.as_mut_bytes()[..size_of::<T>()].copy_from_slice(value.as_bytes());
        hyp_io_write(self.paddr + offset as u64, size_of::<T>(), data);
    }
}
