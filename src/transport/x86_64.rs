//! x86-64 specific transports.

use super::pci::bus::{Cam, ConfigurationAccess, DeviceFunction};
use core::arch::asm;

/// This CPUID returns the signature and should be used to determine if VM is running under pKVM,
/// KVM or not. See the Linux header `arch/x86/include/uapi/asm/kvm_para.h`.
const KVM_CPUID_SIGNATURE: u32 = 0x40000000;

// See `include/uapi/linux/kvm_para.h`. (These hypercalls numbers can change depending on the
// upstream progress.)
const KVM_HC_PKVM_OP: u32 = 20;
const PKVM_GHC_IOREAD: u32 = KVM_HC_PKVM_OP + 3;
const PKVM_GHC_IOWRITE: u32 = KVM_HC_PKVM_OP + 4;

const PKVM_SIGNATURE: &[u8] = b"PKVM";

/// A PCI configuration access mechanism using hypercalls implemented by the x86-64 pKVM hypervisor.
pub struct HypCam {
    /// The physical base address of the PCI root complex.
    phys_base: usize,
    cam: Cam,
}

impl HypCam {
    /// Creates a new `HypCam` for the PCI root complex at the given physical base address.
    pub fn new(phys_base: usize, cam: Cam) -> Self {
        Self { phys_base, cam }
    }

    /// Returns whether we are running under pKVM by checking the CPU ID signature.
    pub fn is_pkvm() -> bool {
        cpuid_signature() == PKVM_SIGNATURE
    }
}

impl ConfigurationAccess for HypCam {
    fn read_word(&self, device_function: DeviceFunction, register_offset: u8) -> u32 {
        let address = self.cam.cam_offset(device_function, register_offset);
        hyp_io_read(self.phys_base + (address as usize), 4)
    }

    fn write_word(&mut self, device_function: DeviceFunction, register_offset: u8, data: u32) {
        let address = self.cam.cam_offset(device_function, register_offset);
        hyp_io_write(self.phys_base + (address as usize), 4, data);
    }

    unsafe fn unsafe_clone(&self) -> Self {
        Self {
            phys_base: self.phys_base,
            cam: self.cam,
        }
    }
}

/// Gets the signature CPU ID.
fn cpuid_signature() -> [u8; 4] {
    let signature: u32;
    unsafe {
        // The argument for cpuid is passed via rax and in case of KVM_CPUID_SIGNATURE returned via
        // rbx, rcx and rdx. Ideally using a named argument in inline asm for rbx would be more
        // straightforward, but when "rbx" is directly used LLVM complains that it is used
        // internally.
        //
        // Therefore use r8 instead and push rbx to the stack before making cpuid call, store
        // rbx content to r8 as use it as inline asm output and pop the rbx.
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

/// Asks the hypervisor to perform an IO read at the given physical address.
fn hyp_io_read(address: usize, size: usize) -> u32 {
    // Arguments for vmcall are passed via rax, rbx, rcx and rdx. Ideally using a named argument in
    // the inline asm for rbx would be more straightforward, but when "rbx" is used directly LLVM
    // complains that it is used internally.
    //
    // Therefore use r8 temporary, push rbx to the stack, perform proper call and pop rbx
    // again
    let data;
    unsafe {
        asm!(
            "push rbx",
            "mov rbx, r8",
            "vmcall",
            "pop rbx",
            inout("rax") PKVM_GHC_IOREAD => data,
            in("r8") address,
            in("rcx") size,
        );
    }
    data
}

/// Asks the hypervisor to perform an IO write at the given physical address.
fn hyp_io_write(address: usize, size: usize, data: u32) {
    unsafe {
        // Arguments for vmcall are passed via rax, rbx, rcx and rdx. Ideally using a named argument
        // in the inline asm for rbx would be more straightforward but when "rbx" is used directly
        // used LLVM complains that it is used internally.
        //
        // Therefore use r8 temporary, push rbx to the stack, perform proper call and pop rbx
        // again
        asm!(
            "push rbx",
            "mov rbx, r8",
            "vmcall",
            "pop rbx",
            in("rax") PKVM_GHC_IOWRITE,
            in("r8") address,
            in("rcx") size,
            in("rdx") data,
        );
    }
}
