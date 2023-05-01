use x86_64::set_general_handler;
use x86_64::structures::idt::{ExceptionVector, InterruptDescriptorTable, InterruptStackFrame};

static mut IDT: InterruptDescriptorTable = InterruptDescriptorTable::new();

fn trap_handler(isf: InterruptStackFrame, index: u8, error_code: Option<u64>) {
    match index {
        x if x == ExceptionVector::Page as u8 => {
            let cr2 = x86_64::registers::control::Cr2::read();
            panic!(
                "#PF at {:#x}, fault_vaddr={:#x}, err_code={:#x?}",
                isf.instruction_pointer, cr2, error_code
            );
        }
        _ => {
            panic!(
                "Unhandled exception {} (error_code = {:#x?}) at {:#x}:\n{:#x?}",
                index, error_code, isf.instruction_pointer, isf
            );
        }
    }
}

pub fn init() {
    unsafe {
        set_general_handler!(&mut IDT, trap_handler);
        IDT.load();
    }
}
