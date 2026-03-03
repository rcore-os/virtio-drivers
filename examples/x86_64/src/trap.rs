use spin::mutex::{SpinMutex, SpinMutexGuard};
use x86_64::registers::control::Cr2;
use x86_64::set_general_handler;
use x86_64::structures::idt::{ExceptionVector, InterruptDescriptorTable, InterruptStackFrame};

static IDT: SpinMutex<InterruptDescriptorTable> = SpinMutex::new(InterruptDescriptorTable::new());

fn trap_handler(isf: InterruptStackFrame, index: u8, error_code: Option<u64>) {
    match index {
        x if x == ExceptionVector::Page as u8 => {
            let cr2 = Cr2::read_raw();
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
    let mut idt = IDT.lock();
    set_general_handler!(&mut idt, trap_handler);
    SpinMutexGuard::leak(idt).load();
}
