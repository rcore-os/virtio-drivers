#![no_std]
#![no_main]

mod exceptions;
mod logger;
mod pl011;

use core::panic::PanicInfo;
use fdt::{standard_nodes::Compatible, Fdt};
use log::{debug, error, info, trace, LevelFilter};
use psci::system_off;

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
    }

    system_off().unwrap();
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    error!("{}", info);
    system_off().unwrap();
    loop {}
}
