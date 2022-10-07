#![no_std]
#![no_main]

mod exceptions;
mod logger;
mod pl011;

use core::panic::PanicInfo;
use log::{error, info, LevelFilter};
use psci::system_off;

#[no_mangle]
extern "C" fn main(_x0: u64, _x1: u64, _x2: u64, _x3: u64) {
    logger::init(LevelFilter::Debug).unwrap();
    info!("virtio-drivers example started.");
    system_off().unwrap();
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    error!("{}", info);
    system_off().unwrap();
    loop {}
}
