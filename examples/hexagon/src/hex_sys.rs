use core::arch::asm;

#[cfg(target_arch = "hexagon")]
pub fn shutdown() -> ! {
    unsafe {
        asm!("stop(r0)");
    }
    loop {}
}
