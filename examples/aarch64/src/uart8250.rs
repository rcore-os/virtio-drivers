//! Minimal driver for an 8250 UART. This only implements enough to work with the emulated 8250
//! provided by crosvm, and won't work with real hardware.

use core::fmt::{self, Write};
use core::ptr::write_volatile;

/// Minimal driver for an 8250 UART. This only implements enough to work with the emulated 8250
/// provided by crosvm, and won't work with real hardware.
pub struct Uart {
    base_address: *mut u8,
}

impl Uart {
    /// Constructs a new instance of the UART driver for a device at the given base address.
    ///
    /// # Safety
    ///
    /// The given base address must point to the 8 MMIO control registers of an appropriate UART
    /// device, which must be mapped into the address space of the process as device memory and not
    /// have any other aliases.
    pub unsafe fn new(base_address: *mut u32) -> Self {
        Self {
            base_address: base_address.cast(),
        }
    }

    /// Writes a single byte to the UART.
    pub fn write_byte(&self, byte: u8) {
        // Safe because we know that the base address points to the control registers of an UART
        // device which is appropriately mapped.
        unsafe {
            write_volatile(self.base_address, byte);
        }
    }
}

impl Write for Uart {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for c in s.as_bytes() {
            self.write_byte(*c);
        }
        Ok(())
    }
}

// Safe because it just contains a pointer to device memory, which can be accessed from any context.
unsafe impl Send for Uart {}
