//! Minimal driver for an 8250 UART. This only implements enough to work with the emulated 8250
//! provided by crosvm, and won't work with real hardware.

use core::fmt::{self, Write};
use safe_mmio::{fields::WriteOnly, UniqueMmioPointer};

/// Minimal driver for an 8250 UART. This only implements enough to work with the emulated 8250
/// provided by crosvm, and won't work with real hardware.
pub struct Uart<'a> {
    base_address: UniqueMmioPointer<'a, WriteOnly<u8>>,
}

impl<'a> Uart<'a> {
    /// Constructs a new instance of the UART driver for a device at the given base address.
    pub fn new(base_address: UniqueMmioPointer<'a, WriteOnly<u8>>) -> Self {
        Self { base_address }
    }

    /// Writes a single byte to the UART.
    pub fn write_byte(&mut self, byte: u8) {
        self.base_address.write(byte);
    }
}

impl Write for Uart<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for c in s.as_bytes() {
            self.write_byte(*c);
        }
        Ok(())
    }
}
