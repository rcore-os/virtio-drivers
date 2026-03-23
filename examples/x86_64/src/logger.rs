//! Log implementation using the UART.

use core::fmt::Write;
use log::{LevelFilter, Log, Metadata, Record, SetLoggerError};
use spin::mutex::SpinMutex;
use uart_16550::{Config, Uart16550Tty, backend::PioBackend};

static LOGGER: Logger = Logger {
    uart: SpinMutex::new(None),
};

struct Logger {
    uart: SpinMutex<Option<Uart16550Tty<PioBackend>>>,
}

/// Initialises UART logger.
pub fn init(max_level: LevelFilter) -> Result<(), SetLoggerError> {
    // Safe because `0x3f8` is COM1 I/O port.
    let uart = unsafe { Uart16550Tty::new_port(0x3f8, Config::default()) }
        .expect("Error initialising UART");
    LOGGER.uart.lock().replace(uart);

    log::set_logger(&LOGGER)?;
    log::set_max_level(max_level);
    Ok(())
}

impl Log for Logger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        writeln!(
            LOGGER.uart.lock().as_mut().unwrap(),
            "[{}] {}",
            record.level(),
            record.args()
        )
        .unwrap();
    }

    fn flush(&self) {}
}
