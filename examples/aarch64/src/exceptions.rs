//! Exception handlers.

use aarch64_rt::{ExceptionHandlers, exception_handlers};
use core::arch::asm;
use log::error;
use smccc::{Hvc, psci::system_off};

exception_handlers!(Handlers);

struct Handlers;

impl ExceptionHandlers for Handlers {}
