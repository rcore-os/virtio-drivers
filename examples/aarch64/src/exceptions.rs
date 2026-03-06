//! Exception handlers.

use aarch64_rt::{ExceptionHandlers, exception_handlers};

exception_handlers!(Handlers);

struct Handlers;

impl ExceptionHandlers for Handlers {}
