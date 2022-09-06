/// An MMIO register which can only be read from.
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct ReadOnly<T: Copy>(T);

impl<T: Copy> ReadOnly<T> {
    pub const fn new(value: T) -> Self {
        Self(value)
    }
}

/// An MMIO register which can only be written to.
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct WriteOnly<T: Copy>(T);

/// An MMIO register which may be both read and written.
#[derive(Debug, Default)]
#[repr(transparent)]
pub struct Volatile<T: Copy>(T);

impl<T: Copy> Volatile<T> {
    pub const fn new(value: T) -> Self {
        Self(value)
    }
}

pub trait VolatileReadable<T> {
    unsafe fn vread(self) -> T;
}

impl<T: Copy> VolatileReadable<T> for *const ReadOnly<T> {
    unsafe fn vread(self) -> T {
        self.read_volatile().0
    }
}

impl<T: Copy> VolatileReadable<T> for *const Volatile<T> {
    unsafe fn vread(self) -> T {
        self.read_volatile().0
    }
}

pub trait VolatileWritable<T> {
    unsafe fn vwrite(self, value: T);
}

impl<T: Copy> VolatileWritable<T> for *mut WriteOnly<T> {
    unsafe fn vwrite(self, value: T) {
        (self as *mut T).write_volatile(value)
    }
}

impl<T: Copy> VolatileWritable<T> for *mut Volatile<T> {
    unsafe fn vwrite(self, value: T) {
        (self as *mut T).write_volatile(value)
    }
}

macro_rules! volread {
    ($nonnull:expr, $field:ident) => {
        $crate::volatile::VolatileReadable::vread(core::ptr::addr_of!((*$nonnull.as_ptr()).$field))
    };
}

macro_rules! volwrite {
    ($nonnull:expr, $field:ident, $value:expr) => {
        $crate::volatile::VolatileWritable::vwrite(
            core::ptr::addr_of_mut!((*$nonnull.as_ptr()).$field),
            $value,
        )
    };
}

pub(crate) use volread;
pub(crate) use volwrite;
