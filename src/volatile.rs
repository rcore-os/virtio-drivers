/// An MMIO register which can only be read from.
#[derive(Default)]
#[repr(transparent)]
pub struct ReadOnly<T: Copy>(T);

impl<T: Copy> ReadOnly<T> {
    /// Construct a new instance for testing.
    pub fn new(value: T) -> Self {
        Self(value)
    }
}

/// An MMIO register which can only be written to.
#[derive(Default)]
#[repr(transparent)]
pub struct WriteOnly<T: Copy>(T);

/// An MMIO register which may be both read and written.
#[derive(Default)]
#[repr(transparent)]
pub struct Volatile<T: Copy>(T);

impl<T: Copy> Volatile<T> {
    /// Construct a new instance for testing.
    pub fn new(value: T) -> Self {
        Self(value)
    }

    #[inline]
    fn self_ptr(&self) -> NonNull<T> {
        NonNull::from(&self.0)
    }

    #[inline(always)]
    pub fn read_volatile(&self) -> T {
        unsafe { self.self_ptr().as_ptr().read_volatile() }
    }

    #[inline(always)]
    pub fn write_volatile(&mut self, value: T) {
        unsafe { self.self_ptr().as_ptr().write_volatile(value) }
    }
}

macro_rules! impl_volatile_ops {
    ($($t:ty),*) => {
        $(
            impl AddAssign<$t> for Volatile<$t> {
                fn add_assign(&mut self, rhs: $t) {
                    self.write_volatile(self.read_volatile() + rhs);
                }
            }

            impl Add<$t> for Volatile<$t> {
                type Output = $t;

                fn add(self, rhs: $t) -> $t {
                    self.read_volatile() + rhs
                }
            }

            impl SubAssign<$t> for Volatile<$t> {
                fn sub_assign(&mut self, rhs: $t) {
                    self.write_volatile(self.read_volatile() - rhs);
                }
            }

            impl Sub<$t> for Volatile<$t> {
                type Output = $t;

                fn sub(self, rhs: $t) -> $t {
                    self.read_volatile() - rhs
                }
            }
        )*
    };
}

impl_volatile_ops!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);

/// A trait implemented by MMIO registers which may be read from.
pub trait VolatileReadable<T> {
    /// Performs a volatile read from the MMIO register.
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

/// A trait implemented by MMIO registers which may be written to.
pub trait VolatileWritable<T> {
    /// Performs a volatile write to the MMIO register.
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

/// Performs a volatile read from the given field of pointer to a struct representing an MMIO region.
///
/// # Usage
/// ```compile_fail
/// # use core::ptr::NonNull;
/// # use virtio_drivers::volatile::{ReadOnly, volread};
/// struct MmioDevice {
///   field: ReadOnly<u32>,
/// }
///
/// let device: NonNull<MmioDevice> = NonNull::new(0x1234 as *mut MmioDevice).unwrap();
/// let value = unsafe { volread!(device, field) };
/// ```
macro_rules! volread {
    ($nonnull:expr, $field:ident) => {
        $crate::volatile::VolatileReadable::vread(core::ptr::addr_of!((*$nonnull.as_ptr()).$field))
    };
}

/// Performs a volatile write to the given field of pointer to a struct representing an MMIO region.
///
/// # Usage
/// ```compile_fail
/// # use core::ptr::NonNull;
/// # use virtio_drivers::volatile::{WriteOnly, volread};
/// struct MmioDevice {
///   field: WriteOnly<u32>,
/// }
///
/// let device: NonNull<MmioDevice> = NonNull::new(0x1234 as *mut MmioDevice).unwrap();
/// unsafe { volwrite!(device, field, 42); }
/// ```
macro_rules! volwrite {
    ($nonnull:expr, $field:ident, $value:expr) => {
        $crate::volatile::VolatileWritable::vwrite(
            core::ptr::addr_of_mut!((*$nonnull.as_ptr()).$field),
            $value,
        )
    };
}

use core::{
    ops::{Add, AddAssign, Sub, SubAssign},
    ptr::NonNull,
};

pub(crate) use volread;
pub(crate) use volwrite;
