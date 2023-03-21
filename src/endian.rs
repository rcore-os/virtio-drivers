//! Endian types used in this library.
//! Each endian type is guarnteed to have the same size and alignment as a regular unsigned primiive
//! of the equal size.
//!
//! # Examples
//!
//! ```
//! # use endian::*;
//!   let b = Be32::from(3);
//!   let l = Le32::from(3);
//!
//!   assert_eq!(b.to_native(), 3);
//!   assert_eq!(l.to_native(), 3);
//!   assert!(b == 3);
//!   assert!(l == 3);
//! ```

use zerocopy::{AsBytes, FromBytes};

macro_rules! endian_type {
    ($old_type:ident, $new_type:ident, $to_new:ident, $from_new:ident) => {
        /// An integer type of with an explicit endianness.
        #[repr(transparent)]
        #[derive(Copy, Clone, Eq, PartialEq, Debug, Default, FromBytes, AsBytes)]
        pub struct $new_type($old_type);

        impl $new_type {
            /// Converts `self` to the native endianness.
            pub fn to_native(self) -> $old_type {
                $old_type::$from_new(self.0)
            }
        }

        impl PartialEq<$old_type> for $new_type {
            fn eq(&self, other: &$old_type) -> bool {
                self.0 == $old_type::$to_new(*other)
            }
        }

        impl PartialEq<$new_type> for $old_type {
            fn eq(&self, other: &$new_type) -> bool {
                $old_type::$to_new(other.0) == *self
            }
        }

        impl From<$new_type> for $old_type {
            fn from(v: $new_type) -> $old_type {
                $old_type::$from_new(v.0)
            }
        }

        impl From<$old_type> for $new_type {
            fn from(v: $old_type) -> $new_type {
                $new_type($old_type::$to_new(v))
            }
        }
    };
}

endian_type!(u16, Le16, to_le, from_le);
endian_type!(u32, Le32, to_le, from_le);
endian_type!(u64, Le64, to_le, from_le);
