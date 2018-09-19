// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Platform-specific types, as defined by C.
//!
//! Code that interacts via FFI will almost certainly be using the
//! base types provided by C, which aren't nearly as nicely defined
//! as Rust's primitive types. This module provides types which will
//! match those defined by C, so that code that interacts with C will
//! refer to the correct types.

#![stable(feature = "raw_os", since = "1.1.0")]

use core::ffi;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/char.md")]
pub type c_char = ffi::c_char;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/schar.md")]
pub type c_schar = ffi::c_schar;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/uchar.md")]
pub type c_uchar = ffi::c_uchar;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/short.md")]
pub type c_short = ffi::c_short;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/ushort.md")]
pub type c_ushort = ffi::c_ushort;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/int.md")]
pub type c_int = ffi::c_int;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/uint.md")]
pub type c_uint = ffi::c_uint;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/long.md")]
pub type c_long = ffi::c_long;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/ulong.md")]
pub type c_ulong = ffi::c_ulong;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/longlong.md")]
pub type c_longlong = ffi::c_longlong;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/ulonglong.md")]
pub type c_ulonglong = ffi::c_ulonglong;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/float.md")]
pub type c_float = ffi::c_float;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(include = "../libcore/ffi/double.md")]
pub type c_double = ffi::c_double;

#[stable(feature = "raw_os", since = "1.1.0")]
#[doc(no_inline)]
pub use core::ffi::c_void;

#[cfg(test)]
#[allow(unused_imports)]
mod tests {
    use any::TypeId;
    use libc;
    use mem;

    macro_rules! ok {
        ($($t:ident)*) => {$(
            assert!(TypeId::of::<libc::$t>() == TypeId::of::<raw::$t>(),
                    "{} is wrong", stringify!($t));
        )*}
    }

    #[test]
    fn same() {
        use os::raw;
        ok!(c_char c_schar c_uchar c_short c_ushort c_int c_uint c_long c_ulong
            c_longlong c_ulonglong c_float c_double);
    }
}
