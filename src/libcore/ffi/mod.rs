#![stable(feature = "", since = "1.30.0")]

#![allow(non_camel_case_types)]

//! Utilities related to FFI bindings.

use ::fmt;

#[doc(include = "ffi/char.md")]
#[cfg(any(all(target_os = "linux", any(target_arch = "aarch64",
                                       target_arch = "arm",
                                       target_arch = "powerpc",
                                       target_arch = "powerpc64",
                                       target_arch = "s390x")),
          all(target_os = "android", any(target_arch = "aarch64",
                                         target_arch = "arm")),
          all(target_os = "l4re", target_arch = "x86_64"),
          all(target_os = "netbsd", any(target_arch = "aarch64",
                                        target_arch = "arm",
                                        target_arch = "powerpc")),
          all(target_os = "openbsd", target_arch = "aarch64"),
          all(target_os = "fuchsia", target_arch = "aarch64")))]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_char = u8;
#[doc(include = "ffi/char.md")]
#[cfg(not(any(all(target_os = "linux", any(target_arch = "aarch64",
                                           target_arch = "arm",
                                           target_arch = "powerpc",
                                           target_arch = "powerpc64",
                                           target_arch = "s390x")),
              all(target_os = "android", any(target_arch = "aarch64",
                                             target_arch = "arm")),
              all(target_os = "l4re", target_arch = "x86_64"),
              all(target_os = "netbsd", any(target_arch = "aarch64",
                                            target_arch = "arm",
                                            target_arch = "powerpc")),
              all(target_os = "openbsd", target_arch = "aarch64"),
              all(target_os = "fuchsia", target_arch = "aarch64"))))]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_char = i8;
#[doc(include = "ffi/schar.md")]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_schar = i8;
#[doc(include = "ffi/uchar.md")]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_uchar = u8;
#[doc(include = "ffi/short.md")]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_short = i16;
#[doc(include = "ffi/ushort.md")]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_ushort = u16;
#[doc(include = "ffi/int.md")]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_int = i32;
#[doc(include = "ffi/uint.md")]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_uint = u32;
#[doc(include = "ffi/long.md")]
#[cfg(any(target_pointer_width = "32", windows))]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_long = i32;
#[doc(include = "ffi/ulong.md")]
#[cfg(any(target_pointer_width = "32", windows))]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_ulong = u32;
#[doc(include = "ffi/long.md")]
#[cfg(all(target_pointer_width = "64", not(windows)))]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_long = i64;
#[doc(include = "ffi/ulong.md")]
#[cfg(all(target_pointer_width = "64", not(windows)))]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_ulong = u64;
#[doc(include = "ffi/longlong.md")]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_longlong = i64;
#[doc(include = "ffi/ulonglong.md")]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_ulonglong = u64;
#[doc(include = "ffi/float.md")]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_float = f32;
#[doc(include = "ffi/double.md")]
#[unstable(feature = "core_ctypes", issue = "0")] pub type c_double = f64;

/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type ptrdiff_t = isize;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type size_t = usize;
/// TODO: docs
#[cfg(windows)]
#[unstable(feature = "core_ctypes", issue = "0")] pub type wchar_t = u16;
/// TODO: docs
#[cfg(all(any(target_arch = "arm", target_arch = "aarch64"),
          not(windows),
          not(target_os = "netbsd"),
          not(target_os = "openbsd")))]
#[unstable(feature = "core_ctypes", issue = "0")] pub type wchar_t = u32;
/// TODO: docs
#[cfg(all(not(windows),
          any(not(any(target_arch = "arm", target_arch = "aarch64")),
              target_os = "netbsd",
              target_os = "openbsd")))]
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type wchar_t = i32;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type wint_t = i32;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type char16_t = u16;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type char32_t = u32;

/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int8_t = i8;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint8_t = u8;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int_least8_t = i8;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint_least8_t = u8;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int_fast8_t = i8;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint_fast8_t = u8;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int16_t = i16;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint16_t = u16;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int_least16_t = i16;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint_least16_t = u16;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int_fast16_t = i16;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint_fast16_t = u16;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int32_t = i32;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint32_t = u32;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int_least32_t = i32;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint_least32_t = u32;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int_fast32_t = i32;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint_fast32_t = u32;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int64_t = i64;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint64_t = u64;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int_least64_t = i64;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint_least64_t = u64;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type int_fast64_t = i64;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uint_fast64_t = u64;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type intmax_t = i64;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uintmax_t = u64;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type intptr_t = isize;
/// TODO: docs
#[unstable(feature = "core_ctypes", issue = "0")] pub type uintptr_t = usize;

/// Equivalent to C's `void` type when used as a [pointer].
///
/// In essence, `*const c_void` is equivalent to C's `const void*`
/// and `*mut c_void` is equivalent to C's `void*`. That said, this is
/// *not* the same as C's `void` return type, which is Rust's `()` type.
///
/// Ideally, this type would be equivalent to [`!`], but currently it may
/// be more ideal to use `c_void` for FFI purposes.
///
/// [`!`]: ../../std/primitive.never.html
/// [pointer]: ../../std/primitive.pointer.html
// NB: For LLVM to recognize the void pointer type and by extension
//     functions like malloc(), we need to have it represented as i8* in
//     LLVM bitcode. The enum used here ensures this and prevents misuse
//     of the "raw" type by only having private variants.. We need two
//     variants, because the compiler complains about the repr attribute
//     otherwise.
#[repr(u8)]
#[stable(feature = "raw_os", since = "1.1.0")]
pub enum c_void {
    #[unstable(feature = "c_void_variant", reason = "should not have to exist",
               issue = "0")]
    #[doc(hidden)] __variant1,
    #[unstable(feature = "c_void_variant", reason = "should not have to exist",
               issue = "0")]
    #[doc(hidden)] __variant2,
}

#[stable(feature = "std_debug", since = "1.16.0")]
impl fmt::Debug for c_void {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("c_void")
    }
}
