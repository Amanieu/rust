// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::ops::*;
use std::cmp::{Ord, PartialOrd, Ordering};

#[derive(Copy, Clone, Default, Eq, PartialEq, Hash, RustcEncodable, RustcDecodable)]
#[repr(C)]
pub struct u128 {
    #[cfg(target_endian = "little")]
    low: u64,
    high: u64,
    #[cfg(target_endian = "big")]
    low: u64,
}

#[derive(Copy, Clone, Default, Eq, PartialEq, Hash, RustcEncodable, RustcDecodable)]
#[repr(C)]
pub struct i128(u128);

macro_rules! forward_ref_unop {
    (impl $imp:ident, $method:ident for $t:ty) => {
        impl<'a> $imp for &'a $t {
            type Output = <$t as $imp>::Output;

            #[inline]
            fn $method(self) -> <$t as $imp>::Output {
                $imp::$method(*self)
            }
        }
    }
}
macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl<'a> $imp<$u> for &'a $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, other)
            }
        }

        impl<'a> $imp<&'a $u> for $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: &'a $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(self, *other)
            }
        }

        impl<'a, 'b> $imp<&'a $u> for &'b $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: &'a $u) -> <$t as $imp<$u>>::Output {
                $imp::$method(*self, *other)
            }
        }
    }
}
macro_rules! forward_binop_i128 {
    (impl $imp:ident, $method:ident) => {
        impl $imp<i128> for i128 {
            type Output = i128;

            #[inline]
            fn $method(self, other: i128) -> i128 {
                i128($imp::$method(self.0, other.0))
            }
        }
        forward_ref_binop! { impl $imp, $method for u128, u128 }
        forward_ref_binop! { impl $imp, $method for i128, i128 }
    }
}

impl Add for u128 {
    type Output = u128;

    #[inline]
    fn add(self, other: u128) -> u128 {
        self.wrapping_add(other)
    }
}
forward_binop_i128! { impl Add, add }

impl Sub for u128 {
    type Output = u128;

    #[inline]
    fn sub(self, other: u128) -> u128 {
        self.wrapping_sub(other)
    }
}
forward_binop_i128! { impl Sub, sub }

impl Mul for u128 {
    type Output = u128;

    #[inline]
    fn mul(self, other: u128) -> u128 {
        self.wrapping_mul(other)
    }
}
forward_binop_i128! { impl Mul, mul }

impl Div for u128 {
    type Output = u128;

    #[inline]
    fn div(self, other: u128) -> u128 {
        unimplemented!();
    }
}
impl Div for i128 {
    type Output = i128;

    #[inline]
    fn div(self, other: i128) -> i128 {
        unimplemented!();
    }
}
forward_ref_binop! { impl Div, div for u128, u128 }
forward_ref_binop! { impl Div, div for i128, i128 }

impl Rem for u128 {
    type Output = u128;

    #[inline]
    fn rem(self, other: u128) -> u128 {
        unimplemented!();
    }
}
impl Rem for i128 {
    type Output = i128;

    #[inline]
    fn rem(self, other: i128) -> i128 {
        unimplemented!();
    }
}
forward_ref_binop! { impl Rem, rem for u128, u128 }
forward_ref_binop! { impl Rem, rem for i128, i128 }

impl Neg for i128 {
    type Output = i128;

    #[inline]
    fn neg(self) -> i128 {
        i128(self.0.wrapping_neg())
    }
}
forward_ref_unop! { impl Neg, neg for i128 }

impl Not for u128 {
    type Output = u128;

    #[inline]
    fn not(self) -> u128 {
        u128 {
            low: !self.low,
            high: !self.high,
        }
    }
}
impl Not for i128 {
    type Output = i128;

    #[inline]
    fn not(self) -> i128 {
        i128(self.0.not())
    }
}
forward_ref_unop! { impl Not, not for u128 }
forward_ref_unop! { impl Not, not for i128 }

impl BitAnd for u128 {
    type Output = u128;

    #[inline]
    fn bitand(self, other: u128) -> u128 {
        u128 {
            low: self.low & other.low,
            high: self.high & other.high,
        }
    }
}
forward_binop_i128! { impl BitAnd, bitand }

impl BitOr for u128 {
    type Output = u128;

    #[inline]
    fn bitor(self, other: u128) -> u128 {
        u128 {
            low: self.low | other.low,
            high: self.high | other.high,
        }
    }
}
forward_binop_i128! { impl BitOr, bitor }

impl BitXor for u128 {
    type Output = u128;

    #[inline]
    fn bitxor(self, other: u128) -> u128 {
        u128 {
            low: self.low ^ other.low,
            high: self.high ^ other.high,
        }
    }
}
forward_binop_i128! { impl BitXor, bitxor }

macro_rules! shl_impl {
    ($($f:ty)*) => ($(
        impl Shl<$f> for u128 {
            type Output = u128;

            #[inline]
            fn shl(self, shift: $f) -> u128 {
                let low = if shift & 64 != 0 {
                    0
                } else {
                    self.low << (shift & 63)
                };
                let high = if shift == 0 {
                    self.high
                } else if shift & 64 != 0 {
                    self.low << (shift & 63)
                } else {
                    self.high << shift | self.low >> 64 - (shift & 63)
                };
                u128 {
                    low: low,
                    high: high,
                }
            }
        }
        impl Shl<$f> for i128 {
            type Output = i128;

            #[inline]
            fn shl(self, shift: $f) -> i128 {
                i128(self.0 << shift)
            }
        }

        forward_ref_binop! { impl Shl, shl for u128, $f }
        forward_ref_binop! { impl Shl, shl for i128, $f }
    )*)
}
shl_impl! { u8 u16 u32 u64 usize i8 i16 i32 i64 isize }

macro_rules! shl2_impl {
    ($($t:ty)*) => ($(
        impl Shl<u128> for $t {
            type Output = $t;

            #[inline]
            fn shl(self, shift: u128) -> $t {
                self << shift.low
            }
        }
        impl Shl<i128> for $t {
            type Output = $t;

            #[inline]
            fn shl(self, shift: i128) -> $t {
                self << shift.0.low
            }
        }

        forward_ref_binop! { impl Shl, shl for $t, u128 }
        forward_ref_binop! { impl Shl, shl for $t, i128 }
    )*)
}
shl2_impl! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

macro_rules! shr_impl {
    ($($f:ty)*) => ($(
        impl Shr<$f> for u128 {
            type Output = u128;

            #[inline]
            fn shr(self, shift: $f) -> u128 {
                let low = if shift == 0 {
                    self.low
                } else if shift & 64 != 0 {
                    self.high >> (shift & 63)
                } else {
                    self.low >> shift | self.high << 64 - (shift & 63)
                };
                let high = if shift & 64 != 0 {
                    0
                } else {
                    self.high >> (shift & 63)
                };
                u128 {
                    low: low,
                    high: high,
                }
            }
        }
        impl Shr<$f> for i128 {
            type Output = i128;

            #[inline]
            fn shr(self, shift: $f) -> i128 {
                i128(self.0 >> shift)
            }
        }

        forward_ref_binop! { impl Shr, shr for u128, $f }
        forward_ref_binop! { impl Shr, shr for i128, $f }
    )*)
}
shr_impl! { u8 u16 u32 u64 usize i8 i16 i32 i64 isize }

macro_rules! shr2_impl {
    ($($t:ty)*) => ($(
        impl Shr<u128> for $t {
            type Output = $t;

            #[inline]
            fn shr(self, shift: u128) -> $t {
                self >> shift.low
            }
        }
        impl Shr<i128> for $t {
            type Output = $t;

            #[inline]
            fn shr(self, shift: i128) -> $t {
                self >> shift.0.low
            }
        }

        forward_ref_binop! { impl Shr, shr for $t, u128 }
        forward_ref_binop! { impl Shr, shr for $t, i128 }
    )*)
}
shr2_impl! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

macro_rules! forward_assign {
    (impl $imp:ident, $method:ident, $forward:ident for $t:ty, $($u:ty)*) => ($(
        impl $imp<$u> for $t {
            #[inline]
            fn $method(&mut self, other: $u) {
                *self = self.$forward(other);
            }
        }
    )*)
}
forward_assign! { impl AddAssign, add_assign, add for u128, u128 }
forward_assign! { impl AddAssign, add_assign, add for i128, i128 }
forward_assign! { impl SubAssign, sub_assign, sub for u128, u128 }
forward_assign! { impl SubAssign, sub_assign, sub for i128, i128 }
forward_assign! { impl MulAssign, mul_assign, mul for u128, u128 }
forward_assign! { impl MulAssign, mul_assign, mul for i128, i128 }
forward_assign! { impl DivAssign, div_assign, div for u128, u128 }
forward_assign! { impl DivAssign, div_assign, div for i128, i128 }
forward_assign! { impl RemAssign, rem_assign, rem for u128, u128 }
forward_assign! { impl RemAssign, rem_assign, rem for i128, i128 }
forward_assign! { impl BitAndAssign, bitand_assign, bitand for u128, u128 }
forward_assign! { impl BitAndAssign, bitand_assign, bitand for i128, i128 }
forward_assign! { impl BitOrAssign, bitor_assign, bitor for u128, u128 }
forward_assign! { impl BitOrAssign, bitor_assign, bitor for i128, i128 }
forward_assign! { impl BitXorAssign, bitxor_assign, bitxor for u128, u128 }
forward_assign! { impl BitXorAssign, bitxor_assign, bitxor for i128, i128 }
forward_assign! { impl ShlAssign, shl_assign, shl for u128, u8 u16 u32 u64 u128 usize i8 i16 i32 i64 isize i128 }
forward_assign! { impl ShlAssign, shl_assign, shl for i128, u8 u16 u32 u64 u128 usize i8 i16 i32 i64 isize i128 }

impl PartialOrd for u128 {
    #[inline]
    fn partial_cmp(&self, other: &u128) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for u128 {
    #[inline]
    fn cmp(&self, other: &u128) -> Ordering {
        (self.high, self.low).cmp(&(other.high, other.low))
    }
}
impl PartialOrd for i128 {
    #[inline]
    fn partial_cmp(&self, other: &i128) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for i128 {
    #[inline]
    fn cmp(&self, other: &i128) -> Ordering {
        (self.0.high as i64, self.0.low).cmp(&(other.0.high as i64, other.0.low))
    }
}

impl u128 {
    const MIN: u128 = u128 { low: 0, high: 0 };

    const MAX: u128 = u128 {
        low: !0,
        high: !0,
    };

    #[inline]
    pub fn zero() -> Self {
        u128 { low: 0, high: 0 }
    }

    #[inline]
    pub fn one() -> Self {
        u128 { low: 1, high: 0 }
    }

    #[inline]
    pub const fn min_value() -> Self {
        Self::MIN
    }

    #[inline]
    pub const fn max_value() -> Self {
        Self::MAX
    }

    // pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
    // from_str_radix(src, radix)
    // }

    #[inline]
    pub fn count_ones(self) -> u32 {
        self.low.count_ones() + self.high.count_ones()
    }

    #[inline]
    pub fn count_zeros(self) -> u32 {
        (!self).count_ones()
    }

    #[inline]
    pub fn leading_zeros(self) -> u32 {
        if self.high == 0 {
            self.low.leading_zeros() + 64
        } else {
            self.high.leading_zeros()
        }
    }

    #[inline]
    pub fn trailing_zeros(self) -> u32 {
        if self.low == 0 {
            self.high.trailing_zeros() + 64
        } else {
            self.low.trailing_zeros()
        }
    }

    #[inline]
    pub fn rotate_left(self, n: u32) -> Self {
        let n = n % 128;
        (self << n) | (self >> ((128 - n) % 128))
    }

    #[inline]
    pub fn rotate_right(self, n: u32) -> Self {
        let n = n % 128;
        (self >> n) | (self << ((128 - n) % 128))
    }

    #[inline]
    pub fn swap_bytes(self) -> Self {
        u128 {
            low: self.high.swap_bytes(),
            high: self.low.swap_bytes(),
        }
    }

    #[inline]
    pub fn from_be(x: Self) -> Self {
        if cfg!(target_endian = "big") {
            x
        } else {
            x.swap_bytes()
        }
    }

    #[inline]
    pub fn from_le(x: Self) -> Self {
        if cfg!(target_endian = "little") {
            x
        } else {
            x.swap_bytes()
        }
    }

    #[inline]
    pub fn to_be(self) -> Self {
        // or not to be?
        if cfg!(target_endian = "big") {
            self
        } else {
            self.swap_bytes()
        }
    }

    #[inline]
    pub fn to_le(self) -> Self {
        if cfg!(target_endian = "little") {
            self
        } else {
            self.swap_bytes()
        }
    }

    #[inline]
    pub fn checked_add(self, other: Self) -> Option<Self> {
        let (a, b) = self.overflowing_add(other);
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        let (a, b) = self.overflowing_sub(other);
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        let (a, b) = self.overflowing_mul(other);
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn checked_div(self, other: Self) -> Option<Self> {
        if other == Self::zero() {
            None
        } else {
            Some(self / other)
        }
    }

    #[inline]
    pub fn checked_rem(self, other: Self) -> Option<Self> {
        if other == Self::zero() {
            None
        } else {
            Some(self % other)
        }
    }

    #[inline]
    pub fn checked_neg(self) -> Option<Self> {
        let (a, b) = self.overflowing_neg();
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn checked_shl(self, rhs: u32) -> Option<Self> {
        let (a, b) = self.overflowing_shl(rhs);
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn checked_shr(self, rhs: u32) -> Option<Self> {
        let (a, b) = self.overflowing_shr(rhs);
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn saturating_add(self, other: Self) -> Self {
        match self.checked_add(other) {
            Some(x) => x,
            None => Self::max_value(),
        }
    }

    #[inline]
    pub fn saturating_sub(self, other: Self) -> Self {
        match self.checked_sub(other) {
            Some(x) => x,
            None => Self::min_value(),
        }
    }

    #[inline]
    pub fn saturating_mul(self, other: Self) -> Self {
        self.checked_mul(other).unwrap_or(Self::max_value())
    }

    #[inline]
    pub fn wrapping_add(self, rhs: Self) -> Self {
        let (low, carry) = self.low.overflowing_add(rhs.low);
        let high = self.high.wrapping_add(rhs.high);
        u128 {
            high: high.wrapping_add(carry as u64),
            low: low,
        }
    }

    #[inline]
    pub fn wrapping_sub(self, rhs: Self) -> Self {
        let (low, borrow) = self.low.overflowing_sub(rhs.low);
        let high = self.high.wrapping_sub(rhs.high);
        u128 {
            high: high.wrapping_sub(borrow as u64),
            low: low,
        }
    }

    #[inline]
    pub fn wrapping_mul(self, rhs: Self) -> Self {
        unimplemented!();
    }

    #[inline(always)]
    pub fn wrapping_div(self, rhs: Self) -> Self {
        self / rhs
    }

    #[inline(always)]
    pub fn wrapping_rem(self, rhs: Self) -> Self {
        self % rhs
    }

    #[inline(always)]
    pub fn wrapping_neg(self) -> Self {
        self.overflowing_neg().0
    }

    #[inline(always)]
    pub fn wrapping_shl(self, rhs: u32) -> Self {
        self.overflowing_shl(rhs).0
    }

    #[inline(always)]
    pub fn wrapping_shr(self, rhs: u32) -> Self {
        self.overflowing_shr(rhs).0
    }

    #[inline]
    pub fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        unimplemented!();
    }

    #[inline]
    pub fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        unimplemented!();
    }

    #[inline]
    pub fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        unimplemented!();
    }

    #[inline]
    pub fn overflowing_div(self, rhs: Self) -> (Self, bool) {
        (self / rhs, false)
    }

    #[inline]
    pub fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
        (self % rhs, false)
    }

    #[inline]
    pub fn overflowing_neg(self) -> (Self, bool) {
        ((!self).wrapping_add(Self::one()), self != Self::zero())
    }

    #[inline]
    pub fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
        (self << (rhs & (128 - 1)), (rhs > (128 - 1)))
    }

    #[inline]
    pub fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
        (self >> (rhs & (128 - 1)), (rhs > (128 - 1)))
    }

    #[inline]
    pub fn pow(self, mut exp: u32) -> Self {
        let mut base = self;
        let mut acc = Self::one();

        let mut prev_base = self;
        let mut base_oflo = false;
        while exp > 0 {
            if (exp & 1) == 1 {
                if base_oflo {
                    acc = acc * (prev_base * prev_base);
                } else {
                    acc = acc * base;
                }
            }
            prev_base = base;
            let (new_base, new_base_oflo) = base.overflowing_mul(base);
            base = new_base;
            base_oflo = new_base_oflo;
            exp /= 2;
        }
        acc
    }

    #[inline]
    pub fn is_power_of_two(self) -> bool {
        (self.wrapping_sub(Self::one())) & self == Self::zero() && !(self == Self::zero())
    }

    #[inline]
    pub fn next_power_of_two(self) -> Self {
        let bits = 128;
        let one: Self = Self::one();
        one << ((bits - self.wrapping_sub(one).leading_zeros() as usize) % bits)
    }

    pub fn checked_next_power_of_two(self) -> Option<Self> {
        let npot = self.next_power_of_two();
        if npot >= self {
            Some(npot)
        } else {
            None
        }
    }

    #[inline]
    pub fn as_u8(self) -> u8 {
        self.low as u8
    }
    #[inline]
    pub fn as_i8(self) -> i8 {
        self.low as i8
    }
    #[inline]
    pub fn as_u16(self) -> u16 {
        self.low as u16
    }
    #[inline]
    pub fn as_i16(self) -> i16 {
        self.low as i16
    }
    #[inline]
    pub fn as_u32(self) -> u32 {
        self.low as u32
    }
    #[inline]
    pub fn as_i32(self) -> i32 {
        self.low as i32
    }
    #[inline]
    pub fn as_u64(self) -> u64 {
        self.low as u64
    }
    #[inline]
    pub fn as_i64(self) -> i64 {
        self.low as i64
    }
    #[inline]
    pub fn as_usize(self) -> usize {
        self.low as usize
    }
    #[inline]
    pub fn as_isize(self) -> isize {
        self.low as isize
    }
    #[inline]
    pub fn as_u128(self) -> u128 {
        self
    }
    #[inline]
    pub fn as_i128(self) -> i128 {
        i128(self)
    }
}

impl i128 {
    const MIN: i128 = i128(u128 {
        low: 0,
        high: 0x8000000000000000,
    });

    const MAX: i128 = i128(u128 {
        low: !0,
        high: 0x7fffffffffffffff,
    });


    #[inline]
    pub fn zero() -> Self {
        i128(u128::zero())
    }

    #[inline]
    pub fn one() -> Self {
        i128(u128::zero())
    }

    #[inline]
    pub const fn min_value() -> Self {
        Self::MIN
    }

    #[inline]
    pub const fn max_value() -> Self {
        Self::MAX
    }

    // pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
    // from_str_radix(src, radix)
    // }

    #[inline]
    pub fn count_ones(self) -> u32 {
        self.0.count_ones()
    }

    #[inline]
    pub fn count_zeros(self) -> u32 {
        (!self).count_ones()
    }

    #[inline]
    pub fn leading_zeros(self) -> u32 {
        self.0.leading_zeros()
    }

    #[inline]
    pub fn trailing_zeros(self) -> u32 {
        self.0.trailing_zeros()
    }

    #[inline]
    pub fn rotate_left(self, n: u32) -> Self {
        i128(self.0.rotate_left(n))
    }

    #[inline]
    pub fn rotate_right(self, n: u32) -> Self {
        i128(self.0.rotate_right(n))
    }

    #[inline]
    pub fn swap_bytes(self) -> Self {
        i128(self.0.swap_bytes())
    }

    #[inline]
    pub fn from_be(x: Self) -> Self {
        if cfg!(target_endian = "big") {
            x
        } else {
            x.swap_bytes()
        }
    }

    #[inline]
    pub fn from_le(x: Self) -> Self {
        if cfg!(target_endian = "little") {
            x
        } else {
            x.swap_bytes()
        }
    }

    #[inline]
    pub fn to_be(self) -> Self {
        if cfg!(target_endian = "big") {
            self
        } else {
            self.swap_bytes()
        }
    }

    #[inline]
    pub fn to_le(self) -> Self {
        if cfg!(target_endian = "little") {
            self
        } else {
            self.swap_bytes()
        }
    }

    #[inline]
    pub fn checked_add(self, other: Self) -> Option<Self> {
        let (a, b) = self.overflowing_add(other);
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn checked_sub(self, other: Self) -> Option<Self> {
        let (a, b) = self.overflowing_sub(other);
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn checked_mul(self, other: Self) -> Option<Self> {
        let (a, b) = self.overflowing_mul(other);
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn checked_div(self, other: Self) -> Option<Self> {
        if other == Self::zero() {
            None
        } else {
            let (a, b) = self.overflowing_div(other);
            if b {
                None
            } else {
                Some(a)
            }
        }
    }

    #[inline]
    pub fn checked_rem(self, other: Self) -> Option<Self> {
        if other == Self::zero() {
            None
        } else {
            let (a, b) = self.overflowing_rem(other);
            if b {
                None
            } else {
                Some(a)
            }
        }
    }

    #[inline]
    pub fn checked_neg(self) -> Option<Self> {
        let (a, b) = self.overflowing_neg();
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn checked_shl(self, rhs: u32) -> Option<Self> {
        let (a, b) = self.overflowing_shl(rhs);
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn checked_shr(self, rhs: u32) -> Option<Self> {
        let (a, b) = self.overflowing_shr(rhs);
        if b {
            None
        } else {
            Some(a)
        }
    }

    #[inline]
    pub fn saturating_add(self, other: Self) -> Self {
        match self.checked_add(other) {
            Some(x) => x,
            None if other >= Self::zero() => Self::max_value(),
            None => Self::min_value(),
        }
    }

    #[inline]
    pub fn saturating_sub(self, other: Self) -> Self {
        match self.checked_sub(other) {
            Some(x) => x,
            None if other >= Self::zero() => Self::min_value(),
            None => Self::max_value(),
        }
    }

    #[inline]
    pub fn saturating_mul(self, other: Self) -> Self {
        self.checked_mul(other).unwrap_or_else(|| {
            if (self.is_negative() && self.is_negative()) ||
               (self.is_positive() && other.is_positive()) {
                Self::max_value()
            } else {
                Self::min_value()
            }
        })
    }

    #[inline]
    pub fn wrapping_add(self, rhs: Self) -> Self {
        i128(self.0.wrapping_add(rhs.0))
    }

    #[inline]
    pub fn wrapping_sub(self, rhs: Self) -> Self {
        i128(self.0.wrapping_sub(rhs.0))
    }

    #[inline]
    pub fn wrapping_mul(self, rhs: Self) -> Self {
        i128(self.0.wrapping_mul(rhs.0))
    }

    #[inline(always)]
    pub fn wrapping_div(self, rhs: Self) -> Self {
        self / rhs
    }

    #[inline(always)]
    pub fn wrapping_rem(self, rhs: Self) -> Self {
        self % rhs
    }

    #[inline(always)]
    pub fn wrapping_neg(self) -> Self {
        self.overflowing_neg().0
    }

    #[inline(always)]
    pub fn wrapping_shl(self, rhs: u32) -> Self {
        self.overflowing_shl(rhs).0
    }

    #[inline(always)]
    pub fn wrapping_shr(self, rhs: u32) -> Self {
        self.overflowing_shr(rhs).0
    }

    #[inline]
    pub fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        unimplemented!();
    }

    #[inline]
    pub fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        unimplemented!();
    }

    #[inline]
    pub fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        unimplemented!();
    }

    #[inline]
    pub fn overflowing_div(self, rhs: Self) -> (Self, bool) {
        (self / rhs, false)
    }

    #[inline]
    pub fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
        (self % rhs, false)
    }

    #[inline]
    pub fn overflowing_neg(self) -> (Self, bool) {
        ((!self).wrapping_add(Self::one()), self != Self::zero())
    }

    #[inline]
    pub fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
        (self << (rhs & (128 - 1)), (rhs > (128 - 1)))
    }

    #[inline]
    pub fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
        (self >> (rhs & (128 - 1)), (rhs > (128 - 1)))
    }

    #[inline]
    pub fn pow(self, mut exp: u32) -> Self {
        let mut base = self;
        let mut acc = Self::one();

        while exp > 1 {
            if (exp & 1) == 1 {
                acc = acc * base;
            }
            exp /= 2;
            base = base * base;
        }

        if exp == 1 {
            acc = acc * base;
        }

        acc
    }

    #[inline]
    pub fn abs(self) -> Self {
        if self.is_negative() {
            -self
        } else {
            self
        }
    }

    #[inline]
    pub fn signum(self) -> Self {
        match self {
            n if n.is_positive() => Self::one(),
            n if n.is_negative() => -Self::one(),
            _ => Self::zero(),
        }
    }

    #[inline]
    pub fn is_positive(self) -> bool {
        !self.is_negative() && self != Self::zero()
    }

    #[inline]
    pub fn is_negative(self) -> bool {
        self.0.high >> 63 != 0
    }

    #[inline]
    pub fn as_u8(self) -> u8 {
        self.0.low as u8
    }
    #[inline]
    pub fn as_i8(self) -> i8 {
        self.0.low as i8
    }
    #[inline]
    pub fn as_u16(self) -> u16 {
        self.0.low as u16
    }
    #[inline]
    pub fn as_i16(self) -> i16 {
        self.0.low as i16
    }
    #[inline]
    pub fn as_u32(self) -> u32 {
        self.0.low as u32
    }
    #[inline]
    pub fn as_i32(self) -> i32 {
        self.0.low as i32
    }
    #[inline]
    pub fn as_u64(self) -> u64 {
        self.0.low as u64
    }
    #[inline]
    pub fn as_i64(self) -> i64 {
        self.0.low as i64
    }
    #[inline]
    pub fn as_usize(self) -> usize {
        self.0.low as usize
    }
    #[inline]
    pub fn as_isize(self) -> isize {
        self.0.low as isize
    }
    #[inline]
    pub fn as_u128(self) -> u128 {
        self.0
    }
    #[inline]
    pub fn as_i128(self) -> i128 {
        self
    }
}

pub trait AsInt128 {
    fn as_i128(&self) -> i128;
    fn as_u128(&self) -> u128;
}

macro_rules! impl_as_int128 {
    ($($t:ty)*) => {$(
        impl AsInt128 for $t {
            #[inline]
            fn as_i128(&self) -> i128 {
                i128(self.as_u128())
            }

            #[inline]
            fn as_u128(&self) -> u128 {
                u128 {
                    low: *self as u64,
                    high: 0,
                }
            }
        }
    )*}
}
impl_as_int128!{ u8 u16 u32 u64 usize i8 i16 i32 i64 isize }

macro_rules! impl_from {
    ($Small: ty, $Large: ty, $as_large: ident) => {
        impl From<$Small> for $Large {
            #[inline]
            fn from(small: $Small) -> $Large {
                small.$as_large()
            }
        }
    }
}

// Unsigned -> Unsigned
impl_from! { u8, u128, as_u128 }
impl_from! { u16, u128, as_u128 }
impl_from! { u32, u128, as_u128 }
impl_from! { u64, u128, as_u128 }
impl_from! { usize, u128, as_u128 }

// Signed -> Signed
impl_from! { i8, i128, as_i128 }
impl_from! { i16, i128, as_i128 }
impl_from! { i32, i128, as_i128 }
impl_from! { i64, i128, as_i128 }
impl_from! { isize, i128, as_i128 }

// Unsigned -> Signed
impl_from! { u8, i128, as_i128 }
impl_from! { u16, i128, as_i128 }
impl_from! { u32, i128, as_i128 }
impl_from! { u64, i128, as_i128 }
impl_from! { usize, i128, as_i128 }

// TODO: from_str_radix, FromStr, Debug, Display, Binary, Octal, LowerHex, UpperHex



