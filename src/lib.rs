#![cfg_attr(not(test), no_std)]

use core::num::NonZeroU32;
use fixed::types::{U2F30, U5F27};

trait NonZeroU32Ext {
    fn log2(self) -> U5F27;
}

impl NonZeroU32Ext for NonZeroU32 {
    fn log2(self) -> U5F27 {
        let mut y = U5F27::from_num(self.ilog2());
        let mut x = if y < 31 {
            U2F30::from_bits(u32::from(self) << (30 - y.to_num::<u32>()))
        } else {
            U2F30::from_bits(u32::from(self) >> (y.to_num::<u32>() - 30))
        };

        for i in 0..27 {
            x = x * x;
            if x > U2F30::from_num(2) {
                x >>= 1;
                y |= U5F27::from_bits(1 << (27 - i - 1));
            }
        }

        y
    }
}

pub trait U32Ext {
    fn checked_log2(self) -> Option<U5F27>;

    fn log2(self) -> U5F27;

    fn checked_log10(self) -> Option<U5F27>;

    fn log10(self) -> U5F27;

    fn checked_log(self, base: Self) -> Option<U5F27>;

    fn log(self, base: Self) -> U5F27;
}

impl U32Ext for u32 {
    /// Returns `Some` the base-2 logarithm of `self` as a fixed-point number, or `None`
    /// if `self` is zero.
    fn checked_log2(self) -> Option<U5F27> {
        if let Some(x) = NonZeroU32::new(self) {
            Some(x.log2())
        } else {
            None
        }
    }

    /// Returns the base-2 logarithm of `self` as a fixed-point number.
    ///
    /// # Panics
    ///
    /// Panics if `self` is zero.
    fn log2(self) -> U5F27 {
        if let Some(y) = self.checked_log2() {
            y
        } else {
            panic!("log2(0) is undefined")
        }
    }

    /// Returns `Some` the base-10 logarithm of `self` as a fixed-point number, or `None`
    /// if `self` is zero.
    fn checked_log10(self) -> Option<U5F27> {
        self.checked_log2().map(|x| x / U5F27::LOG2_10)
    }

    /// Returns the base-10 logarithm of `self` as a fixed-point number.
    ///
    /// # Panics
    ///
    /// Panics if `self` is zero.
    fn log10(self) -> U5F27 {
        if let Some(y) = self.checked_log10() {
            y
        } else {
            panic!("log10(0) is undefined")
        }
    }

    /// Returns `Some(x)`, where `x` is the base-`base` logarithm of `self` as a fixed-point number,
    /// or `None` if `self` is zero.
    fn checked_log(self, base: Self) -> Option<U5F27> {
        if let Some(base) = base.checked_log2() {
            self.checked_log2().map(|x| x / base)
        } else {
            None
        }
    }

    /// Returns the base-`base` logarithm of `self` as a fixed-point number.
    ///
    /// # Panics
    ///
    /// Panics if `self` is zero.
    fn log(self, base: Self) -> U5F27 {
        if let Some(y) = self.checked_log(base) {
            y
        } else {
            panic!("log(x, 0) is undefined")
        }
    }
}

pub trait I32Ext {
    fn checked_log2(self) -> Option<U5F27>;

    fn log2(self) -> U5F27;

    fn checked_log10(self) -> Option<U5F27>;

    fn log10(self) -> U5F27;

    fn checked_log(self, base: Self) -> Option<U5F27>;

    fn log(self, base: Self) -> U5F27;
}

impl I32Ext for i32 {
    /// Returns `Some` the base-2 logarithm of `self` as a fixed-point number, or `None`
    /// if `self` is not positive.
    fn checked_log2(self) -> Option<U5F27> {
        if self > 0 { Some(self as u32) } else { None }.map(|x| x.log2())
    }

    /// Returns the base-2 logarithm of `self` as a fixed-point number.
    ///
    /// # Panics
    ///
    /// Panics if `self` is not positive.
    fn log2(self) -> U5F27 {
        if let Some(y) = self.checked_log2() {
            y
        } else {
            panic!("log2(x) is undefined for non-postive x")
        }
    }

    /// Returns `Some` the base-10 logarithm of `self` as a fixed-point number, or `None`
    /// if `self` is zero.
    fn checked_log10(self) -> Option<U5F27> {
        self.checked_log2().map(|x| x / U5F27::LOG2_10)
    }

    /// Returns the base-10 logarithm of `self` as a fixed-point number.
    ///
    /// # Panics
    ///
    /// Panics if `self` is zero.
    fn log10(self) -> U5F27 {
        if let Some(y) = self.checked_log10() {
            y
        } else {
            panic!("log10(0) is undefined")
        }
    }

    /// Returns `Some(x)`, where `x` is the base-`base` logarithm of `self` as a fixed-point number,
    /// or `None` if `self` is zero.
    fn checked_log(self, base: Self) -> Option<U5F27> {
        if let Some(base) = base.checked_log2() {
            self.checked_log2().map(|x| x / base)
        } else {
            None
        }
    }

    /// Returns the base-`base` logarithm of `self` as a fixed-point number.
    ///
    /// # Panics
    ///
    /// Panics if `self` is zero.
    fn log(self, base: Self) -> U5F27 {
        if let Some(y) = self.checked_log(base) {
            y
        } else {
            panic!("log(x, 0) is undefined")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn log2_zero_u32() {
        assert_eq!(0u32.checked_log2(), None);
    }

    #[test]
    #[should_panic]
    fn panic_log2_zero_u32() {
        0u32.log2();
    }

    #[test]
    fn log2_one_u32() {
        assert_eq!(1u32.log2(), 0);
    }

    #[test]
    fn log2_two_u32() {
        assert_eq!(2u32.log2(), 1);
    }

    #[test]
    fn log2_seven_u32() {
        let expected = U5F27::from_str("2.807354922").unwrap();
        assert_eq!(7i32.log2(), expected);
    }

    #[test]
    fn log2_max_u32() {
        let expected = U5F27::from_str("31.99999999").unwrap();
        assert_eq!(u32::MAX.log2(), expected);
    }

    #[test]
    fn log10_zero_u32() {
        assert_eq!(0u32.checked_log10(), None);
    }

    #[test]
    fn log10_one_u32() {
        assert_eq!(1u32.log10(), 0);
    }

    #[test]
    fn log10_ten_u32() {
        assert_eq!(10u32.log10(), 1);
    }

    #[test]
    fn log_zero_u32() {
        assert_eq!(0u32.checked_log(5), None);
    }

    #[test]
    fn log_one_u32() {
        assert_eq!(1u32.log(5), 0);
    }

    #[test]
    fn log_unit_u32() {
        assert_eq!(5u32.log(5), 1);
    }

    #[test]
    fn log2_negative_i32() {
        assert_eq!((-1i32).checked_log2(), None);
    }

    #[test]
    fn log2_zero_i32() {
        assert_eq!(0i32.checked_log2(), None);
    }

    #[test]
    #[should_panic]
    fn panic_log2_negative_i32() {
        (-1i32).log2();
    }

    #[test]
    #[should_panic]
    fn panic_log2_zero_i32() {
        0i32.log2();
    }

    #[test]
    fn log2_one_i32() {
        assert_eq!(1i32.log2(), 0);
    }

    #[test]
    fn log2_two_i32() {
        assert_eq!(2i32.log2(), 1);
    }

    #[test]
    fn log2_seven_i32() {
        let expected = U5F27::from_str("2.807354922").unwrap();
        assert_eq!(7i32.log2(), expected);
    }

    #[test]
    fn log2_max_i32() {
        let expected = U5F27::from_str("30.99999999").unwrap();
        assert_eq!(i32::MAX.log2(), expected);
    }

    #[test]
    fn log10_zero_i32() {
        assert_eq!(0i32.checked_log10(), None);
    }

    #[test]
    fn log10_one_i32() {
        assert_eq!(1i32.log10(), 0);
    }

    #[test]
    fn log10_ten_i32() {
        assert_eq!(10i32.log10(), 1);
    }

    #[test]
    fn log_zero_i32() {
        assert_eq!(0i32.checked_log(5), None);
    }

    #[test]
    fn log_one_i32() {
        assert_eq!(1i32.log(5), 0);
    }

    #[test]
    fn log_unit_i32() {
        assert_eq!(5i32.log(5), 1);
    }
}
