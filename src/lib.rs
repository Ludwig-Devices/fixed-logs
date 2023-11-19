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
    fn log2(self) -> U5F27;

    fn checked_log2(self) -> Option<U5F27>;
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
}

pub trait I32Ext {
    fn log2(self) -> U5F27;

    fn checked_log2(self) -> Option<U5F27>;
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn negative_i32() {
        assert_eq!((-1i32).checked_log2(), None);
    }

    #[test]
    fn zero_i32() {
        assert_eq!(0i32.checked_log2(), None);
    }

    #[test]
    fn one_i32() {
        assert_eq!(1i32.log2(), 0);
    }

    #[test]
    fn two_i32() {
        assert_eq!(2i32.log2(), 1);
    }

    #[test]
    fn seven_i32() {
        let expected = U5F27::from_str("2.807354922").unwrap();
        assert_eq!(7i32.log2(), expected);
    }

    #[test]
    fn max_i32() {
        let expected = U5F27::from_str("30.99999999").unwrap();
        assert_eq!(i32::MAX.log2(), expected);
    }

    #[test]
    fn zero_u32() {
        assert_eq!(0u32.checked_log2(), None);
    }

    #[test]
    fn one_u32() {
        assert_eq!(1u32.log2(), 0);
    }

    #[test]
    fn two_u32() {
        assert_eq!(2u32.log2(), 1);
    }

    #[test]
    fn seven_u32() {
        let expected = U5F27::from_str("2.807354922").unwrap();
        assert_eq!(7i32.log2(), expected);
    }

    #[test]
    fn max_u32() {
        let expected = U5F27::from_str("31.99999999").unwrap();
        assert_eq!(u32::MAX.log2(), expected);
    }
}
