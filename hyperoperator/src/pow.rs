use crate::root::HyperRoot;

/// Trait for primitive (built-in types) [`Sized`] that adds wrapping and checked hyper exponentiation.
pub trait PrimitiveUintHyperPow {
    /// Wrapping (modular) hyper exponentiation.
    /// Computes self.hyperpow(exp), wrapping around at the boundary of the type.
    ///
    /// `n` parameter:
    /// - n = 0 - exponentiation
    /// - n = 1 - exponentiation
    /// - n = 2 - tetration
    /// - n = 3 - pentation
    /// - n = 4 - hexation
    /// ...
    ///
    /// ```
    /// use hyperoperator::pow::PrimitiveUintHyperPow;
    ///
    /// # fn main() {
    /// let a: u64 = 3;
    /// let b: u64 = 3;
    /// assert_eq!(a.wrapping_hyperpow(b, 2), 7625597484987_u64);
    /// # }
    /// ```
    ///
    fn wrapping_hyperpow(self, exponent: Self, n: u8) -> Self
    where
        Self: Sized;
    /// Checked hyper exponentiation.
    /// Computes self.hyperpow(exp), returning None if overflow occurred.
    ///
    /// `n` parameter:
    /// - n = 0 - exponentiation
    /// - n = 1 - exponentiation
    /// - n = 2 - tetration
    /// - n = 3 - pentation
    /// - n = 4 - hexation
    /// - ...
    ///
    /// ```
    /// use hyperoperator::pow::PrimitiveUintHyperPow;
    ///
    /// # fn main() {
    /// let a: u64 = 2;
    /// let b: u64 = 5;
    /// assert_eq!(a.checked_hyperpow(b, 2), None);
    /// # }
    /// ```
    ///
    fn checked_hyperpow(self, exponent: Self, n: u8) -> Option<Self>
    where
        Self: Sized;
}

macro_rules! hyperpow_unsigned_integer_impl {
    ($TYPE: ty) => {
        impl PrimitiveUintHyperPow for $TYPE {
            fn wrapping_hyperpow(self, exponent: Self, n: u8) -> Self {
                if exponent == 0 {
                    return (1 as $TYPE);
                }

                if exponent == 1 {
                    return self;
                }

                if n == 0 || n == 1 {
                    return self.clone().wrapping_pow(exponent.try_into().unwrap());
                }

                let mut exp = exponent;
                let mut result = (1 as $TYPE);
                while exp > 0 {
                    result = self.clone().wrapping_hyperpow(result, n - 1);
                    exp -= 1;
                }
                return result;
            }

            fn checked_hyperpow(self, exponent: Self, n: u8) -> Option<Self> {
                if exponent == 0 {
                    return Some((1 as $TYPE));
                }

                if exponent == 1 {
                    return Some(self);
                }

                if n == 0 || n == 1 {
                    return self.clone().checked_pow(exponent.try_into().unwrap());
                }

                let mut exp = exponent;
                let mut result = Some(1 as $TYPE);
                while exp > 0 {
                    match result {
                        None => return None,
                        Some(value) => result = self.clone().checked_hyperpow(value, n - 1),
                    }
                    exp -= 1;
                }
                return result;
            }
        }
    };
}

hyperpow_unsigned_integer_impl!(u8);
hyperpow_unsigned_integer_impl!(u16);
hyperpow_unsigned_integer_impl!(u32);
hyperpow_unsigned_integer_impl!(u64);
hyperpow_unsigned_integer_impl!(u128);
hyperpow_unsigned_integer_impl!(usize);

pub trait PrimitiveFloatHyperPow {
    /// Raises a number to an integer hyper power.
    ///
    /// Using this function is generally faster than using powf.
    /// It might have a different sequence of rounding operations than powf,
    /// so the results are not guaranteed to agree.
    ///
    /// `n` parameter:
    /// - n = 0 - exponentiation
    /// - n = 1 - exponentiation
    /// - n = 2 - tetration
    /// - n = 3 - pentation
    /// - n = 4 - hexation
    /// - ...
    ///
    /// ```
    /// use hyperoperator::pow::PrimitiveFloatHyperPow;
    ///
    /// # fn main() {
    /// assert_eq!(2.0_f64.hyperpowi(4, 2), 65536.0);
    /// assert_eq!(2.5_f64.hyperpowi(3, 2), 8560.319976146011);
    /// # }
    /// ```
    ///
    fn hyperpowi(self, exponent: i32, n: u8) -> Self
    where
        Self: Sized;
    /// Raises a number to a floating point hyper power.
    ///
    /// `n` parameter:
    /// - n = 0 - exponentiation
    /// - n = 1 - exponentiation
    /// - n = 2 - tetration
    /// - n = 3 - pentation
    /// - n = 4 - hexation
    /// - ...
    ///
    /// ```
    /// use hyperoperator::pow::PrimitiveFloatHyperPow;
    ///
    /// # fn main() {
    /// assert_eq!(2.0_f64.hyperpowf(3.0, 2), 16.0);
    /// assert_eq!(2.0_f64.hyperpowf(2.5, 2), 7.71540789592915);
    /// # }
    /// ```
    ///
    fn hyperpowf(self, exponent: Self, n: u8) -> Self
    where
        Self: Sized;
    /// Returns `self.hyperpow(e, n)`, (the hyper exponential function).
    ///
    /// `n` parameter:
    /// - n = 0 - exponentiation
    /// - n = 1 - exponentiation
    /// - n = 2 - tetration
    /// - n = 3 - pentation
    /// - n = 4 - hexation
    /// - ...
    ///
    /// ```
    /// use hyperoperator::pow::PrimitiveFloatHyperPow;
    ///
    /// # fn main() {
    /// assert_eq!(2.0_f64.hyperexp(2), 15.154262241479259);
    /// assert_eq!(2.5_f64.hyperexp(2), 340.7674008744644);
    /// # }
    /// ```
    ///
    fn hyperexp(self, n: u8) -> Self
    where
        Self: Sized;
}

macro_rules! hyperpow_float_impl {
    ($TYPE: ty) => {
        impl PrimitiveFloatHyperPow for $TYPE {
            fn hyperpowi(self, exponent: i32, n: u8) -> Self {
                if exponent == 0 {
                    return (1 as $TYPE);
                }

                if exponent == 1 {
                    return self;
                }

                if n == 0 || n == 1 {
                    return self.clone().powi(exponent);
                }

                let mut exp = exponent;
                let mut result = (1 as $TYPE);
                while exp > 0 {
                    result = self.clone().hyperpowf(result, n - 1);
                    exp -= 1;
                }
                return result;
            }

            fn hyperpowf(self, exponent: $TYPE, n: u8) -> Self {
                fn recursive_hyperpow(
                    base: $TYPE,
                    exponent: $TYPE,
                    n: u8,
                    precision: f64,
                ) -> $TYPE {
                    if exponent == 0.0 {
                        return (1 as $TYPE);
                    }

                    if exponent == 1.0 {
                        return base;
                    }

                    if n == 0 || n == 1 {
                        return base.clone().powf(exponent);
                    }

                    return match (exponent, precision) {
                        (exponent, _) if (exponent < 0.0) => 1.0,
                        (exponent, _) if (exponent >= 10.0) => {
                            recursive_hyperpow(base, exponent / 2.0, n, precision / 2.0)
                                .hypersqrt(n)
                        }
                        (exponent, _) if (exponent >= 1.0) => recursive_hyperpow(
                            base,
                            recursive_hyperpow(base, exponent - 1.0, n, precision),
                            n - 1,
                            precision,
                        ),
                        (_, precision) if (precision >= 1.0) => base.hypersqrt(n),
                        (_, precision) => {
                            recursive_hyperpow(base, exponent * 2.0, n, precision * 2.0)
                                .hypersqrt(n)
                        }
                    };
                }
                return recursive_hyperpow(self, exponent, n, 0.0000000000000001_f64);
            }

            fn hyperexp(self, n: u8) -> Self {
                return (std::f64::consts::E as $TYPE).hyperpowf(self, n);
            }
        }
    };
}

hyperpow_float_impl!(f32);
hyperpow_float_impl!(f64);

/// Trait for [`Sized`] that adds `hyperpow` operation (hyper exponentiation).
///
/// BigUint:
///
/// ```
/// use num_bigint::ToBigUint;
/// use hyperoperator::pow::HyperPow;
/// use num_bigint::BigUint;
/// use std::str::FromStr;
///
/// # fn main() {
/// let a = 5_i32.to_biguint().unwrap();
/// let b = 2_i32.to_biguint().unwrap();
/// assert_eq!(a.hyperpow(b, 2), BigUint::from_str("3125").unwrap());
/// # }
/// ```
///
/// BigFloat:
///
/// ```
/// use num_bigfloat::BigFloat;
/// use hyperoperator::pow::HyperPow;
///
/// # fn main() {
/// let a = BigFloat::parse("2.4").unwrap();
/// let b = BigFloat::parse("2.6").unwrap();
/// assert_eq!(a.hyperpow(b, 2).to_string(), "1.042500508439915903472643420925599720010e+2");
/// # }
/// ```
///
pub trait HyperPow<T> {
    /// Raises self to the hyper power of `exponent`
    ///
    /// `n` parameter:
    /// - n = 0 - exponentiation
    /// - n = 1 - exponentiation
    /// - n = 2 - tetration
    /// - n = 3 - pentation
    /// - n = 4 - hexation
    /// - ...
    ///
    fn hyperpow(self, exponent: T, n: u8) -> Self
    where
        Self: Sized;
}

#[cfg(feature = "num_bigint")]
use num_bigint::BigUint;
#[cfg(any(feature = "num_bigint", feature = "num_bigfloat"))]
use num_traits::{One, Pow, Zero};
#[cfg(feature = "num_bigint")]
use std::ops::Sub;

#[cfg(feature = "num_bigint")]
impl HyperPow<BigUint> for BigUint {
    fn hyperpow(self, exponent: BigUint, n: u8) -> Self {
        if exponent == Zero::zero() {
            return One::one();
        }

        if exponent == One::one() {
            return self;
        }

        if n == 0 || n == 1 {
            return self.pow(exponent);
        }

        let mut exp = exponent;
        let mut result = One::one();
        while exp > Zero::zero() {
            result = self.clone().hyperpow(result, n - 1);
            exp = exp.clone().sub(1_u8);
        }
        result
    }
}

#[cfg(feature = "num_bigfloat")]
use num_bigfloat::BigFloat;
#[cfg(feature = "num_bigfloat")]
use num_bigfloat::{ONE, TWO, ZERO};

#[cfg(feature = "num_bigfloat")]
impl HyperPow<BigFloat> for BigFloat {
    fn hyperpow(self, exponent: BigFloat, n: u8) -> Self {
        fn recursive_hyperpow(
            base: BigFloat,
            exponent: BigFloat,
            n: u8,
            precision: f64,
        ) -> BigFloat {
            if exponent == ZERO {
                return ONE;
            }

            if exponent == ONE {
                return base;
            }

            if n == 0 || n == 1 {
                return base.pow(exponent);
            }

            match (exponent, precision) {
                (exponent, _) if (exponent < ZERO) => ONE,
                (exponent, _) if (exponent >= BigFloat::parse("10.0").unwrap()) => {
                    recursive_hyperpow(base, exponent / TWO, n, precision / 2.0).hypersqrt(n)
                }
                (exponent, _) if (exponent >= ONE) => recursive_hyperpow(
                    base,
                    recursive_hyperpow(base, exponent - ONE, n, precision),
                    n - 1,
                    precision,
                ),
                (_, precision) if (precision >= 1.0) => base.hypersqrt(n),
                (_, precision) => {
                    recursive_hyperpow(base, exponent * TWO, n, precision * 2.0).hypersqrt(n)
                }
            }
        }
        recursive_hyperpow(self, exponent, n, 0.0000000000000001_f64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsigned_integer_hyperpow() {
        macro_rules! parameterized_test_unsigned_integer_wrapping_hyperpow {
            ($($t:ty)+) => {
                $(
                    // wrapping_hyperpow
                    assert_eq!((2 as $t).wrapping_hyperpow((0 as $t), u8::MAX), (1 as $t)); // 2[255]0 = 1
                    assert_eq!((2 as $t).wrapping_hyperpow((1 as $t), u8::MAX), (2 as $t)); // 2[255]1 = 2
                    assert_eq!((1 as $t).wrapping_hyperpow((10 as $t), u8::MAX), (1 as $t)); // 1[255]10 = 1
                    assert_eq!((3 as $t).wrapping_hyperpow((4 as $t), 0), (81 as $t)); // 3[3]4 = 81
                    assert_eq!((3 as $t).wrapping_hyperpow((4 as $t), 1), (81 as $t)); // 3[3]4 = 81
                    assert_eq!((3 as $t).wrapping_hyperpow((2 as $t), 2), (27 as $t)); // 3[4]2 = 27
                    assert_eq!((2 as $t).wrapping_hyperpow((2 as $t), 3), (4 as $t)); // 2[5]2 = 4

                    // checked_hyperpow
                    assert_eq!((2 as $t).checked_hyperpow((2 as $t), 2), Some(4 as $t)); // 2[4]2 = 4
                    assert_eq!((255 as $t).checked_hyperpow((2 as $t), 2), None); // MAX[4]2 = None
                )+
            };
        }

        parameterized_test_unsigned_integer_wrapping_hyperpow!(usize u8 u16 u32 u64 u128);
    }

    #[test]
    fn test_float_hyperpow() {
        macro_rules! parameterized_test_float_hyperpow {
            ($($t:ty)+) => {
                $(
                    // hyperpowi
                    assert_eq!((2.71 as $t).hyperpowi(2, 0), (7.3441 as $t)); // 2.71[3]2 = 7.3441
                    assert_eq!((2.71 as $t).hyperpowi(2, 1), (7.3441 as $t)); // 2.71[3]2 = 7.3441
                    assert_eq!((3.5 as $t).hyperpowi(2, 2), (80.21178022896636 as $t)); // 3.5[4]2 = 80.21178022896636
                    assert_eq!((1.5 as $t).hyperpowi(3, 2), (2.1062033521488797 as $t)); // 1.5[4]3 = 2.1062033521488797

                    // hyperpowf
                    assert_eq!((2.5 as $t).hyperpowf((2.5 as $t), 0), (9.882117688026186 as $t)); // 2.71[3]2.71 = 9.882117688026186
                    assert_eq!((2.5 as $t).hyperpowf((2.5 as $t), 1), (9.882117688026186 as $t)); // 2.71[3]2.71 = 9.882117688026186
                    assert_eq!((2.0 as $t).hyperpowf((4.0 as $t), 2), (65536.0 as $t)); // 2.71[3]2.71 = 9.882117688026186
                    assert_eq!((2.0 as $t).hyperpowf((3.0 as $t), 3), (65536.0 as $t)); // 2.71[3]2.71 = 9.882117688026186
                    assert_eq!((1.1 as $t).hyperpowf((5.0 as $t), 2), (1.111780526534057 as $t)); // 2.71[3]2.71 = 9.882117688026186

                    // hyperexp
                    assert_eq!((1 as $t).hyperexp(0), (2.718281828459045 as $t));
                    assert_eq!((1 as $t).hyperexp(1), (2.718281828459045 as $t));
                    assert_eq!((1 as $t).hyperexp(2), (2.718281828459045 as $t));
                )+
            };
        }

        parameterized_test_float_hyperpow!(f32 f64);
    }

    #[cfg(feature = "num_bigint")]
    #[test]
    fn test_biguint() {
        use num_bigint::ToBigUint;
        assert_eq!(
            14.to_biguint()
                .unwrap()
                .hyperpow(2.to_biguint().unwrap(), 0),
            196_i64.to_biguint().unwrap()
        ); // 14[3]2 = 196
        assert_eq!(
            14.to_biguint()
                .unwrap()
                .hyperpow(2.to_biguint().unwrap(), 1),
            196_i64.to_biguint().unwrap()
        ); // 14[3]2 = 196
        assert_eq!(
            14.to_biguint()
                .unwrap()
                .hyperpow(2.to_biguint().unwrap(), 2),
            11112006825558016_i64.to_biguint().unwrap()
        ); // 14[4]2 = 11112006825558016
        assert_eq!(
            3.to_biguint().unwrap().hyperpow(3.to_biguint().unwrap(), 2),
            7625597484987_i64.to_biguint().unwrap()
        ); // 3[4]3 = 7625597484987
    }

    #[cfg(feature = "num_bigfloat")]
    #[test]
    fn test_bigfloat() {
        use num_bigfloat::BigFloat;
        assert_eq!(
            BigFloat::parse("2.71")
                .unwrap()
                .hyperpow(BigFloat::parse("2.71").unwrap(), 0)
                .to_string(),
            "1.490550787307035306754243074608190674950e+1"
        );
        assert_eq!(
            BigFloat::parse("2.71")
                .unwrap()
                .hyperpow(BigFloat::parse("2.71").unwrap(), 1)
                .to_string(),
            "1.490550787307035306754243074608190674950e+1"
        );
        assert_eq!(
            BigFloat::parse("2.71")
                .unwrap()
                .hyperpow(BigFloat::parse("3").unwrap(), 2)
                .to_string(),
            "2.842020288497806735920109265276338114202e+6"
        );
    }
}
