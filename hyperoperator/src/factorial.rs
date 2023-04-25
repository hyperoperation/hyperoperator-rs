use crate::pow::PrimitiveUintHyperPow;

/// Trait for primitive (built-in types) Sized that supports
/// several integer sequences are related to the factorials.
pub trait HyperFactorial {
    /// The hyper extension for exponential factorial.
    ///
    /// If `n` = 0 or `n` = 1, the exponential factorial is defined recursively as a<sub>0</sub> = 1, a<sub>b</sub> = b<sup>a<sub>b - 1</sub></sup>.
    ///
    /// For n > 1: the exponential factorial is defined recursively as a<sub>0</sub> = 1, a<sub>n</sub> = b[n + 2]a<sub>b - 1</sub>.
    ///
    /// `n` parameter:
    /// - n = 0 - exponentiation
    /// - n = 1 - exponentiation
    /// - n = 2 - tetration
    /// - n = 3 - pentation
    /// - n = 4 - hexation
    /// - ...
    ///
    /// Example: `3_u64.exponential_factorial(2)` = <sup><sup>1</sup>2</sup>3 = 27
    /// ```
    /// use hyperoperator::factorial::HyperFactorial;
    ///
    /// # fn main() {
    /// let a: u64 = 3;
    /// assert_eq!(a.exponential_factorial(2), 27_u64);
    /// # }
    /// ```
    fn exponential_factorial(self, n: u8) -> Self
    where
        Self: Sized;
    /// The hyper extension for hyper factorial.
    ///
    /// If `n` = 0 or `n` = 1, the hyper factorial is: 1<sup>1</sup> * 2<sup>2</sup> * 3<sup>3</sup> * ... * b<sup>b</sup>.
    ///
    /// For n > 1: the hyper factorial is: 1[n + 2]1 * 2[n + 2]2 * 3[n + 2]3 * ... * b[n + 2]b
    ///
    /// `n` parameter:
    /// - n = 0 - exponentiation
    /// - n = 1 - exponentiation
    /// - n = 2 - tetration
    /// - n = 3 - pentation
    /// - n = 4 - hexation
    /// - ...
    ///
    /// Example: `3_u64.hyper_factorial(2)` = <sup>1</sup>1 * <sup>2</sup>2 * <sup>3</sup>3 = 30502389939948
    /// ```
    /// use hyperoperator::factorial::HyperFactorial;
    ///
    /// # fn main() {
    /// let a: u64 = 3;
    /// assert_eq!(a.hyper_factorial(2), 30502389939948_u64);
    /// # }
    /// ```
    fn hyper_factorial(self, n: u8) -> Self
    where
        Self: Sized;
}

macro_rules! hyperfactorial_unsigned_integer_impl {
    ($TYPE: ty) => {
        impl HyperFactorial for $TYPE {
            fn exponential_factorial(self, n: u8) -> Self {
                let mut result = (1 as $TYPE);
                let mut number = (1 as $TYPE);
                while number <= self {
                    result = number.wrapping_hyperpow(result, n);
                    number += 1;
                }
                return result;
            }

            fn hyper_factorial(self, n: u8) -> Self {
                let mut result = (1 as $TYPE);
                let mut number = (1 as $TYPE);
                while number <= self {
                    result *= number.wrapping_hyperpow(number, n);
                    number += 1;
                }
                return result;
            }
        }
    };
}

hyperfactorial_unsigned_integer_impl!(u8);
hyperfactorial_unsigned_integer_impl!(u16);
hyperfactorial_unsigned_integer_impl!(u32);
hyperfactorial_unsigned_integer_impl!(u64);
hyperfactorial_unsigned_integer_impl!(u128);
hyperfactorial_unsigned_integer_impl!(usize);

#[cfg(feature = "num_bigint")]
use crate::pow::HyperPow;
#[cfg(feature = "num_bigint")]
use num_bigint::BigUint;
#[cfg(feature = "num_bigint")]
use num_traits::One;

#[cfg(feature = "num_bigint")]
impl HyperFactorial for BigUint {
    fn exponential_factorial(self, n: u8) -> Self {
        let mut result: BigUint = One::one();
        let mut number: BigUint = One::one();
        while number <= self {
            result = number.clone().hyperpow(result, n);
            number += 1_u8;
        }
        result
    }

    fn hyper_factorial(self, n: u8) -> Self {
        let mut result: BigUint = One::one();
        let mut number: BigUint = One::one();
        while number <= self {
            result *= number.clone().hyperpow(number.clone(), n);
            number += 1_u8;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsigned_integer_exponential_factorial() {
        macro_rules! parameterized_test_unsigned_integer_exponential_factorial {
            ($($t:ty)+) => {
                $(
                    assert_eq!((2 as $t).exponential_factorial(0), (2 as $t));
                    assert_eq!((3 as $t).exponential_factorial(1), (9 as $t));
                    assert_eq!((0 as $t).exponential_factorial(2), (1 as $t));
                    assert_eq!((1 as $t).exponential_factorial(2), (1 as $t));
                    assert_eq!((2 as $t).exponential_factorial(2), (2 as $t));
                    assert_eq!((3 as $t).exponential_factorial(2), (27 as $t));
                )+
            };
        }

        parameterized_test_unsigned_integer_exponential_factorial!(usize u8 u16 u32 u64 u128);
    }

    #[test]
    fn test_unsigned_integer_hyper_factorial() {
        macro_rules! parameterized_test_unsigned_integer_hyper_factorial {
            ($($t:ty)+) => {
                $(
                    assert_eq!((2 as $t).hyper_factorial(0), (4 as $t));
                    assert_eq!((3 as $t).hyper_factorial(1), (108 as $t));
                    assert_eq!((0 as $t).hyper_factorial(2), (1 as $t));
                    assert_eq!((1 as $t).hyper_factorial(2), (1 as $t));
                    assert_eq!((2 as $t).hyper_factorial(2), (4 as $t));
                )+
            };
        }

        parameterized_test_unsigned_integer_hyper_factorial!(usize u8 u16 u32 u64 u128);
    }

    #[cfg(feature = "num_bigfloat")]
    #[test]
    fn test_biguint_exponential_factorial() {
        use num_bigint::ToBigUint;
        assert_eq!(
            2_i32.to_biguint().unwrap().exponential_factorial(0),
            2_i32.to_biguint().unwrap()
        );
        assert_eq!(
            3_i32.to_biguint().unwrap().exponential_factorial(1),
            9_i32.to_biguint().unwrap()
        );
        assert_eq!(
            0_i32.to_biguint().unwrap().exponential_factorial(2),
            1_i32.to_biguint().unwrap()
        );
        assert_eq!(
            1_i32.to_biguint().unwrap().exponential_factorial(2),
            1_i32.to_biguint().unwrap()
        );
        assert_eq!(
            2_i32.to_biguint().unwrap().exponential_factorial(2),
            2_i32.to_biguint().unwrap()
        );
        assert_eq!(
            3_i32.to_biguint().unwrap().exponential_factorial(2),
            27_i32.to_biguint().unwrap()
        );
    }

    #[cfg(feature = "num_bigfloat")]
    #[test]
    fn test_biguint_hyper_factorial() {
        use num_bigint::ToBigUint;
        assert_eq!(
            2_i32.to_biguint().unwrap().hyper_factorial(0),
            4_i32.to_biguint().unwrap()
        );
        assert_eq!(
            3_i32.to_biguint().unwrap().hyper_factorial(1),
            108_i32.to_biguint().unwrap()
        );
        assert_eq!(
            0_i32.to_biguint().unwrap().hyper_factorial(2),
            1_i32.to_biguint().unwrap()
        );
        assert_eq!(
            1_i32.to_biguint().unwrap().hyper_factorial(2),
            1_i32.to_biguint().unwrap()
        );
        assert_eq!(
            2_i32.to_biguint().unwrap().hyper_factorial(2),
            4_i32.to_biguint().unwrap()
        );
        assert_eq!(
            3_i64.to_biguint().unwrap().hyper_factorial(2),
            30502389939948_i64.to_biguint().unwrap()
        )
    }
}
