use crate::pow::PrimitiveFloatHyperPow;

pub trait HyperRoot {
    /// Returns the hyper square root of a number.
    ///
    /// Returns NaN if self is a negative number other than -0.0.
    ///
    ///
    /// `n` parameter:
    /// n = 0 - exponentiation
    /// n = 1 - exponentiation
    /// n = 2 - tetration
    /// n = 3 - pentation
    /// n = 4 - hexation
    /// ...
    ///
    /// ```
    /// use num_bigfloat::BigFloat;
    /// use hyperoperator::HyperRoot;
    ///
    /// # fn main() {
    /// let a = BigFloat::parse("27.0").unwrap();
    /// let b = BigFloat::from_f64(std::f64::consts::E);
    /// assert_eq!(a.hypersqrt(2).to_string(), "3.000000000000000000000000000000000000000");
    /// assert_eq!(b.hypersqrt(2).to_string(), "1.763222834351896654975492603088735114643");
    /// # }
    /// ```
    ///
    fn hypersqrt(self, n: u8) -> Self
    where
        Self: Sized;
    /// Returns the hyper cube root of a number.
    ///
    /// Returns NaN if self is a negative number other than -0.0.
    ///
    ///
    /// `n` parameter:
    /// n = 0 - exponentiation
    /// n = 1 - exponentiation
    /// n = 2 - tetration
    /// n = 3 - pentation
    /// n = 4 - hexation
    /// ...
    ///
    /// ```
    /// use num_bigfloat::BigFloat;
    /// use hyperoperator::HyperRoot;
    ///
    /// # fn main() {
    /// let a = BigFloat::parse("1.7").unwrap();
    /// assert_eq!(a.hypercbrt(2).to_string(), "1.395530473956788148473037800353843913917");
    /// # }
    /// ```
    ///
    fn hypercbrt(self, n: u8) -> Self
    where
        Self: Sized;
    /// Returns the hyper n-th root of a number.
    ///
    /// Returns NaN if self is a negative number other than -0.0.
    ///
    ///
    /// `n` parameter:
    /// n = 0 - exponentiation
    /// n = 1 - exponentiation
    /// n = 2 - tetration
    /// n = 3 - pentation
    /// n = 4 - hexation
    /// ...
    ///
    /// ```
    /// use num_bigfloat::BigFloat;
    /// use hyperoperator::HyperRoot;
    ///
    /// # fn main() {
    /// let a = BigFloat::parse("1.2").unwrap();
    /// assert_eq!(a.hyperroot(4, 2).to_string(), "1.164228234547765442221639202165441776589");
    /// # }    
    /// ```
    ///
    fn hyperroot(self, index: u32, n: u8) -> Self
    where
        Self: Sized;
}

macro_rules! hyperroot_impl {
    ($TYPE: ty) => {
        impl HyperRoot for $TYPE {
            fn hypersqrt(self, n: u8) -> Self {
                if self < 0.0 {
                    return (f32::NAN as $TYPE);
                }

                if n == 0 || n == 1 {
                    return self.sqrt();
                }

                let mut z: $TYPE = 1.0;
                for _ in 0..15 {
                    let a = z.hyperpowi(2, n);
                    z -= (a - self) / (a * (z.ln() + 1.0));
                }

                return z;
            }

            fn hypercbrt(self, n: u8) -> Self {
                if self < 0.0 {
                    return (f32::NAN as $TYPE);
                }

                if n == 0 || n == 1 {
                    return self.cbrt();
                }

                let mut z: $TYPE = 1.0;
                for _ in 0..15 {
                    let a = z.hyperpowi(3, n);
                    z -= (a - self) / (2.0 * z * z.ln() + z);
                }

                return z;
            }

            fn hyperroot(self, index: u32, n: u8) -> Self {
                if self < 0.0 {
                    return (f32::NAN as $TYPE);
                }

                if n == 0 || n == 1 {
                    return self.powf((1.0 / (index as f32)).into());
                }

                let index_i32: i32 = index.try_into().unwrap();
                let mut z: $TYPE = 1.0;
                for _ in 0..15 {
                    let a = z.hyperpowi(index_i32, n);
                    z -= (a - self)
                        / (a * ((index - 1) as $TYPE) * z.powi(index_i32 - 1) * z.ln()
                            + z.powi(index_i32 - 1));
                }

                return z;
            }
        }
    };
}

hyperroot_impl!(f32);
hyperroot_impl!(f64);

#[cfg(feature = "num_bigfloat")]
use crate::pow::HyperPow;
#[cfg(feature = "num_bigfloat")]
use num_bigfloat::BigFloat;
#[cfg(feature = "num_bigfloat")]
use num_bigfloat::{NAN, ONE, TWO, ZERO};
#[cfg(feature = "num_bigfloat")]
use num_traits::Pow;

#[cfg(feature = "num_bigfloat")]
fn hyperpowi(base: BigFloat, exponent: i32, n: u8) -> BigFloat {
    if exponent == 0 {
        return ONE;
    }

    if exponent == 1 {
        return base;
    }

    if n == 0 || n == 1 {
        return base.pow(BigFloat::from_i32(exponent));
    }

    let mut exp = exponent;
    let mut result = ONE;
    while exp > 0 {
        result = base.hyperpow(result, n - 1);
        exp -= 1;
    }
    result
}

#[cfg(feature = "num_bigfloat")]
impl HyperRoot for BigFloat {
    fn hypersqrt(self, n: u8) -> Self {
        if self < ZERO {
            return NAN;
        }

        if n == 0 || n == 1 {
            return self.pow(BigFloat::parse("0.5").unwrap());
        }

        let mut z = ONE;
        for _ in 0..100 {
            let a = hyperpowi(z, 2, n);
            z -= (a - self) / (a * (z.ln() + ONE));
        }

        z
    }

    fn hypercbrt(self, n: u8) -> Self {
        if self < ZERO {
            return ONE;
        }

        if n == 0 || n == 1 {
            return self.pow(ONE / BigFloat::parse("3").unwrap());
        }

        let mut z = ONE;
        for _ in 0..100 {
            let a = hyperpowi(z, 3, n);
            z -= (a - self) / (TWO * z * z.ln() + z);
        }

        z
    }

    fn hyperroot(self, index: u32, n: u8) -> Self {
        if self < ZERO {
            return ONE;
        }

        if n == 0 || n == 1 {
            return self.pow(ONE / BigFloat::from_u32(index));
        }

        let index_i32: i32 = index.try_into().unwrap();
        let mut z = ONE;
        for _ in 0..100 {
            let a = hyperpowi(z, index_i32, n);
            z -= (a - self)
                / (a * (BigFloat::from_i32(index_i32 - 1))
                    * z.pow(BigFloat::from_i32(index_i32 - 1))
                    * z.ln()
                    + z.pow(BigFloat::from_i32(index_i32 - 1)));
        }

        z
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hypersqrt() {
        macro_rules! parameterized_test_hypersqrt {
            ($($t:ty)+) => {
                $(
                    assert_eq!((256 as $t).hypersqrt(0), (16 as $t));
                    assert_eq!((256 as $t).hypersqrt(1), (16 as $t));
                    assert_eq!((4 as $t).hypersqrt(2), (2 as $t));
                    assert_eq!((3.14 as $t).hypersqrt(2), (1.853792432853291 as $t));
                )+
            };
        }

        parameterized_test_hypersqrt!(f32 f64);
    }

    #[test]
    fn test_hypercbrt() {
        macro_rules! parameterized_test_hypercbrt {
            ($($t:ty)+) => {
                $(
                    assert_eq!((27 as $t).hypercbrt(0), (3.0000000000000004 as $t));
                    assert_eq!((27 as $t).hypercbrt(1), (3.0000000000000004 as $t));
                    assert_eq!((1.2 as $t).hypercbrt(2), (1.1648876140388167 as $t));
                )+
            };
        }

        parameterized_test_hypercbrt!(f32 f64);
    }

    #[test]
    fn test_hyperroot() {
        macro_rules! parameterized_test_hyperroot {
            ($($t:ty)+) => {
                $(
                    assert_eq!((4 as $t).hyperroot(2, 0), (2 as $t));
                    assert_eq!((4 as $t).hyperroot(2, 1), (2 as $t));
                    assert_eq!((1.0 as $t).hyperroot(4, 2), (1.0 as $t));
                )+
            };
        }

        parameterized_test_hyperroot!(f32 f64);
    }

    #[cfg(feature = "num_bigfloat")]
    #[test]
    fn test_bigfloat() {
        use num_bigfloat::BigFloat;

        // hyperpowi
        assert_eq!(
            hyperpowi(BigFloat::parse("2").unwrap(), 2, 2).to_string(),
            "4.000000000000000000000000000000000000000"
        );
        assert_eq!(
            hyperpowi(BigFloat::parse("16").unwrap(), 2, 2).to_string(),
            "1.844674407370955161600000000000000000000e+19"
        );

        // hypersqrt
        assert_eq!(
            BigFloat::parse("16").unwrap().hypersqrt(0).to_string(),
            "4.000000000000000000000000000000000000000"
        );
        assert_eq!(
            BigFloat::parse("16").unwrap().hypersqrt(1).to_string(),
            "4.000000000000000000000000000000000000000"
        );
        assert_eq!(
            BigFloat::parse("27").unwrap().hypersqrt(2).to_string(),
            "3.000000000000000000000000000000000000000"
        );

        // hypercbrt
        assert_eq!(
            BigFloat::parse("27").unwrap().hypercbrt(0).to_string(),
            "3.000000000000000000000000000000000000000"
        );
        assert_eq!(
            BigFloat::parse("27").unwrap().hypercbrt(1).to_string(),
            "3.000000000000000000000000000000000000000"
        );
        assert_eq!(
            BigFloat::parse("1.71").unwrap().hypercbrt(2).to_string(),
            "1.398693962422692073795032651294153527897"
        );

        // hyperroot
        assert_eq!(
            BigFloat::parse("16").unwrap().hyperroot(4, 0).to_string(),
            "2.000000000000000000000000000000000000000"
        );
        assert_eq!(
            BigFloat::parse("16").unwrap().hyperroot(4, 1).to_string(),
            "2.000000000000000000000000000000000000000"
        );
        assert_eq!(
            BigFloat::parse("1.71").unwrap().hyperroot(4, 2).to_string(),
            "1.381954692587074632734942629848822221349"
        );
    }
}
