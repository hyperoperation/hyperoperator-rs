use crate::pow::PrimitiveFloatHyperPow;

pub trait HyperLog {
    /// Returns the hyper natural logarithm of the number.
    ///
    /// WARNING: Returns an approximate result
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
    /// use hyperoperator::HyperLog;
    /// use hyperoperator::HyperPow;
    ///
    /// # fn main() {
    /// let a = BigFloat::parse("1.2").unwrap();
    /// assert_eq!(a.hyperln(2).to_string(), "1.435727851007358140921528061434015461824e-2");
    /// # }
    /// ```
    ///
    fn hyperln(self, n: u8) -> Self
    where
        Self: Sized;
    /// Returns the hyper logarithm of the number with respect to an arbitrary base.
    ///
    /// `n` parameter:
    /// n = 0 - exponentiation
    /// n = 1 - exponentiation
    /// n = 2 - tetration
    /// n = 3 - pentation
    /// n = 4 - hexation
    /// ...
    ///
    /// WARNING: Returns an approximate result
    fn hyperlog(self, base: Self, n: u8) -> Self
    where
        Self: Sized;
    /// Returns the base 2 hyper logarithm of the number.
    ///
    /// `n` parameter:
    /// n = 0 - exponentiation
    /// n = 1 - exponentiation
    /// n = 2 - tetration
    /// n = 3 - pentation
    /// n = 4 - hexation
    /// ...
    ///
    /// WARNING: Returns an approximate result
    fn hyperlog2(self, n: u8) -> Self
    where
        Self: Sized;
    /// Returns the base 10 hyper logarithm of the number.
    ///
    /// `n` parameter:
    /// n = 0 - exponentiation
    /// n = 1 - exponentiation
    /// n = 2 - tetration
    /// n = 3 - pentation
    /// n = 4 - hexation
    /// ...
    ///
    /// WARNING: Returns an approximate result
    fn hyperlog10(self, n: u8) -> Self
    where
        Self: Sized;
}

macro_rules! hyperlog_impl {
    ($TYPE: ty) => {
        impl HyperLog for $TYPE {
            fn hyperln(self, n: u8) -> Self {
                if n == 0 || n == 1 {
                    return self.clone().ln();
                }

                let mut z = 1.0;
                for _ in 1..20 {
                    z -= (z.hyperexp(n) - self) / z.hyperexp(n);
                }
                return z;
            }

            fn hyperlog(self, base: $TYPE, n: u8) -> Self {
                if n == 0 || n == 1 {
                    return self.clone().log(base);
                }

                return self.hyperln(n) / base.hyperln(n);
            }

            fn hyperlog2(self, n: u8) -> Self {
                if n == 0 || n == 1 {
                    return self.clone().log2();
                }

                return self.hyperlog(2.0, n);
            }

            fn hyperlog10(self, n: u8) -> Self {
                if n == 0 || n == 1 {
                    return self.clone().log10();
                }

                return self.hyperlog(10.0, n);
            }
        }
    };
}

hyperlog_impl!(f32);
hyperlog_impl!(f64);

#[cfg(feature = "num_bigfloat")]
use crate::pow::HyperPow;
#[cfg(feature = "num_bigfloat")]
use num_bigfloat::BigFloat;
#[cfg(feature = "num_bigfloat")]
use num_bigfloat::{ONE, TWO};

#[cfg(feature = "num_bigfloat")]
impl HyperLog for BigFloat {
    fn hyperln(self, n: u8) -> Self {
        if n == 0 || n == 1 {
            return self.clone().ln();
        }

        let mut z = ONE;
        for _ in 1..10 {
            z -= (BigFloat::from_f64(std::f64::consts::E).hyperpow(z, n) - self)
                / BigFloat::from_f64(std::f64::consts::E).hyperpow(z, n);
        }

        z
    }

    fn hyperlog(self, base: BigFloat, n: u8) -> Self {
        if n == 0 || n == 1 {
            return self.clone().log(&base);
        }

        self.hyperln(n) / base.hyperln(n)
    }

    fn hyperlog2(self, n: u8) -> Self {
        if n == 0 || n == 1 {
            return self.clone().log2();
        }

        self.hyperlog(TWO, n)
    }

    fn hyperlog10(self, n: u8) -> Self {
        if n == 0 || n == 1 {
            return self.clone().log10();
        }

        self.hyperlog(BigFloat::from_u32(10), n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hyperln() {
        macro_rules! parameterized_test_hyperln {
            ($($t:ty)+) => {
                $(
                    assert_eq!((2 as $t).hyperln(0), (0.6931471805599453 as $t));
                    assert_eq!((2 as $t).hyperln(1), (0.6931471805599453 as $t));
                )+
            };
        }

        parameterized_test_hyperln!(f32 f64);
    }

    #[cfg(feature = "num_bigfloat")]
    #[test]
    fn test_bigfloat() {
        // hyperln
        assert_eq!(
            BigFloat::from_f64(2.0).hyperln(0).to_string(),
            "6.931471805599453094172321214581765680755e-1"
        );
        assert_eq!(
            BigFloat::from_f64(2.0).hyperln(1).to_string(),
            "6.931471805599453094172321214581765680755e-1"
        );

        // hyperlog
        assert_eq!(
            BigFloat::from_f64(16.0).hyperlog(TWO, 0).to_string(),
            "4.000000000000000000000000000000000000000"
        );
        assert_eq!(
            BigFloat::from_f64(16.0).hyperlog(TWO, 1).to_string(),
            "4.000000000000000000000000000000000000000"
        );
    }
}
