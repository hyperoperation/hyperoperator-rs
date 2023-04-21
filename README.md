# Hyperoperator

hyperoperator-rs is the library for representing tetration, pentation, hexation and etc.

# What are hyperoperations?

See the article from wikipedia: https://en.wikipedia.org/wiki/Hyperoperation

# How to use library

You can use primitive Rust types for hyperoperations:

```
use hyperoperator::PrimitiveUintHyperPow;

fn main() {
    let a: u64 = 3;
    let b: u64 = 3;
    assert_eq!(a.wrapping_hyperpow(b, 2), 7625597484987_u64); // 3[4]3 = 7625597484987
}
```

But, I recommend to use BigUint (https://docs.rs/num-bigint/latest/num_bigint/) and BigFloat (https://crates.io/crates/num-bigfloat).

BigUint:

```
use num_bigint::ToBigUint;
use hyperoperator::HyperPow;
use num_bigint::BigUint;
use std::str::FromStr;

fn main() {
let a = 5_i32.to_biguint().unwrap();
let b = 2_i32.to_biguint().unwrap();
assert_eq!(a.hyperpow(b, 2), BigUint::from_str("3125").unwrap());
}
```

BigFloat:

```
use num_bigfloat::BigFloat;
use hyperoperator::HyperPow;

fn main() {
let a = BigFloat::parse("2.4").unwrap();
let b = BigFloat::parse("2.6").unwrap();
assert_eq!(a.hyperpow(b, 2).to_string(), "1.042500508439915903472643420925599720010e+2");
}
```

# Constants

There are some constants, that can be computed by the library:

<sup>&#960;</sup>e = 728034511260117696327592154758044404454e+22

```
use num_bigfloat::BigFloat;
use hyperoperator::HyperPow;

fn main() {
    let a = BigFloat::from_f64(std::f64::consts::E);
    let b = BigFloat::from_f64(std::f64::consts::PI);
    let result = a.hyperpow(b, 2);
    println!("{}", result);
}
```

<sup>e</sup>&#960; = 3.868086910401845854593013135317223752003e+7

```
use num_bigfloat::BigFloat;
use hyperoperator::HyperPow;

fn main() {
    let a = BigFloat::from_f64(std::f64::consts::PI);
    let b = BigFloat::from_f64(std::f64::consts::E);
    let result = a.hyperpow(b, 2);
    println!("{}", result);
}
```

<sup>e</sup>e = 6.932832796031805568798087525696897618254e+3

```
use num_bigfloat::BigFloat;
use hyperoperator::HyperPow;

fn main() {
    let a = BigFloat::from_f64(std::f64::consts::E);
    let b = BigFloat::from_f64(std::f64::consts::E);
    let result = a.hyperpow(b, 2);
    println!("{}", result);
}
```

# Feedback

Email: izveigor@gmail.com
