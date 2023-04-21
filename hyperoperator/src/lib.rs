//! `hyperoperator-rs` is a crate that supports different types of hyperoperations
//! (hyper exponention, hyper root (super root) and hyper log (super log)).
//! If you don't know about hyperoperations then see the article: [Hyperoperation](https://en.wikipedia.org/wiki/Hyperoperation).
//!
//! # What can this library do
//! - Computes tetration, pentation, hextation and etc.
//! - Computes super roots and super log (only hyper natural logarithm, other hyper logarithms can only be computed only approximately)
//! - Supports [BigUint](https://docs.rs/num-bigint/latest/num_bigint/) and [BigFloat](https://crates.io/crates/num-bigfloat) types for calculations
//!
//! # Example
//! ## Hyper exponention
//! ```
//! use num_bigfloat::BigFloat;
//! use hyperoperator::pow::HyperPow;
//!
//! # fn main() {
//! let a = BigFloat::parse("2.4").unwrap();
//! let b = BigFloat::parse("2.6").unwrap();
//! // tetration
//! assert_eq!(a.hyperpow(b, 2).to_string(), "1.042500508439915903472643420925599720010e+2");
//! # }
//! ```
//!
//! ## Hyper (super) root
//! ```
//! use num_bigfloat::BigFloat;
//! use hyperoperator::root::HyperRoot;
//!
//! # fn main() {
//! let a = BigFloat::parse("27.0").unwrap();
//! let b = BigFloat::from_f64(std::f64::consts::E);
//! // tetration
//! assert_eq!(a.hypersqrt(2).to_string(), "3.000000000000000000000000000000000000000");
//! assert_eq!(b.hypersqrt(2).to_string(), "1.763222834351896654975492603088735114643");
//! # }
//! ```
//!
//! ## Hyper (super) log
//! ```
//! use num_bigfloat::BigFloat;
//! use hyperoperator::log::HyperLog;
//!
//! # fn main() {
//! let a = BigFloat::parse("1.2").unwrap();
//! // tetration
//! assert_eq!(a.hyperln(2).to_string(), "1.435727851007358140921528061434015461824e-2");
//! # }
//! ```
//!
pub mod log;
pub mod pow;
pub mod root;
