//! SLH-DSA-SHA2-128s as specified in FIPS 205.
//!
//! The code is deliberately plain: no `unsafe`, no traits, no iterators, no
//! closures. It is written to be translated to Lean by Aeneas and proven
//! equivalent to a Lean transcription of FIPS 205.
//!
//! # The `hw-sha2` feature
//!
//! Off by default. With it on, the SHA-256 compression function runs on the
//! ARMv8 SHA-256 instructions where the CPU has them (AArch64 only so far;
//! elsewhere the feature changes nothing). That is one small module of
//! `unsafe` intrinsics, [`sha256`]'s `hw`, which the proofs do not cover:
//! they are about the default build. See that module for the exact statement
//! a build with the feature relies on.
#![cfg_attr(not(feature = "hw-sha2"), forbid(unsafe_code))]
#![cfg_attr(feature = "hw-sha2", deny(unsafe_code))]

pub mod address;
pub mod fors;
pub mod hash;
pub mod ht;
pub mod params;
pub mod sha256;
pub mod slh;
pub mod util;
pub mod wots;
pub mod xmss;

pub use slh::{slh_keygen_internal, slh_sign, slh_sign_internal, slh_verify, slh_verify_internal};
