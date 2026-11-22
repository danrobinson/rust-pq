//! SLH-DSA-SHA2-128s as specified in FIPS 205.
//!
//! The code is deliberately plain: no `unsafe`, no traits, no iterators, no
//! closures. It is written to be translated to Lean by Aeneas and proven
//! equivalent to a Lean transcription of FIPS 205.
//!
//! # The `hw-sha2` feature
//!
//! Off by default. With it on, SHA-256 runs on the ARMv8 SHA-256 instructions
//! where the CPU has them (AArch64 only so far; elsewhere the feature changes
//! nothing), and the hash chains that make up nearly all of SLH-DSA are
//! computed four at a time. That is one module, [`sha256`]'s `hw`. It is
//! translated and proved like the rest, except for eighteen small functions
//! that wrap the intrinsics: those are trusted, and the proofs take their
//! meaning from a model of the instructions. See that module.
#![cfg_attr(not(feature = "hw-sha2"), forbid(unsafe_code))]
#![cfg_attr(feature = "hw-sha2", deny(unsafe_code))]

pub mod address;
pub mod api;
pub mod fors;
pub mod hash;
pub mod ht;
pub mod params;
pub mod sha256;
pub mod slh;
pub mod util;
pub mod wots;
pub mod xmss;

pub use api::{keygen, public_key, sign, sign_checked, sign_deterministic, sign_deterministic_checked, verify};
pub use slh::{
    slh_keygen_internal, slh_sign, slh_sign_checked, slh_sign_internal, slh_sign_internal_checked, slh_verify,
    slh_verify_internal,
};
