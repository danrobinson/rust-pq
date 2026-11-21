//! SLH-DSA-SHA2-128s as specified in FIPS 205.
//!
//! The code is deliberately plain: no `unsafe`, no traits, no iterators, no
//! closures. It is written to be translated to Lean by Aeneas and proven
//! equivalent to a Lean transcription of FIPS 205.
#![forbid(unsafe_code)]

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
