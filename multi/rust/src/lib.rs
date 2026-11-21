//! SLH-DSA with SHA-2 as specified in FIPS 205, for all six parameter sets
//! SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}.
//!
//! The code is deliberately plain: no `unsafe`, no traits, no iterators, no
//! closures. It is written to be translated to Lean by Aeneas and proven
//! equivalent to a Lean transcription of FIPS 205.
//!
//! `slh` holds one implementation, generic over a `params::Params` value.
//! The modules `sha2_128s` … `sha2_256f` are that implementation at each
//! parameter set, with fixed-size key types.
#![forbid(unsafe_code)]

pub mod address;
pub mod fors;
pub mod hash;
pub mod ht;
pub mod params;
pub mod sets;
pub mod sha256;
pub mod sha512;
pub mod slh;
pub mod util;
pub mod wots;
pub mod xmss;

pub use sets::{sha2_128f, sha2_128s, sha2_192f, sha2_192s, sha2_256f, sha2_256s};
