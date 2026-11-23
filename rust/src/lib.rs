//! SLH-DSA with SHA-2 as specified in FIPS 205, for all six parameter sets
//! SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}.
//!
//! The code is deliberately plain: no `unsafe` (outside the opt-in hardware
//! backend), no traits, no iterators, no closures, and no use of the standard
//! library beyond an allocator (`no_std`). It is written to be translated to
//! Lean by Aeneas and proven equivalent to a Lean transcription of FIPS 205.
//!
//! One implementation serves all six sets. Its functions take the parameter
//! set as a value, `p: &params::Params`, and the hash length `n` also as a
//! const generic `N`, which sizes the arrays that hold hash values; the two
//! must agree. The modules `sha2_128s` … `sha2_256f` are that implementation
//! at each parameter set, with fixed-size key types and the names of the
//! single-set crate: `sha2_128s::api::keygen`, `sha2_128s::slh_sign_internal`,
//! `sha2_128s::encoding::pkcs8_encode`, ….
//!
//! # The `hw-sha2` feature
//!
//! Off by default. With it on, SHA-256 runs on the ARMv8 SHA-256 instructions
//! and the SHA-512 compression function on the ARMv8.2 SHA-512 instructions,
//! each where the CPU has them (tested separately; AArch64 only so far;
//! elsewhere the feature changes nothing), and the hash chains that make up
//! nearly all of SLH-DSA are computed four at a time. That is two modules,
//! [`sha256`]'s `hw` and [`sha512`]'s `hw`, written in the Aeneas subset like
//! the rest except for small functions that wrap the intrinsics. SHA-512 is
//! used by the sets with n = 24 and 32.
#![cfg_attr(not(feature = "hw-sha2"), forbid(unsafe_code))]
#![cfg_attr(feature = "hw-sha2", deny(unsafe_code))]
#![no_std]

extern crate alloc;
// Where the target does not guarantee the SHA-256 or the SHA-512 instructions,
// the feature tests of the `hw-sha2` backends ask the operating system, through `std`.
#[cfg(any(
    test,
    all(
        feature = "hw-sha2",
        target_arch = "aarch64",
        not(target_os = "none"),
        not(all(target_feature = "neon", target_feature = "sha2"))
    ),
    all(
        feature = "hw-sha2",
        target_arch = "aarch64",
        not(target_os = "none"),
        not(all(target_feature = "neon", target_feature = "sha3"))
    )
))]
extern crate std;

pub mod adapter;
pub mod address;
pub mod api;
pub mod encoding;
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
