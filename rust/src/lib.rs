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
//! where the CPU has them (AArch64 only so far; elsewhere the feature changes
//! nothing), and the hash chains that make up nearly all of SLH-DSA are
//! computed four at a time. That is one module, [`sha256`]'s `hw`. It is
//! written in the Aeneas subset like the rest, except for small functions
//! that wrap the intrinsics. SHA-512 is portable in this build.
//!
//! # The `hw-sha512` feature (experimental, unverified)
//!
//! Off by default and independent of `hw-sha2`. With it on, the SHA-512
//! compression function runs on the ARMv8.2 SHA-512 instructions where the
//! CPU has them. It exists to measure what hardware SHA-512 buys the sets
//! with n = 24 and 32; nothing about it is proved, and no Lean model of its
//! instructions exists. See [`sha512`]'s `hw`.
#![cfg_attr(not(any(feature = "hw-sha2", feature = "hw-sha512")), forbid(unsafe_code))]
#![cfg_attr(any(feature = "hw-sha2", feature = "hw-sha512"), deny(unsafe_code))]
#![no_std]

extern crate alloc;
// Where the target does not guarantee the SHA-256 instructions, the feature
// test of the `hw-sha2` backend asks the operating system, through `std`.
#[cfg(any(
    test,
    all(
        feature = "hw-sha2",
        target_arch = "aarch64",
        not(target_os = "none"),
        not(all(target_feature = "neon", target_feature = "sha2"))
    ),
    all(
        feature = "hw-sha512",
        target_arch = "aarch64",
        not(target_os = "none"),
        not(all(target_feature = "neon", target_feature = "sha3"))
    )
))]
extern crate std;

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
