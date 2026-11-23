//! The interface of RustCrypto's [`slh-dsa`] crate for the six SLH-DSA-SHA2
//! parameter sets, backed by the formally verified `slhdsa` crate
//! (`../rust`).
//!
//! Code written against `slh-dsa` 0.2 that uses only the SHA-2 sets
//! ([`Sha2_128s`], [`Sha2_128f`], [`Sha2_192s`], [`Sha2_192f`],
//! [`Sha2_256s`], [`Sha2_256f`]) can switch by changing the dependency:
//!
//! ```toml
//! slh-dsa = { package = "slhdsa-compat", path = "…/formal-sig/compat" }
//! ```
//!
//! ```
//! use slh_dsa::*;
//! use slh_dsa::signature::*;
//!
//! // Generate a signing key from the operating system's random source.
//! let sk = SigningKey::<Sha2_128f>::generate().unwrap();
//! let vk = sk.verifying_key();
//!
//! // Hedged signing, the default of FIPS 205.
//! let sig = sk.try_sign_hedged(b"Hello world", b"").unwrap();
//! assert!(vk.verify(b"Hello world", &sig).is_ok());
//! ```
//!
//! # What is verified and what is not
//!
//! Key generation, signing and verification, and every decision this crate
//! would otherwise make itself, are functions of the verified crate
//! (`slhdsa::api`, `slhdsa::slh`, `slhdsa::encoding` and `slhdsa::adapter`),
//! called on the caller's bytes at each set's parameters: which bytes of a
//! private key are which, the context-string framing and the order of the
//! argument checks, the choice of `PK.seed` as the randomness of a
//! deterministic signature, appending the parts of a multi-part message, the
//! acceptance of key and signature bytes, the comparisons of keys,
//! signatures and algorithm identifiers, and the PKCS#8 / SPKI encodings.
//! What this crate adds is **not** covered by the proofs: the key and
//! signature types and their trait plumbing, drawing randomness from a
//! random source, the loop over the parts of a message, *decoding* PKCS#8 /
//! SPKI (done by the `pkcs8` crate before the key bytes reach the verified
//! parser), and the wiping described below. `README.md` lists it exactly.
//! The tests compare every entry point with RustCrypto's crate on the same
//! inputs, for all six sets.
//!
//! # Secrets are wiped
//!
//! * A [`SigningKey`] keeps its secret in an allocation of its own, wiped
//!   when the key is dropped; moving a key moves a pointer, not the secret.
//! * The verified code keeps everything derived from the secret on the
//!   stack, and this crate overwrites that stack after each key generation
//!   and signature.
//! * `tests/wipe.rs` and `tests/heap.rs` search the stack and every freed
//!   heap block for the seeds and values derived from them, for all six
//!   sets, and find none.
//!
//! This is a best effort, as it is everywhere: registers are not cleared,
//! the compiler may keep copies the source does not show, and what you copy
//! out with `to_bytes` is yours to wipe.
//!
//! # Differences from RustCrypto's crate
//!
//! * Only the six SHA-2 sets exist. The six SHAKE sets (`Shake128s` …) are
//!   missing, and so are upstream's generic types `Sha2L1` and `Sha2L35` of
//!   which its SHA-2 names are aliases.
//! * This crate is `no_std` like upstream, but always needs an allocator.
//! * A [`SigningKey`] is always wiped when dropped (upstream does so only
//!   with its `zeroize` feature), its `Debug` output does not print the
//!   secret, and comparing two signing keys takes time independent of where
//!   they differ.
//! * Multi-part messages are copied into one buffer before signing or
//!   verifying.
//! * Additions, behind the default `getrandom` feature:
//!   [`SigningKey::generate`] and [`SigningKey::try_sign_hedged`].
//!
//! # Credit
//!
//! The public interface, and the PKCS#8 / SPKI glue in particular, follow
//! `slh-dsa` 0.2.0-rc.5 by the RustCrypto developers (copyright 2024 Trail of
//! Bits, Inc.), licensed Apache-2.0 OR MIT. The licence texts are in this
//! crate's directory.
//!
//! [`slh-dsa`]: https://github.com/RustCrypto/signatures/tree/master/slh-dsa

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

extern crate alloc;

use alloc::vec::Vec;

pub use signature;

mod params;
mod scrub;
mod signature_encoding;
mod signing_key;
mod verifying_key;

pub use params::{ParameterSet, Sha2_128f, Sha2_128s, Sha2_192f, Sha2_192s, Sha2_256f, Sha2_256s};
#[doc(hidden)]
pub use scrub::SCRUB_BYTES;
pub use signature_encoding::{Signature, SignatureLen};
pub use signing_key::{SigningKey, SigningKeyLen};
pub use verifying_key::{VerifyingKey, VerifyingKeyLen};

/// The parts of a multi-part message, joined by the verified
/// `slhdsa::adapter::append`. (The loop over `&[&[u8]]` itself cannot be
/// translated: nested borrows.)
fn join(parts: &[&[u8]]) -> Vec<u8> {
    let mut m = Vec::new();
    for part in parts {
        slhdsa::adapter::append(&mut m, part);
    }
    m
}

/// Equality of two public byte strings, by the verified `slhdsa::adapter::bytes_equal`.
fn same(a: &[u8], b: &[u8]) -> bool {
    slhdsa::adapter::bytes_equal(a, b)
}
