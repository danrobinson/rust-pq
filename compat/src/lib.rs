//! The interface of RustCrypto's [`slh-dsa`] crate for SLH-DSA-SHA2-128s,
//! backed by the formally verified `slhdsa` crate.
//!
//! Code written against `slh-dsa` 0.2 that only uses [`Sha2_128s`] can switch
//! by changing the dependency:
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
//! let sk = SigningKey::<Sha2_128s>::generate().unwrap();
//! let vk = sk.verifying_key();
//!
//! // Hedged signing, the default of FIPS 205.
//! let sig = sk.try_sign_hedged(b"Hello world", b"").unwrap();
//! assert!(vk.verify(b"Hello world", &sig).is_ok());
//! ```
//!
//! # What is verified and what is not
//!
//! Key generation, signing and verification are the verified crate's
//! interface functions (`slhdsa::keygen`, `sign`, `sign_deterministic`,
//! `verify`), called on byte arrays: which bytes of a private key are which,
//! the context-string framing, and the choice of `PK.seed` as the randomness
//! of a deterministic signature are all decided there. What this crate adds
//! is **not** covered by the proofs: the key and signature types and their
//! trait plumbing, drawing randomness from a random source, joining a
//! multi-part message into one buffer, the PKCS#8 / SPKI encodings (done by
//! the `pkcs8` crate), and the wiping described below. The tests compare
//! every entry point with RustCrypto's crate on the same inputs.
//!
//! # Optional guard against faults
//!
//! The signing methods do the work of the standard and no more, as
//! RustCrypto's do. [`SigningKey::try_sign_checked`] adds a guard: each
//! value that a one-time key signs is computed twice, by routes that share
//! no work, and compared before the signature is released. A fault during
//! signing that would otherwise produce a signature a forger can exploit is
//! reported as an error instead. The signature is the same; signing takes a
//! little under twice as long.
//!
//! # Secrets are wiped
//!
//! * A [`SigningKey`] keeps its secret in an allocation of its own, wiped
//!   when the key is dropped; moving a key moves a pointer, not the secret.
//! * The verified code keeps everything derived from the secret on the
//!   stack, and this crate overwrites that stack after each key generation
//!   and signature.
//! * `tests/wipe.rs` and `tests/heap.rs` search the stack and every freed
//!   heap block for the seeds and values derived from them, and find none.
//!
//! This is a best effort, as it is everywhere: registers are not cleared,
//! the compiler may keep copies the source does not show, and what you copy
//! out with `to_bytes` is yours to wipe.
//!
//! # Differences from RustCrypto's crate
//!
//! * Only [`Sha2_128s`] exists. The other eleven parameter sets are missing.
//! * This crate needs the standard library; upstream is `no_std`.
//! * A [`SigningKey`] is always wiped when dropped (upstream does so only
//!   with its `zeroize` feature), its `Debug` output does not print the
//!   secret, and comparing two signing keys takes time independent of where
//!   they differ.
//! * Multi-part messages are copied into one buffer before signing or
//!   verifying.
//! * Additions: [`SigningKey::try_sign_checked`], and, behind the default
//!   `getrandom` feature, [`SigningKey::generate`] and
//!   [`SigningKey::try_sign_hedged`].
//!
//! # Credit
//!
//! The public interface, and the PKCS#8 / SPKI glue in particular, follow
//! `slh-dsa` 0.2.0-rc.5 by the RustCrypto developers (copyright 2024 Trail of
//! Bits, Inc.), licensed Apache-2.0 OR MIT. The licence texts are in this
//! crate's directory.
//!
//! [`slh-dsa`]: https://github.com/RustCrypto/signatures/tree/master/slh-dsa

#![forbid(unsafe_code)]
#![deny(missing_docs)]

pub use signature;

mod params;
mod scrub;
mod signature_encoding;
mod signing_key;
mod verifying_key;

pub use params::{ParameterSet, Sha2_128s};
#[doc(hidden)]
pub use scrub::SCRUB_BYTES;
pub use signature_encoding::{Signature, SignatureLen};
pub use signing_key::{SigningKey, SigningKeyLen};
pub use verifying_key::{VerifyingKey, VerifyingKeyLen};

/// Join the parts of a multi-part message. One part is used as it is.
fn joined<'a>(parts: &'a [&'a [u8]], buf: &'a mut Vec<u8>) -> &'a [u8] {
    if parts.len() == 1 {
        return parts[0];
    }
    for part in parts {
        buf.extend_from_slice(part);
    }
    buf
}
