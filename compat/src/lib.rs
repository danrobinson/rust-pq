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
//! functions (`slh_keygen_internal`, `slh_sign`, `slh_sign_internal`,
//! `slh_verify`, `slh_verify_internal`), called on byte arrays. Everything in
//! this crate is glue around those calls and is **not** covered by the
//! proofs: the key and signature types, drawing randomness, joining a
//! multi-part message into one buffer, and the PKCS#8 / SPKI encodings. The
//! tests compare every entry point with RustCrypto's crate on the same
//! inputs.
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

#![forbid(unsafe_code)]
#![deny(missing_docs)]

pub use signature;

mod params;
mod signature_encoding;
mod signing_key;
mod verifying_key;

pub use params::{ParameterSet, Sha2_128s};
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
