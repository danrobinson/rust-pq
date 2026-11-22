//! The one parameter set, and the calls into the verified crate.

use crate::{SignatureLen, SigningKeyLen, VerifyingKeyLen};
use hybrid_array::sizes::{U32, U64, U7856};
use crate::scrub::scrub_stack;
use alloc::vec::Vec;
use zeroize::Zeroize;

/// The verified functions, on byte slices of the parameter set's lengths.
/// Each one that works with the secret seed overwrites the stack it used
/// before returning (see [`crate::scrub`]).
///
/// Private: a parameter set cannot be defined outside this crate.
pub(crate) trait Core {
    /// Security parameter `n` in bytes.
    const N: usize;

    /// `slh_keygen` on its `3n` random bytes `SK.seed ‖ SK.prf ‖ PK.seed`:
    /// writes `SK` and `PK`.
    fn keygen(seeds: &[u8], sk: &mut [u8], pk: &mut [u8]);
    /// `slh_sign`. `addrnd` absent is the deterministic variant.
    /// `false` if the context is too long.
    fn sign(m: &[u8], ctx: &[u8], sk: &[u8], addrnd: Option<&[u8]>, sig: &mut [u8]) -> bool;
    /// `slh_sign` with every signed value computed twice and compared.
    /// `false` if the context is too long or a recomputation disagreed.
    fn sign_checked(m: &[u8], ctx: &[u8], sk: &[u8], addrnd: Option<&[u8]>, sig: &mut [u8]) -> bool;
    /// `slh_sign_internal` on the message as given.
    fn sign_internal(m: &[u8], sk: &[u8], addrnd: &[u8], sig: &mut [u8]);
    /// `slh_verify_internal` on the message as given.
    fn verify_internal(m: &[u8], sig: &[u8], pk: &[u8]) -> bool;
    /// `slh_verify` with a context string.
    fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8]) -> bool;

    /// Accept `bytes` as a private key: writes it to `sk` and returns `true`
    /// if it has the right length.
    fn sk_from(bytes: &[u8], sk: &mut [u8]) -> bool;
    /// Accept `bytes` as a public key, likewise.
    fn pk_from(bytes: &[u8], pk: &mut [u8]) -> bool;
    /// Whether `bytes` has the length of a signature.
    fn sig_len_ok(bytes: &[u8]) -> bool;
    /// Whether two private keys are equal, looking at every byte.
    fn sk_eq(a: &[u8], b: &[u8]) -> bool;
    /// The public key held in a private key.
    fn pk_of(sk: &[u8], pk: &mut [u8]);
    /// The PKCS#8 DER encoding of a private key, handed to `f`, then wiped.
    fn with_pkcs8<T>(sk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T;
    /// The SubjectPublicKeyInfo DER encoding of a public key, handed to `f`.
    fn with_spki<T>(pk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T;
}

/// A parameter set of FIPS 205. Only [`Sha2_128s`] implements it.
#[allow(private_bounds)] // Intentionally not implementable elsewhere
pub trait ParameterSet: Core + SigningKeyLen + VerifyingKeyLen + SignatureLen {
    /// Human-readable name of the parameter set, as in FIPS 205.
    const NAME: &'static str;

    /// The object identifier of the parameter set.
    const ALGORITHM_OID: pkcs8::ObjectIdentifier;
}

/// SLH-DSA-SHA2-128s.
#[derive(Debug, Clone)]
#[allow(non_camel_case_types)]
pub struct Sha2_128s {
    _private: (),
}

impl SigningKeyLen for Sha2_128s {
    type SkLen = U64;
}

impl VerifyingKeyLen for Sha2_128s {
    type VkLen = U32;
}

impl SignatureLen for Sha2_128s {
    type SigLen = U7856;
}

impl ParameterSet for Sha2_128s {
    const NAME: &'static str = "SLH-DSA-SHA2-128s";
    const ALGORITHM_OID: pkcs8::ObjectIdentifier = const_oid::db::fips205::ID_SLH_DSA_SHA_2_128_S;
}

/// Copy a signature out, if one was made.
fn put(made: Option<Vec<u8>>, sig: &mut [u8]) -> bool {
    match made {
        Some(bytes) => {
            sig.copy_from_slice(&bytes);
            true
        }
        None => false,
    }
}

/// A slice as the fixed-length array the verified functions take. The callers
/// in this crate always pass the right length; a wrong one is a bug here.
fn fixed<const L: usize>(bytes: &[u8]) -> &[u8; L] {
    bytes.try_into().expect("length fixed by the parameter set")
}

impl Core for Sha2_128s {
    const N: usize = slhdsa::params::N;

    fn keygen(seeds: &[u8], sk: &mut [u8], pk: &mut [u8]) {
        let sk: &mut [u8; 64] = sk.try_into().expect("length fixed by the parameter set");
        let pk: &mut [u8; 32] = pk.try_into().expect("length fixed by the parameter set");
        slhdsa::keygen(fixed(seeds), sk, pk);
        scrub_stack();
    }

    fn sign(m: &[u8], ctx: &[u8], sk: &[u8], addrnd: Option<&[u8]>, sig: &mut [u8]) -> bool {
        let made = match addrnd {
            Some(addrnd) => slhdsa::sign(m, ctx, fixed(sk), fixed(addrnd)),
            None => slhdsa::sign_deterministic(m, ctx, fixed(sk)),
        };
        scrub_stack();
        put(made, sig)
    }

    fn sign_checked(m: &[u8], ctx: &[u8], sk: &[u8], addrnd: Option<&[u8]>, sig: &mut [u8]) -> bool {
        let made = match addrnd {
            Some(addrnd) => slhdsa::sign_checked(m, ctx, fixed(sk), fixed(addrnd)),
            None => slhdsa::sign_deterministic_checked(m, ctx, fixed(sk)),
        };
        scrub_stack();
        put(made, sig)
    }

    fn sign_internal(m: &[u8], sk: &[u8], addrnd: &[u8], sig: &mut [u8]) {
        let bytes = slhdsa::slh_sign_internal(m, fixed(sk), fixed(addrnd));
        scrub_stack();
        sig.copy_from_slice(&bytes);
    }

    fn verify_internal(m: &[u8], sig: &[u8], pk: &[u8]) -> bool {
        slhdsa::slh_verify_internal(m, sig, fixed(pk))
    }

    fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8]) -> bool {
        slhdsa::verify(m, sig, ctx, fixed(pk))
    }

    fn sk_from(bytes: &[u8], sk: &mut [u8]) -> bool {
        let mut parsed = slhdsa::encoding::secret_key_from(bytes);
        let ok = match &parsed {
            Some(key) => {
                sk.copy_from_slice(key);
                true
            }
            None => false,
        };
        parsed.zeroize();
        scrub_stack();
        ok
    }

    fn pk_from(bytes: &[u8], pk: &mut [u8]) -> bool {
        match slhdsa::encoding::public_key_from(bytes) {
            Some(key) => {
                pk.copy_from_slice(&key);
                true
            }
            None => false,
        }
    }

    fn sig_len_ok(bytes: &[u8]) -> bool {
        slhdsa::encoding::signature_len_ok(bytes)
    }

    fn sk_eq(a: &[u8], b: &[u8]) -> bool {
        slhdsa::encoding::secret_keys_equal(fixed(a), fixed(b))
    }

    fn pk_of(sk: &[u8], pk: &mut [u8]) {
        pk.copy_from_slice(&slhdsa::public_key(fixed(sk)));
    }

    fn with_pkcs8<T>(sk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T {
        let mut der = [0u8; slhdsa::params::PKCS8_BYTES];
        slhdsa::encoding::pkcs8_encode(fixed(sk), &mut der);
        let out = f(&der);
        der.zeroize();
        out
    }

    fn with_spki<T>(pk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T {
        f(&slhdsa::encoding::spki_encode(fixed(pk)))
    }
}
