//! The one parameter set, and the calls into the verified crate.

use crate::{SignatureLen, SigningKeyLen, VerifyingKeyLen};
use hybrid_array::sizes::{U32, U64, U7856};
use zeroize::Zeroize;

/// The verified functions, on byte slices of the parameter set's lengths.
///
/// Private: a parameter set cannot be defined outside this crate.
pub(crate) trait Core {
    /// Security parameter `n` in bytes.
    const N: usize;

    /// `slh_keygen_internal`: writes `SK` and `PK`.
    fn keygen(sk_seed: &[u8], sk_prf: &[u8], pk_seed: &[u8], sk: &mut [u8], pk: &mut [u8]);
    /// `slh_sign_internal` on the message as given.
    fn sign_internal(m: &[u8], sk: &[u8], addrnd: &[u8], sig: &mut [u8]);
    /// `slh_sign` with a context string. `false` if the context is too long.
    fn sign(m: &[u8], ctx: &[u8], sk: &[u8], addrnd: &[u8], sig: &mut [u8]) -> bool;
    /// `slh_verify_internal` on the message as given.
    fn verify_internal(m: &[u8], sig: &[u8], pk: &[u8]) -> bool;
    /// `slh_verify` with a context string.
    fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8]) -> bool;
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

/// A slice as the fixed-length array the verified functions take. The callers
/// in this crate always pass the right length; a wrong one is a bug here.
fn fixed<const L: usize>(bytes: &[u8]) -> &[u8; L] {
    bytes.try_into().expect("length fixed by the parameter set")
}

impl Core for Sha2_128s {
    const N: usize = slhdsa::params::N;

    fn keygen(sk_seed: &[u8], sk_prf: &[u8], pk_seed: &[u8], sk: &mut [u8], pk: &mut [u8]) {
        let (mut sk_bytes, pk_bytes) =
            slhdsa::slh_keygen_internal(fixed(sk_seed), fixed(sk_prf), fixed(pk_seed));
        sk.copy_from_slice(&sk_bytes);
        pk.copy_from_slice(&pk_bytes);
        sk_bytes.zeroize();
    }

    fn sign_internal(m: &[u8], sk: &[u8], addrnd: &[u8], sig: &mut [u8]) {
        let bytes = slhdsa::slh_sign_internal(m, fixed(sk), fixed(addrnd));
        sig.copy_from_slice(&bytes);
    }

    fn sign(m: &[u8], ctx: &[u8], sk: &[u8], addrnd: &[u8], sig: &mut [u8]) -> bool {
        match slhdsa::slh_sign(m, ctx, fixed(sk), fixed(addrnd)) {
            Some(bytes) => {
                sig.copy_from_slice(&bytes);
                true
            }
            None => false,
        }
    }

    fn verify_internal(m: &[u8], sig: &[u8], pk: &[u8]) -> bool {
        slhdsa::slh_verify_internal(m, sig, fixed(pk))
    }

    fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8]) -> bool {
        slhdsa::slh_verify(m, sig, ctx, fixed(pk))
    }
}
