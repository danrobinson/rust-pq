//! The twelve SLH-DSA parameter sets, and the calls into the verified crate.
//!
//! One macro, [`parameter_set!`], defines each set's type, its lengths, its
//! name and identifier, and its forwarding to the verified crate. Nothing
//! here decides anything: every function below calls one verified function
//! (the generic ones of `slhdsa::api`, `slhdsa::slh`, `slhdsa::encoding` and
//! `slhdsa::adapter`, at the set's `PARAMS` and `N`) on the caller's slices,
//! and the ones that touch the secret then overwrite the stack.

use crate::scrub::scrub_stack;
use crate::{SignatureLen, SigningKeyLen, VerifyingKeyLen};

/// Fixed-size storage used by the scheme. Public serialization uses the
/// RustCrypto array types, while the signing path needs only ordinary arrays.
pub(crate) trait Buffer: Sized {
    fn zeroed() -> Self;
    fn as_slice(&self) -> &[u8];
    fn as_mut_slice(&mut self) -> &mut [u8];
}

impl<const N: usize> Buffer for [u8; N] {
    fn zeroed() -> Self { [0; N] }
    fn as_slice(&self) -> &[u8] { self }
    fn as_mut_slice(&mut self) -> &mut [u8] { self }
}

pub(crate) trait SigningKeyStorage { type Sk: Buffer + Clone; }
pub(crate) trait VerifyingKeyStorage { type Vk: Buffer + Clone; }
pub(crate) trait SignatureStorage { type Sig: Buffer + Clone; }

/// The verified functions, on byte slices of the parameter set's lengths.
/// Each one that works with the secret seed overwrites the stack it used
/// before returning (see [`crate::scrub`]).
///
/// Private: a parameter set cannot be defined outside this crate.
pub(crate) trait Core: SigningKeyStorage + VerifyingKeyStorage + SignatureStorage {
    /// Security parameter `n` in bytes.
    const N: usize;

    /// `slh_keygen` on its `3n` random bytes `SK.seed ‖ SK.prf ‖ PK.seed`:
    /// writes `SK` and `PK`.
    #[cfg_attr(not(feature = "getrandom"), allow(dead_code))]
    fn keygen(seeds: &[u8], sk: &mut [u8], pk: &mut [u8]);
    /// `slh_keygen_internal` on three separate seeds (`slhdsa::adapter::keygen_seeds`).
    fn keygen_seeds(sk_seed: &[u8], sk_prf: &[u8], pk_seed: &[u8], sk: &mut [u8], pk: &mut [u8]);
    /// `slh_sign` on `m` (`slhdsa::adapter::sign_into`).
    fn sign(m: &[u8], ctx: &[u8], sk: &[u8], addrnd: Option<&[u8]>, sig: &mut [u8]) -> bool;
    /// `slh_sign_internal` on `m` (`slhdsa::adapter::sign_internal_into`).
    fn sign_internal(m: &[u8], sk: &[u8], addrnd: Option<&[u8]>, sig: &mut [u8]);
    /// `slh_verify_internal`.
    fn verify_internal(m: &[u8], sig: &[u8], pk: &[u8]) -> bool;
    /// `slh_verify` with a context string.
    fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8]) -> bool;
    /// A private key and its public key from bytes (`slhdsa::adapter::signing_key_from`).
    fn sk_from(bytes: &[u8], sk: &mut [u8], pk: &mut [u8]) -> bool;
    /// A public key from bytes (`slhdsa::encoding::public_key_from`).
    fn pk_from(bytes: &[u8], pk: &mut [u8]) -> bool;
    /// A signature from bytes (`slhdsa::adapter::signature_from`).
    fn sig_from(bytes: &[u8], sig: &mut [u8]) -> bool;
    /// The PKCS#8 DER encoding of a private key, handed to `f`, then wiped.
    /// (Used by the encoders, which need the `alloc` feature.)
    #[cfg_attr(not(feature = "alloc"), allow(dead_code))]
    fn with_pkcs8<T>(sk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T;
    /// The SubjectPublicKeyInfo DER encoding of a public key, handed to `f`.
    #[cfg_attr(not(feature = "alloc"), allow(dead_code))]
    fn with_spki<T>(pk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T;
}

/// Algorithm identity needed to decode a parsed PKCS#8 or SPKI key.
pub(crate) trait DerAlgorithm {
    const DER_OID: pkcs8::ObjectIdentifier;
}

/// A parameter set of FIPS 205. Implemented by the six SHA-2 and six SHAKE sets.
#[allow(private_bounds)] // Intentionally not implementable elsewhere
pub trait ParameterSet:
    DerAlgorithm + Core + Clone + core::fmt::Debug
    + SigningKeyLen<SkLen: hybrid_array::ArraySize<ArrayType<u8> = Self::Sk>>
    + VerifyingKeyLen<VkLen: hybrid_array::ArraySize<ArrayType<u8> = Self::Vk>>
    + SignatureLen<SigLen: hybrid_array::ArraySize<ArrayType<u8> = Self::Sig>>
{
    /// Human-readable name of the parameter set, as in FIPS 205.
    const NAME: &'static str;

    /// The object identifier of the parameter set.
    const ALGORITHM_OID: pkcs8::ObjectIdentifier = Self::DER_OID;
}

/// `Option<&[u8]>` as the verified signers take it: whether there is a
/// randomizer, and its bytes (empty when there is none).
fn split(addrnd: Option<&[u8]>) -> (bool, &[u8]) {
    match addrnd {
        Some(r) => (true, r),
        None => (false, &[]),
    }
}

/// RustCrypto names its hash families by node and digest size in bytes.
macro_rules! hash_family {
    ($family:ident, $doc:literal) => {
        #[doc = $doc]
        #[derive(Clone, Debug)]
        pub struct $family<N, M>(core::marker::PhantomData<(N, M)>);
    };
}

hash_family!(Sha2L1, "SHA-2 family at FIPS 205 security category 1.");
hash_family!(Sha2L35, "SHA-2 family at FIPS 205 security categories 3 and 5.");
hash_family!(Shake, "FIPS 205 SHAKE256 family.");

/// One parameter set: the type, its lengths, name and identifier, and the
/// forwarding to the verified crate at `slhdsa::$m::params`.
macro_rules! parameter_set {
    ($ty:ident = $suite:ident<$n:ident, $digest:ident>, $([$family:ident])? $m:ident, $name:literal, $oid:ident, sk: $sk:ident, vk: $vk:ident, sig: $sig:ident) => {
        #[doc = concat!("SLH-DSA-", $name, ".")]
        #[allow(non_camel_case_types)]
        pub type $ty = $suite<hybrid_array::sizes::$n, hybrid_array::sizes::$digest>;

        impl SigningKeyLen for $ty {
            type SkLen = hybrid_array::sizes::$sk;
        }

        impl VerifyingKeyLen for $ty {
            type VkLen = hybrid_array::sizes::$vk;
        }

        impl SignatureLen for $ty {
            type SigLen = hybrid_array::sizes::$sig;
        }

        // The array lengths of the interface are the verified crate's.
        const _: () = {
            use hybrid_array::typenum::Unsigned;
            assert!(<hybrid_array::sizes::$sk as Unsigned>::USIZE == slhdsa::$m::params::SK_BYTES);
            assert!(<hybrid_array::sizes::$vk as Unsigned>::USIZE == slhdsa::$m::params::PK_BYTES);
            assert!(<hybrid_array::sizes::$sig as Unsigned>::USIZE == slhdsa::$m::params::SIG_BYTES);
        };

        impl ParameterSet for $ty {
            const NAME: &'static str = concat!("SLH-DSA-", $name);
        }

        impl DerAlgorithm for $ty {
            const DER_OID: pkcs8::ObjectIdentifier = const_oid::db::fips205::$oid;
        }

        impl SigningKeyStorage for $ty { type Sk = [u8; slhdsa::$m::params::SK_BYTES]; }
        impl VerifyingKeyStorage for $ty { type Vk = [u8; slhdsa::$m::params::PK_BYTES]; }
        impl SignatureStorage for $ty { type Sig = [u8; slhdsa::$m::params::SIG_BYTES]; }

        impl Core for $ty {
            const N: usize = slhdsa::$m::params::N;

            fn keygen(seeds: &[u8], sk: &mut [u8], pk: &mut [u8]) {
                slhdsa::$($family::)?api::keygen::<{ slhdsa::$m::params::N }>(&slhdsa::$m::params::PARAMS, seeds, sk, pk);
                scrub_stack();
            }

            fn keygen_seeds(sk_seed: &[u8], sk_prf: &[u8], pk_seed: &[u8], sk: &mut [u8], pk: &mut [u8]) {
                slhdsa::$($family::)?adapter::keygen_seeds::<{ slhdsa::$m::params::N }>(
                    &slhdsa::$m::params::PARAMS, sk_seed, sk_prf, pk_seed, sk, pk,
                );
                scrub_stack();
            }

            fn sign(m: &[u8], ctx: &[u8], sk: &[u8], addrnd: Option<&[u8]>, sig: &mut [u8]) -> bool {
                let (has, r) = split(addrnd);
                let ok = slhdsa::$($family::)?adapter::sign_into::<{ slhdsa::$m::params::N }>(
                    &slhdsa::$m::params::PARAMS, m, ctx, sk, has, r, sig,
                );
                scrub_stack();
                ok
            }

            fn sign_internal(m: &[u8], sk: &[u8], addrnd: Option<&[u8]>, sig: &mut [u8]) {
                let (has, r) = split(addrnd);
                slhdsa::$($family::)?adapter::sign_internal_into::<{ slhdsa::$m::params::N }>(
                    &slhdsa::$m::params::PARAMS, m, sk, has, r, sig,
                );
                scrub_stack();
            }

            fn verify_internal(m: &[u8], sig: &[u8], pk: &[u8]) -> bool {
                slhdsa::$($family::)?slh::slh_verify_internal::<{ slhdsa::$m::params::N }>(&slhdsa::$m::params::PARAMS, m, sig, pk)
            }

            fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8]) -> bool {
                slhdsa::$($family::)?api::verify::<{ slhdsa::$m::params::N }>(&slhdsa::$m::params::PARAMS, m, sig, ctx, pk)
            }

            fn sk_from(bytes: &[u8], sk: &mut [u8], pk: &mut [u8]) -> bool {
                let ok = slhdsa::adapter::signing_key_from::<{ slhdsa::$m::params::N }>(bytes, sk, pk);
                scrub_stack();
                ok
            }

            fn pk_from(bytes: &[u8], pk: &mut [u8]) -> bool {
                slhdsa::encoding::public_key_from(bytes, pk)
            }

            fn sig_from(bytes: &[u8], sig: &mut [u8]) -> bool {
                slhdsa::adapter::signature_from(&slhdsa::$m::params::PARAMS, bytes, sig)
            }

            fn with_pkcs8<T>(sk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T {
                let mut der = [0u8; slhdsa::$m::params::PKCS8_BYTES];
                slhdsa::encoding::der_encode(&slhdsa::$m::PKCS8_PREFIX, sk, &mut der);
                let out = f(&der);
                zeroize::Zeroize::zeroize(&mut der);
                out
            }

            fn with_spki<T>(pk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T {
                let mut der = [0u8; slhdsa::$m::params::SPKI_BYTES];
                slhdsa::encoding::der_encode(&slhdsa::$m::SPKI_PREFIX, pk, &mut der);
                f(&der)
            }
        }
    };
}

parameter_set!(Sha2_128s = Sha2L1<U16, U30>, sha2_128s, "SHA2-128s", ID_SLH_DSA_SHA_2_128_S, sk: U64, vk: U32, sig: U7856);
parameter_set!(Sha2_128f = Sha2L1<U16, U34>, sha2_128f, "SHA2-128f", ID_SLH_DSA_SHA_2_128_F, sk: U64, vk: U32, sig: U17088);
parameter_set!(Sha2_192s = Sha2L35<U24, U39>, sha2_192s, "SHA2-192s", ID_SLH_DSA_SHA_2_192_S, sk: U96, vk: U48, sig: U16224);
parameter_set!(Sha2_192f = Sha2L35<U24, U42>, sha2_192f, "SHA2-192f", ID_SLH_DSA_SHA_2_192_F, sk: U96, vk: U48, sig: U35664);
parameter_set!(Sha2_256s = Sha2L35<U32, U47>, sha2_256s, "SHA2-256s", ID_SLH_DSA_SHA_2_256_S, sk: U128, vk: U64, sig: U29792);
parameter_set!(Sha2_256f = Sha2L35<U32, U49>, sha2_256f, "SHA2-256f", ID_SLH_DSA_SHA_2_256_F, sk: U128, vk: U64, sig: U49856);

parameter_set!(Shake128s = Shake<U16, U30>, [shake] shake_128s, "SHAKE-128s", ID_SLH_DSA_SHAKE_128_S, sk: U64, vk: U32, sig: U7856);
parameter_set!(Shake128f = Shake<U16, U34>, [shake] shake_128f, "SHAKE-128f", ID_SLH_DSA_SHAKE_128_F, sk: U64, vk: U32, sig: U17088);
parameter_set!(Shake192s = Shake<U24, U39>, [shake] shake_192s, "SHAKE-192s", ID_SLH_DSA_SHAKE_192_S, sk: U96, vk: U48, sig: U16224);
parameter_set!(Shake192f = Shake<U24, U42>, [shake] shake_192f, "SHAKE-192f", ID_SLH_DSA_SHAKE_192_F, sk: U96, vk: U48, sig: U35664);
parameter_set!(Shake256s = Shake<U32, U47>, [shake] shake_256s, "SHAKE-256s", ID_SLH_DSA_SHAKE_256_S, sk: U128, vk: U64, sig: U29792);
parameter_set!(Shake256f = Shake<U32, U49>, [shake] shake_256f, "SHAKE-256f", ID_SLH_DSA_SHAKE_256_F, sk: U128, vk: U64, sig: U49856);
