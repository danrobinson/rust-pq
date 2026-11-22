//! The six SHA-2 parameter sets, and the calls into the verified crate.
//!
//! One macro, [`parameter_set!`], defines each set's type, its lengths, its
//! name and identifier, and its forwarding to the module of the verified
//! crate for that set (`slhdsa::sha2_128s`, …). Nothing here decides
//! anything: every function below converts slices to the verified crate's
//! fixed-size array types, calls one verified function, copies the result
//! out, and (for the ones that touch the secret) overwrites the stack.

use crate::scrub::scrub_stack;
use crate::{SignatureLen, SigningKeyLen, VerifyingKeyLen};
use alloc::vec::Vec;

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
    /// (Used by the encoders, which need the `alloc` feature.)
    #[cfg_attr(not(feature = "alloc"), allow(dead_code))]
    fn with_pkcs8<T>(sk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T;
    /// The SubjectPublicKeyInfo DER encoding of a public key, handed to `f`.
    #[cfg_attr(not(feature = "alloc"), allow(dead_code))]
    fn with_spki<T>(pk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T;
}

/// A parameter set of FIPS 205. Implemented by the six SHA-2 sets.
#[allow(private_bounds)] // Intentionally not implementable elsewhere
pub trait ParameterSet: Core + SigningKeyLen + VerifyingKeyLen + SignatureLen {
    /// Human-readable name of the parameter set, as in FIPS 205.
    const NAME: &'static str;

    /// The object identifier of the parameter set.
    const ALGORITHM_OID: pkcs8::ObjectIdentifier;
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

/// The mutable counterpart of [`fixed`].
fn fixed_mut<const L: usize>(bytes: &mut [u8]) -> &mut [u8; L] {
    bytes.try_into().expect("length fixed by the parameter set")
}

/// One parameter set: the type, its lengths, name and identifier, and the
/// forwarding to `slhdsa::$m`.
macro_rules! parameter_set {
    ($ty:ident, $m:ident, $name:literal, $oid:ident, sk: $sk:ident, vk: $vk:ident, sig: $sig:ident) => {
        #[doc = concat!("SLH-DSA-", $name, ".")]
        #[derive(Debug, Clone)]
        #[allow(non_camel_case_types)]
        pub struct $ty {
            _private: (),
        }

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
            const ALGORITHM_OID: pkcs8::ObjectIdentifier = const_oid::db::fips205::$oid;
        }

        impl Core for $ty {
            const N: usize = slhdsa::$m::params::N;

            fn keygen(seeds: &[u8], sk: &mut [u8], pk: &mut [u8]) {
                slhdsa::$m::keygen(fixed(seeds), fixed_mut(sk), fixed_mut(pk));
                scrub_stack();
            }

            fn sign(m: &[u8], ctx: &[u8], sk: &[u8], addrnd: Option<&[u8]>, sig: &mut [u8]) -> bool {
                let made = match addrnd {
                    Some(addrnd) => slhdsa::$m::sign(m, ctx, fixed(sk), fixed(addrnd)),
                    None => slhdsa::$m::sign_deterministic(m, ctx, fixed(sk)),
                };
                scrub_stack();
                put(made, sig)
            }

            fn sign_checked(m: &[u8], ctx: &[u8], sk: &[u8], addrnd: Option<&[u8]>, sig: &mut [u8]) -> bool {
                let made = match addrnd {
                    Some(addrnd) => slhdsa::$m::sign_checked(m, ctx, fixed(sk), fixed(addrnd)),
                    None => slhdsa::$m::sign_deterministic_checked(m, ctx, fixed(sk)),
                };
                scrub_stack();
                put(made, sig)
            }

            fn sign_internal(m: &[u8], sk: &[u8], addrnd: &[u8], sig: &mut [u8]) {
                let bytes = slhdsa::$m::slh_sign_internal(m, fixed(sk), fixed(addrnd));
                scrub_stack();
                sig.copy_from_slice(&bytes);
            }

            fn verify_internal(m: &[u8], sig: &[u8], pk: &[u8]) -> bool {
                slhdsa::$m::slh_verify_internal(m, sig, fixed(pk))
            }

            fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8]) -> bool {
                slhdsa::$m::verify(m, sig, ctx, fixed(pk))
            }

            fn sk_from(bytes: &[u8], sk: &mut [u8]) -> bool {
                let mut parsed = slhdsa::$m::encoding::secret_key_from(bytes);
                let ok = match &parsed {
                    Some(key) => {
                        sk.copy_from_slice(key);
                        true
                    }
                    None => false,
                };
                zeroize::Zeroize::zeroize(&mut parsed);
                scrub_stack();
                ok
            }

            fn pk_from(bytes: &[u8], pk: &mut [u8]) -> bool {
                match slhdsa::$m::encoding::public_key_from(bytes) {
                    Some(key) => {
                        pk.copy_from_slice(&key);
                        true
                    }
                    None => false,
                }
            }

            fn sig_len_ok(bytes: &[u8]) -> bool {
                slhdsa::$m::encoding::signature_len_ok(bytes)
            }

            fn sk_eq(a: &[u8], b: &[u8]) -> bool {
                slhdsa::$m::encoding::secret_keys_equal(fixed(a), fixed(b))
            }

            fn pk_of(sk: &[u8], pk: &mut [u8]) {
                pk.copy_from_slice(&slhdsa::$m::public_key(fixed(sk)));
            }

            fn with_pkcs8<T>(sk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T {
                let mut der = [0u8; slhdsa::$m::params::PKCS8_BYTES];
                slhdsa::$m::encoding::pkcs8_encode(fixed(sk), &mut der);
                let out = f(&der);
                zeroize::Zeroize::zeroize(&mut der);
                out
            }

            fn with_spki<T>(pk: &[u8], f: impl FnOnce(&[u8]) -> T) -> T {
                f(&slhdsa::$m::encoding::spki_encode(fixed(pk)))
            }
        }
    };
}

parameter_set!(Sha2_128s, sha2_128s, "SHA2-128s", ID_SLH_DSA_SHA_2_128_S, sk: U64, vk: U32, sig: U7856);
parameter_set!(Sha2_128f, sha2_128f, "SHA2-128f", ID_SLH_DSA_SHA_2_128_F, sk: U64, vk: U32, sig: U17088);
parameter_set!(Sha2_192s, sha2_192s, "SHA2-192s", ID_SLH_DSA_SHA_2_192_S, sk: U96, vk: U48, sig: U16224);
parameter_set!(Sha2_192f, sha2_192f, "SHA2-192f", ID_SLH_DSA_SHA_2_192_F, sk: U96, vk: U48, sig: U35664);
parameter_set!(Sha2_256s, sha2_256s, "SHA2-256s", ID_SLH_DSA_SHA_2_256_S, sk: U128, vk: U64, sig: U29792);
parameter_set!(Sha2_256f, sha2_256f, "SHA2-256f", ID_SLH_DSA_SHA_2_256_F, sk: U128, vk: U64, sig: U49856);
