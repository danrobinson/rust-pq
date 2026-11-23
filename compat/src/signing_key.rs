//! The private key type.

use crate::params::{Core, Buffer};
use crate::{join, same, ParameterSet, Signature, VerifyingKey, VerifyingKeyLen};
use ::signature::{
    rand_core::{CryptoRng, TryCryptoRng},
    Error, KeypairRef, MultipartSigner, RandomizedMultipartSigner, RandomizedSigner, Signer,
};
use hybrid_array::{Array, ArraySize};
use pkcs8::{
    der::AnyRef,
    spki::{AlgorithmIdentifier, AssociatedAlgorithmIdentifier, SignatureAlgorithmIdentifier},
};
use zeroize::{Zeroize, ZeroizeOnDrop};

#[cfg(feature = "alloc")]
use pkcs8::{der, EncodePrivateKey};

use alloc::boxed::Box;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// A trait specifying the length of a serialized signing key for a given parameter set
pub trait SigningKeyLen: VerifyingKeyLen {
    /// The length of the serialized signing key in bytes
    type SkLen: ArraySize;
}

/// A `SigningKey` allows signing messages with a fixed parameter set.
///
/// The secret is overwritten with zeros when the key is dropped. It is kept
/// in its own heap allocation, so moving a `SigningKey` moves a pointer and
/// leaves no copy of the secret behind.
#[allow(private_bounds)]
pub struct SigningKey<P: Core> {
    /// `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`.
    bytes: Box<P::Sk>,
    /// `PK.seed ‖ PK.root` again, as the public key type.
    verifying_key: VerifyingKey<P>,
}

impl<P: ParameterSet> Clone for SigningKey<P> {
    fn clone(&self) -> Self {
        // Copied from one allocation to the other, never through the stack.
        let mut bytes = Box::new(P::Sk::zeroed());
        bytes.as_mut_slice().copy_from_slice(self.bytes.as_slice());
        SigningKey {
            bytes,
            verifying_key: self.verifying_key.clone(),
        }
    }
}

/// Does not print the secret.
impl<P: ParameterSet> core::fmt::Debug for SigningKey<P> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SigningKey")
            .field("verifying_key", &self.verifying_key)
            .finish_non_exhaustive()
    }
}

/// Looks at every byte, wherever the keys differ.
impl<P: ParameterSet> PartialEq for SigningKey<P> {
    fn eq(&self, other: &Self) -> bool {
        slhdsa::encoding::secret_keys_equal(self.bytes.as_slice(), other.bytes.as_slice())
    }
}

impl<P: ParameterSet> Eq for SigningKey<P> {}

impl<P: Core> Drop for SigningKey<P> {
    fn drop(&mut self) {
        self.bytes.as_mut_slice().zeroize();
    }
}

impl<P: ParameterSet> ZeroizeOnDrop for SigningKey<P> {}

#[allow(private_bounds)]
impl<P: Core> SigningKey<P> {
    /// Create a new `SigningKey` from a cryptographic random number generator
    pub fn new<R: CryptoRng + ?Sized>(rng: &mut R) -> Self {
        // Each supported family uses at most 32 bytes per seed. Give the
        // RNG three independent n-byte slices in the order of Algorithm 21.
        let mut sk_seed = [0u8; 32];
        let mut sk_prf = [0u8; 32];
        let mut pk_seed = [0u8; 32];
        let key = Self::key_from_rng_parts(
            rng,
            &mut sk_seed[..P::N],
            &mut sk_prf[..P::N],
            &mut pk_seed[..P::N],
        );
        sk_seed.zeroize();
        sk_prf.zeroize();
        pk_seed.zeroize();
        key
    }

    fn key_from_rng_parts<R: CryptoRng + ?Sized>(
        rng: &mut R, sk_seed: &mut [u8], sk_prf: &mut [u8], pk_seed: &mut [u8],
    ) -> Self {
        rng.fill_bytes(sk_seed);
        rng.fill_bytes(sk_prf);
        rng.fill_bytes(pk_seed);
        Self::slh_keygen_internal(sk_seed, sk_prf, pk_seed)
    }

    /// Draw `SK.seed`, `SK.prf` and `PK.seed`, in that order, and derive the key.
    #[cfg(feature = "getrandom")]
    fn try_new<R: TryCryptoRng + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        let n = P::N;
        let mut seeds = P::Sk::zeroed();
        let drawn = rng
            .try_fill_bytes(&mut seeds.as_mut_slice()[..n])
            .and_then(|()| rng.try_fill_bytes(&mut seeds.as_mut_slice()[n..2 * n]))
            .and_then(|()| rng.try_fill_bytes(&mut seeds.as_mut_slice()[2 * n..3 * n]));
        let key = drawn.map(|()| Self::from_seeds(&seeds.as_slice()[..3 * n]));
        seeds.as_mut_slice().zeroize();
        key
    }

    /// Create a new `SigningKey` from the operating system's random source.
    ///
    /// Not part of RustCrypto's interface.
    /// # Errors
    /// Returns an error if the operating system cannot supply randomness.
    #[cfg(feature = "getrandom")]
    pub fn generate() -> Result<Self, Error> {
        Self::try_new(&mut getrandom::SysRng).map_err(|_| Error::new())
    }

    /// `seeds` is `SK.seed ‖ SK.prf ‖ PK.seed`.
    #[cfg(feature = "getrandom")]
    fn from_seeds(seeds: &[u8]) -> Self {
        // The private key is written straight into its allocation.
        let mut bytes = Box::new(P::Sk::zeroed());
        let mut pk = P::Vk::zeroed();
        P::keygen(seeds, bytes.as_mut_slice(), pk.as_mut_slice());
        SigningKey {
            bytes,
            verifying_key: VerifyingKey { bytes: pk },
        }
    }

    #[doc(hidden)]
    #[must_use]
    /// Construct a new SigningKey from pre-chosen seeds.
    /// Implements [slh_keygen_internal] as defined in FIPS-205.
    /// Published for KAT validation purposes but not intended for general use.
    /// Each seed must be `n` bytes long, panics otherwise.
    pub fn slh_keygen_internal(sk_seed: &[u8], sk_prf: &[u8], pk_seed: &[u8]) -> Self {
        let mut bytes = Box::new(P::Sk::zeroed());
        let mut pk = P::Vk::zeroed();
        P::keygen_seeds(sk_seed, sk_prf, pk_seed, bytes.as_mut_slice(), pk.as_mut_slice());
        SigningKey {
            bytes,
            verifying_key: VerifyingKey { bytes: pk },
        }
    }

    #[doc(hidden)]
    /// Sign a message with a pre-chosen randomizer.
    /// Implements [slh_sign_internal] as defined in FIPS-205.
    /// Published for KAT validation purposes but not intended for general use.
    /// opt_rand must be a P::N length slice, panics otherwise.
    pub fn slh_sign_internal(&self, msg: &[&[u8]], opt_rand: Option<&[u8]>) -> Signature<P> {
        let m = join(msg);
        let mut sig = P::Sig::zeroed();
        P::sign_internal(&m, self.bytes.as_slice(), opt_rand, sig.as_mut_slice());
        Signature { bytes: sig }
    }

    /// Implements [slh-sign] as defined in FIPS-205, using a context string.
    /// Context strings must be 255 bytes or less.
    ///
    /// With `opt_rand` absent the signature is deterministic; with `n` fresh
    /// random bytes it is hedged. `opt_rand` must be `n` bytes long, panics
    /// otherwise.
    /// # Errors
    /// Returns an error if the context string is too long.
    pub fn try_sign_with_context(
        &self,
        msg: &[u8],
        ctx: &[u8],
        opt_rand: Option<&[u8]>,
    ) -> Result<Signature<P>, Error> {
        self.raw_try_sign_with_context(&[msg], ctx, opt_rand)
    }

    /// Hedged signing with a context string: FIPS 205's default `slh_sign`,
    /// with the per-signature randomness drawn from the operating system.
    ///
    /// Not part of RustCrypto's interface.
    /// # Errors
    /// Returns an error if the context string is longer than 255 bytes or the
    /// operating system cannot supply randomness.
    #[cfg(feature = "getrandom")]
    pub fn try_sign_hedged(&self, msg: &[u8], ctx: &[u8]) -> Result<Signature<P>, Error> {
        self.raw_try_sign_with_rng(&mut getrandom::SysRng, &[msg], ctx)
    }

    fn raw_try_sign_with_context(
        &self,
        msg: &[&[u8]],
        ctx: &[u8],
        opt_rand: Option<&[u8]>,
    ) -> Result<Signature<P>, Error> {
        let m = join(msg);
        let mut sig = P::Sig::zeroed();
        if P::sign(&m, ctx, self.bytes.as_slice(), opt_rand, sig.as_mut_slice()) {
            Ok(Signature { bytes: sig })
        } else {
            Err(Error::new())
        }
    }

    fn raw_try_sign_with_rng<R: TryCryptoRng + ?Sized>(
        &self,
        rng: &mut R,
        msg: &[&[u8]],
        ctx: &[u8],
    ) -> Result<Signature<P>, Error> {
        let mut randomizer = [0u8; 32];
        let result = self.sign_with_rng_buffer(rng, msg, ctx, &mut randomizer[..P::N]);
        randomizer.zeroize();
        result
    }

    fn sign_with_rng_buffer<R: TryCryptoRng + ?Sized>(
        &self, rng: &mut R, msg: &[&[u8]], ctx: &[u8], randomizer: &mut [u8],
    ) -> Result<Signature<P>, Error> {
        match rng.try_fill_bytes(randomizer) {
            Ok(()) => self.raw_try_sign_with_context(msg, ctx, Some(randomizer)),
            Err(_) => Err(Error::new()),
        }
    }

}

impl<P: ParameterSet> SigningKey<P> {
    /// Serialize the signing key to a new stack-allocated array
    ///
    /// This clones the underlying fields
    pub fn to_bytes(&self) -> Array<u8, P::SkLen> {
        Array((*self.bytes).clone())
    }

    /// Serialize the signing key to a new heap-allocated vector
    #[cfg(feature = "alloc")]
    pub fn to_vec(&self) -> Vec<u8> {
        self.bytes.as_slice().to_vec()
    }
}

impl<P: Core> TryFrom<&[u8]> for SigningKey<P> {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        let mut sk = Box::new(P::Sk::zeroed());
        let mut pk = P::Vk::zeroed();
        if !P::sk_from(bytes, sk.as_mut_slice(), pk.as_mut_slice()) {
            return Err(Error::new());
        }
        Ok(SigningKey {
            bytes: sk,
            verifying_key: VerifyingKey { bytes: pk },
        })
    }
}

impl<P: Core> Signer<Signature<P>> for SigningKey<P> {
    fn try_sign(&self, msg: &[u8]) -> Result<Signature<P>, Error> {
        self.try_multipart_sign(&[msg])
    }
}

impl<P: Core> MultipartSigner<Signature<P>> for SigningKey<P> {
    fn try_multipart_sign(&self, msg: &[&[u8]]) -> Result<Signature<P>, Error> {
        self.raw_try_sign_with_context(msg, &[], None)
    }
}

impl<P: Core> RandomizedSigner<Signature<P>> for SigningKey<P> {
    fn try_sign_with_rng<R: TryCryptoRng + ?Sized>(
        &self,
        rng: &mut R,
        msg: &[u8],
    ) -> Result<Signature<P>, signature::Error> {
        self.try_multipart_sign_with_rng(rng, &[msg])
    }
}

impl<P: Core> RandomizedMultipartSigner<Signature<P>> for SigningKey<P> {
    fn try_multipart_sign_with_rng<R: TryCryptoRng + ?Sized>(
        &self,
        rng: &mut R,
        msg: &[&[u8]],
    ) -> Result<Signature<P>, Error> {
        self.raw_try_sign_with_rng(rng, msg, &[])
    }
}

impl<P: ParameterSet> AsRef<VerifyingKey<P>> for SigningKey<P> {
    fn as_ref(&self) -> &VerifyingKey<P> {
        &self.verifying_key
    }
}

impl<P: ParameterSet> KeypairRef for SigningKey<P> {
    type VerifyingKey = VerifyingKey<P>;
}

impl<P> TryFrom<pkcs8::PrivateKeyInfoRef<'_>> for SigningKey<P>
where
    P: Core + crate::params::DerAlgorithm,
{
    type Error = pkcs8::Error;

    fn try_from(private_key_info: pkcs8::PrivateKeyInfoRef<'_>) -> pkcs8::Result<Self> {
        // `spki`'s `assert_algorithm_oid`, with the comparison done by the verified crate.
        let oid = private_key_info.algorithm.oid;
        if !same(oid.as_bytes(), P::DER_OID.as_bytes()) {
            return Err(pkcs8::spki::Error::OidUnknown { oid }.into());
        }

        Self::try_from(private_key_info.private_key.as_bytes())
            .map_err(|_| pkcs8::KeyError::Invalid.into())
    }
}

#[cfg(feature = "alloc")]
impl<P> EncodePrivateKey for SigningKey<P>
where
    P: Core,
{
    fn to_pkcs8_der(&self) -> pkcs8::Result<der::SecretDocument> {
        // The encoding is the verified crate's; the `der` crate only checks
        // that it is well formed and takes ownership of it.
        P::with_pkcs8(self.bytes.as_slice(), |encoding| Ok(der::SecretDocument::try_from(encoding)?))
    }
}

impl<P: ParameterSet> SignatureAlgorithmIdentifier for SigningKey<P> {
    type Params = AnyRef<'static>;

    const SIGNATURE_ALGORITHM_IDENTIFIER: AlgorithmIdentifier<Self::Params> =
        Signature::<P>::ALGORITHM_IDENTIFIER;
}
