//! The private key type.

use crate::{joined, ParameterSet, Signature, VerifyingKey, VerifyingKeyLen};
use ::signature::{
    rand_core::{CryptoRng, TryCryptoRng},
    Error, KeypairRef, MultipartSigner, RandomizedMultipartSigner, RandomizedSigner, Signer,
};
use hybrid_array::typenum::Unsigned;
use hybrid_array::{Array, ArraySize};
use pkcs8::{
    der::AnyRef,
    spki::{AlgorithmIdentifier, AssociatedAlgorithmIdentifier, SignatureAlgorithmIdentifier},
};
use zeroize::{Zeroize, ZeroizeOnDrop};

#[cfg(feature = "alloc")]
use pkcs8::{
    der::{self, asn1::OctetStringRef},
    EncodePrivateKey,
};

/// A trait specifying the length of a serialized signing key for a given parameter set
pub trait SigningKeyLen: VerifyingKeyLen {
    /// The length of the serialized signing key in bytes
    type SkLen: ArraySize;
}

/// A `SigningKey` allows signing messages with a fixed parameter set.
///
/// The secret is overwritten with zeros when the key is dropped.
pub struct SigningKey<P: ParameterSet> {
    /// `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`.
    bytes: Array<u8, P::SkLen>,
    /// `PK.seed ‖ PK.root` again, as the public key type.
    verifying_key: VerifyingKey<P>,
}

impl<P: ParameterSet> Clone for SigningKey<P> {
    fn clone(&self) -> Self {
        SigningKey {
            bytes: self.bytes.clone(),
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
        let mut diff = 0u8;
        for (a, b) in self.bytes.iter().zip(other.bytes.iter()) {
            diff |= a ^ b;
        }
        diff == 0
    }
}

impl<P: ParameterSet> Eq for SigningKey<P> {}

impl<P: ParameterSet> Drop for SigningKey<P> {
    fn drop(&mut self) {
        self.bytes.zeroize();
    }
}

impl<P: ParameterSet> ZeroizeOnDrop for SigningKey<P> {}

impl<P: ParameterSet> SigningKey<P> {
    /// Create a new `SigningKey` from a cryptographic random number generator
    pub fn new<R: CryptoRng + ?Sized>(rng: &mut R) -> Self {
        let Ok(key) = Self::try_new(rng);
        key
    }

    /// Draw `SK.seed`, `SK.prf` and `PK.seed`, in that order, and derive the key.
    fn try_new<R: TryCryptoRng + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        let n = P::N;
        let mut seeds = Array::<u8, P::SkLen>::default();
        let drawn = rng
            .try_fill_bytes(&mut seeds[..n])
            .and_then(|()| rng.try_fill_bytes(&mut seeds[n..2 * n]))
            .and_then(|()| rng.try_fill_bytes(&mut seeds[2 * n..3 * n]));
        let key = drawn.map(|()| Self::from_seeds(&seeds[..n], &seeds[n..2 * n], &seeds[2 * n..3 * n]));
        seeds.zeroize();
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

    fn from_seeds(sk_seed: &[u8], sk_prf: &[u8], pk_seed: &[u8]) -> Self {
        let mut bytes = Array::<u8, P::SkLen>::default();
        let mut pk = Array::<u8, P::VkLen>::default();
        P::keygen(sk_seed, sk_prf, pk_seed, &mut bytes, &mut pk);
        SigningKey {
            bytes,
            verifying_key: VerifyingKey { bytes: pk },
        }
    }

    /// `PK.seed`, the third block of the private key.
    fn pk_seed(&self) -> &[u8] {
        &self.bytes[2 * P::N..3 * P::N]
    }

    #[doc(hidden)]
    #[must_use]
    /// Construct a new SigningKey from pre-chosen seeds.
    /// Implements [slh_keygen_internal] as defined in FIPS-205.
    /// Published for KAT validation purposes but not intended for general use.
    /// Each seed must be `n` bytes long, panics otherwise.
    pub fn slh_keygen_internal(sk_seed: &[u8], sk_prf: &[u8], pk_seed: &[u8]) -> Self {
        assert!(sk_seed.len() == P::N && sk_prf.len() == P::N && pk_seed.len() == P::N);
        Self::from_seeds(sk_seed, sk_prf, pk_seed)
    }

    #[doc(hidden)]
    /// Sign a message with a pre-chosen randomizer.
    /// Implements [slh_sign_internal] as defined in FIPS-205.
    /// Published for KAT validation purposes but not intended for general use.
    /// opt_rand must be a P::N length slice, panics otherwise.
    pub fn slh_sign_internal(&self, msg: &[&[u8]], opt_rand: Option<&[u8]>) -> Signature<P> {
        let rand = opt_rand.unwrap_or(self.pk_seed());
        assert!(rand.len() == P::N);
        let mut buf = Vec::new();
        let m = joined(msg, &mut buf);
        let mut sig = Array::<u8, P::SigLen>::default();
        P::sign_internal(m, &self.bytes, rand, &mut sig);
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
        if ctx.len() > 255 {
            return Err(Error::new());
        }
        let rand = opt_rand.unwrap_or(self.pk_seed());
        assert!(rand.len() == P::N);
        let mut buf = Vec::new();
        let m = joined(msg, &mut buf);
        let mut sig = Array::<u8, P::SigLen>::default();
        if P::sign(m, ctx, &self.bytes, rand, &mut sig) {
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
        let n = P::N;
        let mut randomizer = Array::<u8, P::VkLen>::default();
        let sig = match rng.try_fill_bytes(&mut randomizer[..n]) {
            Ok(()) => self.raw_try_sign_with_context(msg, ctx, Some(&randomizer[..n])),
            Err(_) => Err(Error::new()),
        };
        randomizer.zeroize();
        sig
    }

    /// Serialize the signing key to a new stack-allocated array
    ///
    /// This clones the underlying fields
    pub fn to_bytes(&self) -> Array<u8, P::SkLen> {
        self.bytes.clone()
    }

    /// Serialize the signing key to a new heap-allocated vector
    #[cfg(feature = "alloc")]
    pub fn to_vec(&self) -> Vec<u8> {
        self.bytes.to_vec()
    }
}

impl<P: ParameterSet> TryFrom<&[u8]> for SigningKey<P> {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if bytes.len() != P::SkLen::USIZE {
            return Err(Error::new());
        }
        let verifying_key = VerifyingKey::try_from(&bytes[2 * P::N..])?;
        let mut sk = Array::<u8, P::SkLen>::default();
        sk.copy_from_slice(bytes);
        Ok(SigningKey {
            bytes: sk,
            verifying_key,
        })
    }
}

impl<P: ParameterSet> Signer<Signature<P>> for SigningKey<P> {
    fn try_sign(&self, msg: &[u8]) -> Result<Signature<P>, Error> {
        self.try_multipart_sign(&[msg])
    }
}

impl<P: ParameterSet> MultipartSigner<Signature<P>> for SigningKey<P> {
    fn try_multipart_sign(&self, msg: &[&[u8]]) -> Result<Signature<P>, Error> {
        self.raw_try_sign_with_context(msg, &[], None)
    }
}

impl<P: ParameterSet> RandomizedSigner<Signature<P>> for SigningKey<P> {
    fn try_sign_with_rng<R: TryCryptoRng + ?Sized>(
        &self,
        rng: &mut R,
        msg: &[u8],
    ) -> Result<Signature<P>, signature::Error> {
        self.try_multipart_sign_with_rng(rng, &[msg])
    }
}

impl<P: ParameterSet> RandomizedMultipartSigner<Signature<P>> for SigningKey<P> {
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
    P: ParameterSet,
{
    type Error = pkcs8::Error;

    fn try_from(private_key_info: pkcs8::PrivateKeyInfoRef<'_>) -> pkcs8::Result<Self> {
        private_key_info
            .algorithm
            .assert_algorithm_oid(P::ALGORITHM_OID)?;

        Self::try_from(private_key_info.private_key.as_bytes())
            .map_err(|_| pkcs8::KeyError::Invalid.into())
    }
}

#[cfg(feature = "alloc")]
impl<P> EncodePrivateKey for SigningKey<P>
where
    P: ParameterSet,
{
    fn to_pkcs8_der(&self) -> pkcs8::Result<der::SecretDocument> {
        let algorithm_identifier = pkcs8::AlgorithmIdentifierRef {
            oid: P::ALGORITHM_OID,
            parameters: None,
        };

        let mut private_key = self.to_bytes();
        let document = OctetStringRef::new(&private_key)
            .map_err(pkcs8::Error::from)
            .and_then(|octets| {
                let pkcs8_key = pkcs8::PrivateKeyInfoRef::new(algorithm_identifier, octets);
                Ok(der::SecretDocument::encode_msg(&pkcs8_key)?)
            });
        private_key.zeroize();
        document
    }
}

impl<P: ParameterSet> SignatureAlgorithmIdentifier for SigningKey<P> {
    type Params = AnyRef<'static>;

    const SIGNATURE_ALGORITHM_IDENTIFIER: AlgorithmIdentifier<Self::Params> =
        Signature::<P>::ALGORITHM_IDENTIFIER;
}
