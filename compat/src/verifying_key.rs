//! The public key type.

use crate::{joined, ParameterSet, Signature};
use ::signature::{Error, MultipartVerifier, Verifier};
use hybrid_array::typenum::Unsigned;
use hybrid_array::{Array, ArraySize};
use pkcs8::{der, spki};

#[cfg(feature = "alloc")]
use pkcs8::EncodePublicKey;

/// A trait specifying the length of a serialized verifying key for a given parameter set
pub trait VerifyingKeyLen {
    /// The length of the serialized verifying key in bytes
    type VkLen: ArraySize;
}

/// A `VerifyingKey` is an SLH-DSA public key, allowing
/// verification of signatures created with the corresponding
/// `SigningKey`
pub struct VerifyingKey<P: ParameterSet> {
    /// `PK.seed ‖ PK.root`.
    pub(crate) bytes: Array<u8, P::VkLen>,
}

impl<P: ParameterSet> core::fmt::Debug for VerifyingKey<P> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("VerifyingKey")
            .field("bytes", &self.bytes.as_slice())
            .finish()
    }
}

impl<P: ParameterSet> PartialEq for VerifyingKey<P> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl<P: ParameterSet> Eq for VerifyingKey<P> {}

impl<P: ParameterSet> VerifyingKey<P> {
    #[doc(hidden)]
    /// Verify a raw message (without context).
    /// Implements [slh_verify_internal] as defined in FIPS-205.
    /// Published for KAT validation purposes but not intended for general use.
    pub fn slh_verify_internal(
        &self,
        msg: &[&[u8]],
        signature: &Signature<P>,
    ) -> Result<(), Error> {
        let mut buf = Vec::new();
        let m = joined(msg, &mut buf);
        P::verify_internal(m, &signature.bytes, &self.bytes)
            .then_some(())
            .ok_or(Error::new())
    }

    /// Implements [slh-verify] as defined in FIPS-205, using a context string.
    /// Context strings must be 255 bytes or less.
    /// # Errors
    /// Returns an error if the context is too long or if the signature is invalid
    pub fn try_verify_with_context(
        &self,
        msg: &[u8],
        ctx: &[u8],
        signature: &Signature<P>,
    ) -> Result<(), Error> {
        self.raw_try_verify_with_context(&[msg], ctx, signature)
    }

    fn raw_try_verify_with_context(
        &self,
        msg: &[&[u8]],
        ctx: &[u8],
        signature: &Signature<P>,
    ) -> Result<(), Error> {
        let mut buf = Vec::new();
        let m = joined(msg, &mut buf);
        P::verify(m, &signature.bytes, ctx, &self.bytes)
            .then_some(())
            .ok_or(Error::new())
    }

    /// Serialize the verifying key to a new stack-allocated array
    pub fn to_bytes(&self) -> Array<u8, P::VkLen> {
        self.bytes.clone()
    }

    /// Serialize the verifying key to a new heap-allocated vector
    #[cfg(feature = "alloc")]
    pub fn to_vec(&self) -> Vec<u8> {
        self.bytes.to_vec()
    }
}

impl<P: ParameterSet> Clone for VerifyingKey<P> {
    fn clone(&self) -> Self {
        VerifyingKey {
            bytes: self.bytes.clone(),
        }
    }
}

impl<P: ParameterSet> From<&VerifyingKey<P>> for Array<u8, P::VkLen> {
    fn from(vk: &VerifyingKey<P>) -> Array<u8, P::VkLen> {
        vk.to_bytes()
    }
}

impl<P: ParameterSet> From<Array<u8, P::VkLen>> for VerifyingKey<P> {
    fn from(bytes: Array<u8, P::VkLen>) -> VerifyingKey<P> {
        VerifyingKey { bytes }
    }
}

impl<P: ParameterSet> TryFrom<&[u8]> for VerifyingKey<P> {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if bytes.len() != P::VkLen::USIZE {
            return Err(Error::new());
        }
        let mut vk = Array::<u8, P::VkLen>::default();
        vk.copy_from_slice(bytes);
        Ok(VerifyingKey { bytes: vk })
    }
}

impl<P: ParameterSet> Verifier<Signature<P>> for VerifyingKey<P> {
    fn verify(&self, msg: &[u8], signature: &Signature<P>) -> Result<(), Error> {
        self.multipart_verify(&[msg], signature)
    }
}

impl<P: ParameterSet> MultipartVerifier<Signature<P>> for VerifyingKey<P> {
    fn multipart_verify(&self, msg: &[&[u8]], signature: &Signature<P>) -> Result<(), Error> {
        self.raw_try_verify_with_context(msg, &[], signature)
    }
}

#[cfg(feature = "alloc")]
impl<P: ParameterSet> EncodePublicKey for VerifyingKey<P> {
    fn to_public_key_der(&self) -> pkcs8::spki::Result<der::Document> {
        let algorithm_identifier = pkcs8::AlgorithmIdentifierRef {
            oid: P::ALGORITHM_OID,
            parameters: None,
        };

        let public_key = self.to_bytes();
        let subject_public_key = der::asn1::BitStringRef::new(0, &public_key)?;

        pkcs8::SubjectPublicKeyInfo {
            algorithm: algorithm_identifier,
            subject_public_key,
        }
        .try_into()
    }
}

impl<P: ParameterSet> TryFrom<pkcs8::SubjectPublicKeyInfoRef<'_>> for VerifyingKey<P> {
    type Error = spki::Error;

    fn try_from(spki: pkcs8::SubjectPublicKeyInfoRef<'_>) -> spki::Result<Self> {
        spki.algorithm.assert_algorithm_oid(P::ALGORITHM_OID)?;

        Self::try_from(
            spki.subject_public_key
                .as_bytes()
                .ok_or_else(|| der::Tag::BitString.value_error().to_error())?,
        )
        .map_err(|_| spki::Error::KeyMalformed)
    }
}
