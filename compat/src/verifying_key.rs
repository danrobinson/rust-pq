//! The public key type.

use crate::{join, same, ParameterSet, Signature};
use ::signature::{Error, MultipartVerifier, Verifier};
use hybrid_array::{Array, ArraySize};
use alloc::vec::Vec;
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
        same(&self.bytes, &other.bytes)
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
        let m = join(msg);
        P::verify_internal(&m, &signature.bytes, &self.bytes)
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
        let m = join(msg);
        P::verify(&m, &signature.bytes, ctx, &self.bytes)
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
        let mut vk = Array::<u8, P::VkLen>::default();
        if P::pk_from(bytes, &mut vk) {
            Ok(VerifyingKey { bytes: vk })
        } else {
            Err(Error::new())
        }
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
        // The encoding is the verified crate's; the `der` crate only checks
        // that it is well formed and takes ownership of it.
        P::with_spki(&self.bytes, |encoding| Ok(der::Document::try_from(encoding)?))
    }
}

impl<P: ParameterSet> TryFrom<pkcs8::SubjectPublicKeyInfoRef<'_>> for VerifyingKey<P> {
    type Error = spki::Error;

    fn try_from(spki: pkcs8::SubjectPublicKeyInfoRef<'_>) -> spki::Result<Self> {
        // `spki`'s `assert_algorithm_oid`, with the comparison done by the verified crate.
        let oid = spki.algorithm.oid;
        if !same(oid.as_bytes(), P::ALGORITHM_OID.as_bytes()) {
            return Err(spki::Error::OidUnknown { oid });
        }

        Self::try_from(
            spki.subject_public_key
                .as_bytes()
                .ok_or_else(|| der::Tag::BitString.value_error().to_error())?,
        )
        .map_err(|_| spki::Error::KeyMalformed)
    }
}
