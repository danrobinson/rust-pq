//! The signature type and its encodings.

use crate::ParameterSet;
use ::signature::{Error, SignatureEncoding};
use hybrid_array::typenum::Unsigned;
use hybrid_array::{Array, ArraySize};
use pkcs8::{der::AnyRef, spki::AssociatedAlgorithmIdentifier, AlgorithmIdentifierRef};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

#[cfg(feature = "alloc")]
use pkcs8::{
    der::{self, asn1::BitString},
    spki::SignatureBitStringEncoding,
};

/// A trait specifying the length of a serialized signature for a given parameter set
pub trait SignatureLen {
    /// The length of the signature in bytes
    type SigLen: ArraySize;
}

/// An SLH-DSA signature for a given parameter set.
///
/// This is a large value held inline: `P::SigLen` bytes. Any byte string of
/// the right length is accepted; nothing about it is checked until it is
/// verified.
pub struct Signature<P: ParameterSet> {
    pub(crate) bytes: Array<u8, P::SigLen>,
}

impl<P: ParameterSet> Clone for Signature<P> {
    fn clone(&self) -> Self {
        Signature {
            bytes: self.bytes.clone(),
        }
    }
}

impl<P: ParameterSet> core::fmt::Debug for Signature<P> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Signature")
            .field("bytes", &self.bytes.as_slice())
            .finish()
    }
}

impl<P: ParameterSet> PartialEq for Signature<P> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl<P: ParameterSet> Eq for Signature<P> {}

impl<P: ParameterSet> Signature<P> {
    /// Serialize the signature to a `Vec<u8>` of length `P::SigLen`.
    #[cfg(feature = "alloc")]
    pub fn to_vec(&self) -> Vec<u8> {
        self.bytes.to_vec()
    }

    /// Serialize the signature to a new stack-allocated array
    pub fn to_bytes(&self) -> Array<u8, P::SigLen> {
        self.bytes.clone()
    }
}

impl<P: ParameterSet> TryFrom<&[u8]> for Signature<P> {
    type Error = Error;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        if !P::sig_len_ok(bytes) {
            return Err(Error::new());
        }
        let mut sig = Array::<u8, P::SigLen>::default();
        sig.copy_from_slice(bytes);
        Ok(Signature { bytes: sig })
    }
}

#[cfg(feature = "alloc")]
impl<P: ParameterSet> From<&Signature<P>> for Vec<u8> {
    fn from(sig: &Signature<P>) -> Vec<u8> {
        sig.to_vec()
    }
}

impl<P: ParameterSet> SignatureEncoding for Signature<P> {
    type Repr = Array<u8, P::SigLen>;

    fn encoded_len(&self) -> usize {
        P::SigLen::USIZE
    }
}

#[cfg(feature = "alloc")]
impl<P: ParameterSet> SignatureBitStringEncoding for Signature<P> {
    fn to_bitstring(&self) -> der::Result<BitString> {
        BitString::new(0, self.to_vec())
    }
}

impl<P: ParameterSet> AssociatedAlgorithmIdentifier for Signature<P> {
    type Params = AnyRef<'static>;

    const ALGORITHM_IDENTIFIER: AlgorithmIdentifierRef<'static> = AlgorithmIdentifierRef {
        oid: P::ALGORITHM_OID,
        parameters: None,
    };
}

impl<P: ParameterSet> From<Signature<P>> for Array<u8, P::SigLen> {
    fn from(sig: Signature<P>) -> Array<u8, P::SigLen> {
        sig.bytes
    }
}

impl<P: ParameterSet> From<&Array<u8, P::SigLen>> for Signature<P> {
    fn from(bytes: &Array<u8, P::SigLen>) -> Signature<P> {
        Signature {
            bytes: bytes.clone(),
        }
    }
}
