//! Byte encodings of keys and signatures: what a caller's bytes are accepted
//! as, and the two ASN.1 wrappers in which keys travel.
//!
//! For every SLH-DSA-SHA2 parameter set both wrappers are a fixed prefix
//! followed by the key bytes (RFC 9909): `OneAsymmetricKey` version 0 with
//! the algorithm identifier of the set (2.16.840.1.101.3.4.3.20–25 for
//! SHA2-128s, 128f, 192s, 192f, 256s, 256f; no parameters) and the private
//! key as an OCTET STRING; and `SubjectPublicKeyInfo` with the same
//! identifier and the public key as a BIT STRING with no unused bits. The
//! prefixes differ from set to set (the identifier's last arc, and the
//! lengths); each set's are in its module (`sha2_128s::encoding`, …), and the
//! functions here take the prefix as an argument. The decoders accept exactly
//! what the encoders produce.

use crate::params::Params;

/// A private key from its bytes: any `4n` bytes (the length of `sk`), and
/// nothing else. `false`, with `sk` untouched, if the length is wrong.
pub fn secret_key_from(bytes: &[u8], sk: &mut [u8]) -> bool {
    if bytes.len() != sk.len() {
        return false;
    }
    sk.copy_from_slice(bytes);
    true
}

/// A public key from its bytes: any `2n` bytes (the length of `pk`), and
/// nothing else.
pub fn public_key_from(bytes: &[u8], pk: &mut [u8]) -> bool {
    if bytes.len() != pk.len() {
        return false;
    }
    pk.copy_from_slice(bytes);
    true
}

/// Whether `bytes` has the length of a signature. (Nothing else about a
/// signature can be checked without verifying it.)
pub fn signature_len_ok(p: &Params, bytes: &[u8]) -> bool {
    bytes.len() == p.sig_bytes()
}

/// Whether two private keys (of the same length) are equal. Looks at every
/// byte, wherever they differ.
pub fn secret_keys_equal(a: &[u8], b: &[u8]) -> bool {
    let mut diff: u8 = 0;
    let mut i = 0;
    while i < a.len() {
        diff |= a[i] ^ b[i];
        i += 1;
    }
    diff == 0
}

/// `prefix ‖ key`, written to `out` (of length `|prefix| + |key|`): the
/// PKCS#8 encoding of a private key, or the `SubjectPublicKeyInfo` encoding
/// of a public key, given the set's prefix.
pub fn der_encode(prefix: &[u8], key: &[u8], out: &mut [u8]) {
    let l = prefix.len();
    out[0..l].copy_from_slice(prefix);
    out[l..l + key.len()].copy_from_slice(key);
}

/// The key in a DER encoding that [`der_encode`] produces with `prefix`,
/// written to `key`. `false`, with `key` untouched, unless `der` is exactly
/// `prefix` followed by `|key|` bytes.
pub fn der_decode(prefix: &[u8], der: &[u8], key: &mut [u8]) -> bool {
    let l = prefix.len();
    if der.len() != l + key.len() {
        return false;
    }
    let mut i = 0;
    while i < l {
        if der[i] != prefix[i] {
            return false;
        }
        i += 1;
    }
    key.copy_from_slice(&der[l..der.len()]);
    true
}
