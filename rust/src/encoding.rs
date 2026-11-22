//! Byte encodings of keys and signatures: what a caller's bytes are accepted
//! as, and the two ASN.1 wrappers in which keys travel.
//!
//! For SLH-DSA-SHA2-128s both wrappers are a fixed prefix followed by the key
//! bytes (RFC 9909): `OneAsymmetricKey` version 0 with the algorithm
//! identifier `id-slh-dsa-sha2-128s` (2.16.840.1.101.3.4.3.20, no
//! parameters) and the private key as an OCTET STRING; and
//! `SubjectPublicKeyInfo` with the same identifier and the public key as a
//! BIT STRING with no unused bits. The decoders accept exactly what the
//! encoders produce.

use crate::params::{PKCS8_BYTES, PK_BYTES, SIG_BYTES, SK_BYTES, SPKI_BYTES};

/// `SEQUENCE(82) { INTEGER 0, SEQUENCE(11) { OID }, OCTET STRING(64) …`
pub const PKCS8_PREFIX: [u8; 20] = [
    0x30, 0x52, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x14, 0x04,
    0x40,
];

/// `SEQUENCE(48) { SEQUENCE(11) { OID }, BIT STRING(33), 0 unused bits …`
pub const SPKI_PREFIX: [u8; 18] =
    [0x30, 0x30, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x14, 0x03, 0x21, 0x00];

/// A private key from its bytes: any `4n` bytes, and nothing else.
pub fn secret_key_from(bytes: &[u8]) -> Option<[u8; SK_BYTES]> {
    if bytes.len() != SK_BYTES {
        return None;
    }
    let mut sk = [0u8; SK_BYTES];
    sk.copy_from_slice(bytes);
    Some(sk)
}

/// A public key from its bytes: any `2n` bytes, and nothing else.
pub fn public_key_from(bytes: &[u8]) -> Option<[u8; PK_BYTES]> {
    if bytes.len() != PK_BYTES {
        return None;
    }
    let mut pk = [0u8; PK_BYTES];
    pk.copy_from_slice(bytes);
    Some(pk)
}

/// Whether `bytes` has the length of a signature. (Nothing else about a
/// signature can be checked without verifying it.)
pub fn signature_len_ok(bytes: &[u8]) -> bool {
    bytes.len() == SIG_BYTES
}

/// Whether two private keys are equal. Looks at every byte, wherever they
/// differ.
pub fn secret_keys_equal(a: &[u8; SK_BYTES], b: &[u8; SK_BYTES]) -> bool {
    let mut diff: u8 = 0;
    let mut i = 0;
    while i < SK_BYTES {
        diff |= a[i] ^ b[i];
        i += 1;
    }
    diff == 0
}

/// The PKCS#8 (`OneAsymmetricKey`) DER encoding of a private key, written to
/// `out`.
pub fn pkcs8_encode(sk: &[u8; SK_BYTES], out: &mut [u8; PKCS8_BYTES]) {
    out[0..20].copy_from_slice(&PKCS8_PREFIX);
    out[20..PKCS8_BYTES].copy_from_slice(sk);
}

/// The private key in a PKCS#8 DER encoding, written to `sk`. `false`, with
/// `sk` untouched, unless `der` is exactly an encoding [`pkcs8_encode`]
/// produces.
pub fn pkcs8_decode(der: &[u8], sk: &mut [u8; SK_BYTES]) -> bool {
    if der.len() != PKCS8_BYTES {
        return false;
    }
    let mut i = 0;
    while i < 20 {
        if der[i] != PKCS8_PREFIX[i] {
            return false;
        }
        i += 1;
    }
    sk.copy_from_slice(&der[20..PKCS8_BYTES]);
    true
}

/// The `SubjectPublicKeyInfo` DER encoding of a public key.
pub fn spki_encode(pk: &[u8; PK_BYTES]) -> [u8; SPKI_BYTES] {
    let mut out = [0u8; SPKI_BYTES];
    out[0..18].copy_from_slice(&SPKI_PREFIX);
    out[18..SPKI_BYTES].copy_from_slice(pk);
    out
}

/// The public key in a `SubjectPublicKeyInfo` DER encoding, if `der` is
/// exactly an encoding [`spki_encode`] produces.
pub fn spki_decode(der: &[u8]) -> Option<[u8; PK_BYTES]> {
    if der.len() != SPKI_BYTES {
        return None;
    }
    let mut i = 0;
    while i < 18 {
        if der[i] != SPKI_PREFIX[i] {
            return None;
        }
        i += 1;
    }
    let mut pk = [0u8; PK_BYTES];
    pk.copy_from_slice(&der[18..SPKI_BYTES]);
    Some(pk)
}
