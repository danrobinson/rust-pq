//! HashSLH-DSA — FIPS 205 Pre-Hash Mode (Algorithms 23 and 25).
//!
//! Implements FIPS 205 §10.2.2 (`hash_slh_sign`) and §10.3.2 (`hash_slh_verify`) for all
//! twelve SHA-2 and SHAKE parameter sets, along with pre-hashed (`*_prehashed`) entry points
//! for callers that stream and hash large messages externally and cached signing variants
//! backed by [`crate::cache::TopTreeCache`].
//!
//! Supported NIST-approved pre-hash functions:
//! - [`PreHash::Sha256`]   — SHA-256 (32-byte digest, OID `2.16.840.1.101.3.4.2.1`)
//! - [`PreHash::Sha512`]   — SHA-512 (64-byte digest, OID `2.16.840.1.101.3.4.2.3`)
//! - [`PreHash::Shake128`] — SHAKE128 with 256-bit / 32-byte digest (OID `2.16.840.1.101.3.4.2.11`)
//! - [`PreHash::Shake256`] — SHAKE256 with 512-bit / 64-byte digest (OID `2.16.840.1.101.3.4.2.12`)
//!
//! Note on FIPS 205 security categories (§10.2.2): NIST recommends SHA-256 or SHAKE128
//! (256-bit) for Category 1 parameter sets (`128s`/`128f`), and SHA-512 or SHAKE256
//! (512-bit) for Category 3 & 5 parameter sets (`192s`/`192f`/`256s`/`256f`). All four
//! pre-hash algorithms are accepted for every parameter set in accordance with Algorithms 23 & 25.

use alloc::vec;
use alloc::vec::Vec;
use crate::cache::{HashFamily, TopTreeCache};
use crate::params::Params;
use crate::util::block;

/// DER-encoded OID for SHA-256 (`2.16.840.1.101.3.4.2.1`).
pub const OID_SHA256: [u8; 11] = [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01];
/// DER-encoded OID for SHA-512 (`2.16.840.1.101.3.4.2.3`).
pub const OID_SHA512: [u8; 11] = [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03];
/// DER-encoded OID for SHAKE128 (`2.16.840.1.101.3.4.2.11`).
pub const OID_SHAKE128: [u8; 11] = [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0b];
/// DER-encoded OID for SHAKE256 (`2.16.840.1.101.3.4.2.12`).
pub const OID_SHAKE256: [u8; 11] = [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0c];

/// Maximum length of the FIPS 205 HashSLH-DSA formatted message `M'`:
/// `1 (domain) + 1 (|ctx|) + 255 (ctx) + 11 (OID) + 64 (max PH(M)) = 332` bytes.
const MAX_MP_LEN: usize = 1 + 1 + 255 + 11 + 64;

/// Approved pre-hash function for HashSLH-DSA (FIPS 205 §10.2.2 / §10.3.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreHash {
    /// SHA-256 (32-byte digest, OID `2.16.840.1.101.3.4.2.1`).
    Sha256,
    /// SHA-512 (64-byte digest, OID `2.16.840.1.101.3.4.2.3`).
    Sha512,
    /// SHAKE128 with 256-bit (32-byte) output (OID `2.16.840.1.101.3.4.2.11`).
    Shake128,
    /// SHAKE256 with 512-bit (64-byte) output (OID `2.16.840.1.101.3.4.2.12`).
    Shake256,
}

impl PreHash {
    /// The 11-byte DER-encoded ASN.1 OBJECT IDENTIFIER for this pre-hash function.
    #[inline]
    pub const fn oid_der(self) -> &'static [u8; 11] {
        match self {
            PreHash::Sha256 => &OID_SHA256,
            PreHash::Sha512 => &OID_SHA512,
            PreHash::Shake128 => &OID_SHAKE128,
            PreHash::Shake256 => &OID_SHAKE256,
        }
    }

    /// Expected byte length of `PH(M)` for this pre-hash function.
    #[inline]
    pub const fn digest_len(self) -> usize {
        match self {
            PreHash::Sha256 | PreHash::Shake128 => 32,
            PreHash::Sha512 | PreHash::Shake256 => 64,
        }
    }

    /// Computes `PH(message)` as a newly allocated `Vec<u8>`.
    pub fn hash(self, message: &[u8]) -> Vec<u8> {
        let (buf, len) = self.hash_stack(message);
        let mut out = vec![0u8; len];
        out.copy_from_slice(&buf[..len]);
        out
    }

    /// Computes `PH(message)` into a fixed 64-byte stack buffer, returning `(buf, len)`.
    fn hash_stack(self, message: &[u8]) -> ([u8; 64], usize) {
        let mut out = [0u8; 64];
        match self {
            PreHash::Sha256 => {
                let d = crate::sha256::sha256(message);
                out[..32].copy_from_slice(&d);
                (out, 32)
            }
            PreHash::Sha512 => {
                let d = crate::sha512::sha512(message);
                out.copy_from_slice(&d);
                (out, 64)
            }
            PreHash::Shake128 => {
                shake128(message, &mut out[..32]);
                (out, 32)
            }
            PreHash::Shake256 => {
                crate::shake256::shake256(message, &mut out[..64]);
                (out, 64)
            }
        }
    }
}

// ============================================================================
// SHAKE128 (FIPS 202 §6.2: rate = 168 bytes / 1344 bits, domain byte = 0x1f)
// ============================================================================

const RATE_SHAKE128: usize = 168;

const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

fn keccak_f1600_portable(state: &mut [u64; 25]) {
    for &rc in &RC {
        let mut parity = [0u64; 5];
        for x in 0..5 {
            parity[x] = state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20];
        }
        let mut d = [0u64; 5];
        for x in 0..5 {
            d[x] = parity[(x + 4) % 5] ^ parity[(x + 1) % 5].rotate_left(1);
        }
        let a = *state;
        let b = [
            (a[0] ^ d[0]).rotate_left(0),
            (a[6] ^ d[1]).rotate_left(44),
            (a[12] ^ d[2]).rotate_left(43),
            (a[18] ^ d[3]).rotate_left(21),
            (a[24] ^ d[4]).rotate_left(14),
            (a[3] ^ d[3]).rotate_left(28),
            (a[9] ^ d[4]).rotate_left(20),
            (a[10] ^ d[0]).rotate_left(3),
            (a[16] ^ d[1]).rotate_left(45),
            (a[22] ^ d[2]).rotate_left(61),
            (a[1] ^ d[1]).rotate_left(1),
            (a[7] ^ d[2]).rotate_left(6),
            (a[13] ^ d[3]).rotate_left(25),
            (a[19] ^ d[4]).rotate_left(8),
            (a[20] ^ d[0]).rotate_left(18),
            (a[4] ^ d[4]).rotate_left(27),
            (a[5] ^ d[0]).rotate_left(36),
            (a[11] ^ d[1]).rotate_left(10),
            (a[17] ^ d[2]).rotate_left(15),
            (a[23] ^ d[3]).rotate_left(56),
            (a[2] ^ d[2]).rotate_left(62),
            (a[8] ^ d[3]).rotate_left(55),
            (a[14] ^ d[4]).rotate_left(39),
            (a[15] ^ d[0]).rotate_left(41),
            (a[21] ^ d[1]).rotate_left(2),
        ];
        for row in (0..25).step_by(5) {
            state[row] = b[row] ^ (!b[row + 1] & b[row + 2]);
            state[row + 1] = b[row + 1] ^ (!b[row + 2] & b[row + 3]);
            state[row + 2] = b[row + 2] ^ (!b[row + 3] & b[row + 4]);
            state[row + 3] = b[row + 3] ^ (!b[row + 4] & b[row]);
            state[row + 4] = b[row + 4] ^ (!b[row] & b[row + 1]);
        }
        state[0] ^= rc;
    }
}

#[inline]
fn keccak_f1600(state: &mut [u64; 25]) {
    #[cfg(all(
        target_arch = "aarch64",
        target_endian = "little",
        target_vendor = "apple"
    ))]
    if crate::shake256::parallel::available() && crate::sha512::hw::arm::available() {
        let mut words = core::array::from_fn(|i| [state[i]; crate::shake256::parallel::WIDTH]);
        crate::shake256::parallel::permute(&mut words);
        for i in 0..25 {
            state[i] = words[i][0];
        }
        return;
    }
    keccak_f1600_portable(state);
}

/// SHAKE128 extendable-output function (FIPS 202 §6.2) with caller-selected output length.
///
/// Rate = 168 bytes (1344 bits), domain separator = `0x1f`.
pub fn shake128(input: &[u8], output: &mut [u8]) {
    let mut lanes = [0u64; 25];
    let mut pos = 0usize;
    let mut i = 0usize;

    // Fast path: absorb full 8-byte words whenever lane-aligned.
    while input.len() - i >= 8 && pos % 8 == 0 {
        let word = u64::from_le_bytes(input[i..i + 8].try_into().unwrap());
        lanes[pos / 8] ^= word;
        pos += 8;
        i += 8;
        if pos == RATE_SHAKE128 {
            keccak_f1600(&mut lanes);
            pos = 0;
        }
    }
    while i < input.len() {
        lanes[pos / 8] ^= (input[i] as u64) << (8 * (pos % 8));
        pos += 1;
        if pos == RATE_SHAKE128 {
            keccak_f1600(&mut lanes);
            pos = 0;
        }
        i += 1;
    }

    // Domain separator (0x1f) and pad10*1 final bit at byte 167 (MSB of lane 20).
    lanes[pos / 8] ^= 0x1fu64 << (8 * (pos % 8));
    lanes[RATE_SHAKE128 / 8 - 1] ^= 1u64 << 63;
    keccak_f1600(&mut lanes);

    // Squeeze arbitrary-length output.
    let mut out_pos = 0usize;
    for byte in output.iter_mut() {
        if out_pos == RATE_SHAKE128 {
            keccak_f1600(&mut lanes);
            out_pos = 0;
        }
        *byte = (lanes[out_pos / 8] >> (8 * (out_pos % 8))) as u8;
        out_pos += 1;
    }
}

// ============================================================================
// FIPS 205 Algorithm 23 / 25 framing: M' = toByte(1, 1) || toByte(|ctx|, 1) || ctx || OID || PH(M)
// ============================================================================

/// Builds the HashSLH-DSA formatted message `M'` on the stack.
/// Returns `None` if `ctx.len() > 255` or `digest.len() != ph.digest_len()`.
#[inline]
fn format_prehash_message(ctx: &[u8], ph: PreHash, digest: &[u8]) -> Option<([u8; MAX_MP_LEN], usize)> {
    if ctx.len() > 255 || digest.len() != ph.digest_len() {
        return None;
    }
    let oid = ph.oid_der();
    let total = 2 + ctx.len() + oid.len() + digest.len();
    let mut mp = [0u8; MAX_MP_LEN];
    mp[0] = 1;
    mp[1] = ctx.len() as u8;
    let mut off = 2;
    mp[off..off + ctx.len()].copy_from_slice(ctx);
    off += ctx.len();
    mp[off..off + oid.len()].copy_from_slice(oid);
    off += oid.len();
    mp[off..off + digest.len()].copy_from_slice(digest);
    Some((mp, total))
}

// ============================================================================
// Generic HashSLH-DSA API (Algorithms 23 & 25)
// ============================================================================

/// Algorithm 23 (`hash_slh_sign`) with an externally computed pre-hash `digest = PH(M)`.
///
/// Returns `None` if `ctx.len() > 255` or `digest.len() != ph.digest_len()`.
#[inline(never)]
pub fn hash_slh_sign_prehashed<const N: usize>(
    family: HashFamily,
    p: &Params,
    digest: &[u8],
    ctx: &[u8],
    ph: PreHash,
    sk: &[u8],
    addrnd: &[u8; N],
) -> Option<Vec<u8>> {
    let (mp, len) = format_prehash_message(ctx, ph, digest)?;
    let sig = match family {
        HashFamily::Sha2 => crate::slh::slh_sign_internal::<N>(p, &mp[..len], sk, addrnd),
        HashFamily::Shake => crate::shake::slh::slh_sign_internal::<N>(p, &mp[..len], sk, addrnd),
    };
    Some(sig)
}

/// Deterministic Algorithm 23 (`hash_slh_sign`) with an externally computed `digest = PH(M)`.
///
/// Returns `None` if `ctx.len() > 255` or `digest.len() != ph.digest_len()`.
pub fn hash_slh_sign_prehashed_deterministic<const N: usize>(
    family: HashFamily,
    p: &Params,
    digest: &[u8],
    ctx: &[u8],
    ph: PreHash,
    sk: &[u8],
) -> Option<Vec<u8>> {
    let pk_seed = block::<N>(sk, 2);
    hash_slh_sign_prehashed::<N>(family, p, digest, ctx, ph, sk, &pk_seed)
}

/// Algorithm 23 (`hash_slh_sign`), hedged: hashes `m` with `ph` and signs the formatted message.
///
/// Returns `None` if `ctx.len() > 255`.
pub fn hash_slh_sign<const N: usize>(
    family: HashFamily,
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    ph: PreHash,
    sk: &[u8],
    addrnd: &[u8; N],
) -> Option<Vec<u8>> {
    if ctx.len() > 255 {
        return None;
    }
    let (digest, dlen) = ph.hash_stack(m);
    hash_slh_sign_prehashed::<N>(family, p, &digest[..dlen], ctx, ph, sk, addrnd)
}

/// Algorithm 23 (`hash_slh_sign`), deterministic variant.
///
/// Returns `None` if `ctx.len() > 255`.
pub fn hash_slh_sign_deterministic<const N: usize>(
    family: HashFamily,
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    ph: PreHash,
    sk: &[u8],
) -> Option<Vec<u8>> {
    if ctx.len() > 255 {
        return None;
    }
    let pk_seed = block::<N>(sk, 2);
    hash_slh_sign::<N>(family, p, m, ctx, ph, sk, &pk_seed)
}

/// Algorithm 25 (`hash_slh_verify`) with an externally computed `digest = PH(M)`.
///
/// Returns `false` if `ctx.len() > 255`, `digest.len() != ph.digest_len()`, or the signature is invalid.
pub fn hash_slh_verify_prehashed<const N: usize>(
    family: HashFamily,
    p: &Params,
    digest: &[u8],
    sig: &[u8],
    ctx: &[u8],
    ph: PreHash,
    pk: &[u8],
) -> bool {
    let Some((mp, len)) = format_prehash_message(ctx, ph, digest) else {
        return false;
    };
    match family {
        HashFamily::Sha2 => crate::slh::slh_verify_internal::<N>(p, &mp[..len], sig, pk),
        HashFamily::Shake => crate::shake::slh::slh_verify_internal::<N>(p, &mp[..len], sig, pk),
    }
}

/// Algorithm 25 (`hash_slh_verify`): hashes `m` with `ph` and verifies `sig`.
///
/// Returns `false` if `ctx.len() > 255` or the signature is invalid.
pub fn hash_slh_verify<const N: usize>(
    family: HashFamily,
    p: &Params,
    m: &[u8],
    sig: &[u8],
    ctx: &[u8],
    ph: PreHash,
    pk: &[u8],
) -> bool {
    if ctx.len() > 255 {
        return false;
    }
    let (digest, dlen) = ph.hash_stack(m);
    hash_slh_verify_prehashed::<N>(family, p, &digest[..dlen], sig, ctx, ph, pk)
}

// ============================================================================
// Cached HashSLH-DSA signing (combining Algorithm 23 + TopTreeCache)
// ============================================================================

/// Algorithm 23 (`hash_slh_sign`) on a pre-computed `digest = PH(M)` using a [`TopTreeCache`].
pub fn hash_slh_sign_prehashed_cached<const N: usize>(
    p: &Params,
    digest: &[u8],
    ctx: &[u8],
    ph: PreHash,
    sk: &[u8],
    addrnd: &[u8; N],
    cache: &TopTreeCache<N>,
) -> Option<Vec<u8>> {
    let (mp, len) = format_prehash_message(ctx, ph, digest)?;
    Some(cache.sign_internal(p, &mp[..len], sk, addrnd))
}

/// Deterministic Algorithm 23 (`hash_slh_sign`) on a pre-computed `digest` using a [`TopTreeCache`].
pub fn hash_slh_sign_prehashed_deterministic_cached<const N: usize>(
    p: &Params,
    digest: &[u8],
    ctx: &[u8],
    ph: PreHash,
    sk: &[u8],
    cache: &TopTreeCache<N>,
) -> Option<Vec<u8>> {
    let pk_seed = block::<N>(sk, 2);
    hash_slh_sign_prehashed_cached::<N>(p, digest, ctx, ph, sk, &pk_seed, cache)
}

/// Algorithm 23 (`hash_slh_sign`), hedged, using a [`TopTreeCache`].
pub fn hash_slh_sign_cached<const N: usize>(
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    ph: PreHash,
    sk: &[u8],
    addrnd: &[u8; N],
    cache: &TopTreeCache<N>,
) -> Option<Vec<u8>> {
    if ctx.len() > 255 {
        return None;
    }
    let (digest, dlen) = ph.hash_stack(m);
    hash_slh_sign_prehashed_cached::<N>(p, &digest[..dlen], ctx, ph, sk, addrnd, cache)
}

/// Algorithm 23 (`hash_slh_sign`), deterministic, using a [`TopTreeCache`].
pub fn hash_slh_sign_deterministic_cached<const N: usize>(
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    ph: PreHash,
    sk: &[u8],
    cache: &TopTreeCache<N>,
) -> Option<Vec<u8>> {
    if ctx.len() > 255 {
        return None;
    }
    let pk_seed = block::<N>(sk, 2);
    hash_slh_sign_cached::<N>(p, m, ctx, ph, sk, &pk_seed, cache)
}

// ============================================================================
// Typed per-parameter-set modules for all 12 FIPS 205 sets
// ============================================================================

macro_rules! prehash_set {
    ($name:ident, $family:expr, $doc:expr) => {
        #[doc = $doc]
        pub mod $name {
            use alloc::vec::Vec;
            use super::PreHash;
            use crate::cache::{HashFamily, TopTreeCache};
            use crate::$name::params::{N, PARAMS, PK_BYTES, SK_BYTES};

            /// Algorithm 23 (`hash_slh_sign`), hedged. `None` if `ctx.len() > 255`.
            pub fn hash_slh_sign(
                m: &[u8],
                ctx: &[u8],
                ph: PreHash,
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
            ) -> Option<Vec<u8>> {
                super::hash_slh_sign::<N>($family, &PARAMS, m, ctx, ph, sk, addrnd)
            }

            /// Algorithm 23 (`hash_slh_sign`), deterministic. `None` if `ctx.len() > 255`.
            pub fn hash_slh_sign_deterministic(
                m: &[u8],
                ctx: &[u8],
                ph: PreHash,
                sk: &[u8; SK_BYTES],
            ) -> Option<Vec<u8>> {
                super::hash_slh_sign_deterministic::<N>($family, &PARAMS, m, ctx, ph, sk)
            }

            /// Algorithm 25 (`hash_slh_verify`).
            pub fn hash_slh_verify(
                m: &[u8],
                sig: &[u8],
                ctx: &[u8],
                ph: PreHash,
                pk: &[u8; PK_BYTES],
            ) -> bool {
                super::hash_slh_verify::<N>($family, &PARAMS, m, sig, ctx, ph, pk)
            }

            /// Algorithm 23 (`hash_slh_sign`) on a caller-supplied pre-hash digest.
            pub fn hash_slh_sign_prehashed(
                digest: &[u8],
                ctx: &[u8],
                ph: PreHash,
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
            ) -> Option<Vec<u8>> {
                super::hash_slh_sign_prehashed::<N>($family, &PARAMS, digest, ctx, ph, sk, addrnd)
            }

            /// Deterministic Algorithm 23 on a caller-supplied pre-hash digest.
            pub fn hash_slh_sign_prehashed_deterministic(
                digest: &[u8],
                ctx: &[u8],
                ph: PreHash,
                sk: &[u8; SK_BYTES],
            ) -> Option<Vec<u8>> {
                super::hash_slh_sign_prehashed_deterministic::<N>(
                    $family, &PARAMS, digest, ctx, ph, sk,
                )
            }

            /// Algorithm 25 (`hash_slh_verify`) on a caller-supplied pre-hash digest.
            pub fn hash_slh_verify_prehashed(
                digest: &[u8],
                sig: &[u8],
                ctx: &[u8],
                ph: PreHash,
                pk: &[u8; PK_BYTES],
            ) -> bool {
                super::hash_slh_verify_prehashed::<N>($family, &PARAMS, digest, sig, ctx, ph, pk)
            }

            /// Cached Algorithm 23 (`hash_slh_sign`), hedged.
            pub fn hash_slh_sign_cached(
                m: &[u8],
                ctx: &[u8],
                ph: PreHash,
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
                cache: &TopTreeCache<N>,
            ) -> Option<Vec<u8>> {
                super::hash_slh_sign_cached::<N>(&PARAMS, m, ctx, ph, sk, addrnd, cache)
            }

            /// Cached Algorithm 23 (`hash_slh_sign`), deterministic.
            pub fn hash_slh_sign_deterministic_cached(
                m: &[u8],
                ctx: &[u8],
                ph: PreHash,
                sk: &[u8; SK_BYTES],
                cache: &TopTreeCache<N>,
            ) -> Option<Vec<u8>> {
                super::hash_slh_sign_deterministic_cached::<N>(&PARAMS, m, ctx, ph, sk, cache)
            }

            /// Cached Algorithm 23 on a caller-supplied pre-hash digest, hedged.
            pub fn hash_slh_sign_prehashed_cached(
                digest: &[u8],
                ctx: &[u8],
                ph: PreHash,
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
                cache: &TopTreeCache<N>,
            ) -> Option<Vec<u8>> {
                super::hash_slh_sign_prehashed_cached::<N>(
                    &PARAMS, digest, ctx, ph, sk, addrnd, cache,
                )
            }

            /// Cached Algorithm 23 on a caller-supplied pre-hash digest, deterministic.
            pub fn hash_slh_sign_prehashed_deterministic_cached(
                digest: &[u8],
                ctx: &[u8],
                ph: PreHash,
                sk: &[u8; SK_BYTES],
                cache: &TopTreeCache<N>,
            ) -> Option<Vec<u8>> {
                super::hash_slh_sign_prehashed_deterministic_cached::<N>(
                    &PARAMS, digest, ctx, ph, sk, cache,
                )
            }
        }
    };
}

prehash_set!(sha2_128s, HashFamily::Sha2, "HashSLH-DSA for SLH-DSA-SHA2-128s.");
prehash_set!(sha2_128f, HashFamily::Sha2, "HashSLH-DSA for SLH-DSA-SHA2-128f.");
prehash_set!(sha2_192s, HashFamily::Sha2, "HashSLH-DSA for SLH-DSA-SHA2-192s.");
prehash_set!(sha2_192f, HashFamily::Sha2, "HashSLH-DSA for SLH-DSA-SHA2-192f.");
prehash_set!(sha2_256s, HashFamily::Sha2, "HashSLH-DSA for SLH-DSA-SHA2-256s.");
prehash_set!(sha2_256f, HashFamily::Sha2, "HashSLH-DSA for SLH-DSA-SHA2-256f.");

prehash_set!(shake_128s, HashFamily::Shake, "HashSLH-DSA for SLH-DSA-SHAKE-128s.");
prehash_set!(shake_128f, HashFamily::Shake, "HashSLH-DSA for SLH-DSA-SHAKE-128f.");
prehash_set!(shake_192s, HashFamily::Shake, "HashSLH-DSA for SLH-DSA-SHAKE-192s.");
prehash_set!(shake_192f, HashFamily::Shake, "HashSLH-DSA for SLH-DSA-SHAKE-192f.");
prehash_set!(shake_256s, HashFamily::Shake, "HashSLH-DSA for SLH-DSA-SHAKE-256s.");
prehash_set!(shake_256f, HashFamily::Shake, "HashSLH-DSA for SLH-DSA-SHAKE-256f.");

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keccak_f1600_matches_portable() {
        let mut a = [0u64; 25];
        for (i, lane) in a.iter_mut().enumerate() {
            *lane = (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0xa5a5_5a5a_f0f0_0f0f;
        }
        let mut b = a;
        keccak_f1600(&mut a);
        keccak_f1600_portable(&mut b);
        assert_eq!(a, b);
    }
}
