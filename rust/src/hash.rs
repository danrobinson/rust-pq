//! The SLH-DSA hash functions for SHA2, security category 1 (FIPS 205 §11.2.1).

use crate::address::Adrs;
use crate::params::{M, N};
use crate::sha256::{compress, digest, hmac_sha256, sha256, sha256_from, H0};

/// `PK.seed` together with the SHA-256 state after the first block of every
/// tweakable hash, `PK.seed ‖ toByte(0, 64 − n)`. Computed once per key
/// generation, signature or verification and shared by all hash calls.
#[derive(Clone, Copy)]
pub struct Seed {
    pub pk_seed: [u8; N],
    pub state: [u32; 8],
}

/// The `Seed` of `PK.seed`: one compression of `PK.seed ‖ toByte(0, 48)`.
pub fn seed_ctx(pk_seed: &[u8; N]) -> Seed {
    let mut blk = [0u8; 64];
    blk[0..N].copy_from_slice(pk_seed);
    let state = compress(&H0, &blk, 0);
    Seed { pk_seed: *pk_seed, state }
}

/// The one padded block that follows `PK.seed ‖ toByte(0, 64 − n)` when
/// hashing `ADRSc ‖ m` for a short `m` (at most 33 bytes):
/// `ADRSc ‖ m ‖ 0x80 ‖ 0… ‖ bit length`.
pub fn short_block(adrs: &Adrs, m: &[u8]) -> [u8; 64] {
    let len = m.len();
    let mut blk = [0u8; 64];
    blk[0..22].copy_from_slice(&adrs.compress());
    blk[22..22 + len].copy_from_slice(m);
    blk[22 + len] = 0x80;
    let bits = (86 + len) * 8;
    blk[62] = (bits >> 8) as u8;
    blk[63] = bits as u8;
    blk
}

/// The first `n` bytes of the digest for a final state.
pub fn trunc(st: &[u32; 8]) -> [u8; N] {
    let d = digest(st);
    let mut out = [0u8; N];
    out.copy_from_slice(&d[0..N]);
    out
}

/// `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ m))` for a short
/// `m` (at most 33 bytes): `F` and `PRF` (|m| = n) and `H` (|m| = 2n).
///
/// `ADRSc ‖ m` and the SHA-256 padding fit in a single block after the first,
/// so the block is built on the stack and compressed once from the seed state.
pub fn thash_short(seed: &Seed, adrs: &Adrs, m: &[u8]) -> [u8; N] {
    let blk = short_block(adrs, m);
    let st = compress(&seed.state, &blk, 0);
    trunc(&st)
}

/// `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ m))` for any `m`,
/// continuing from the precomputed state of the first block: `T_l`
/// (|m| = l·n). Short messages may use `thash_short`.
pub fn thash(seed: &Seed, adrs: &Adrs, m: &[u8]) -> [u8; N] {
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(&adrs.compress());
    buf.extend_from_slice(m);
    let d = sha256_from(&seed.state, 64, &buf);
    let mut out = [0u8; N];
    out.copy_from_slice(&d[0..N]);
    out
}

/// `PRF_msg(SK.prf, opt_rand, M) = Trunc_n(HMAC-SHA-256(SK.prf, opt_rand ‖ M))`.
pub fn prf_msg(sk_prf: &[u8; N], opt_rand: &[u8; N], m: &[u8]) -> [u8; N] {
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(opt_rand);
    buf.extend_from_slice(m);
    let d = hmac_sha256(sk_prf, &buf);
    let mut out = [0u8; N];
    out.copy_from_slice(&d[0..N]);
    out
}

/// `SHA-256(R ‖ PK.seed ‖ PK.root ‖ M)`, the inner hash of `H_msg`.
///
/// When `M` has at least `n` bytes, the first block is
/// `R ‖ PK.seed ‖ PK.root ‖ M[0..n]` and the rest of `M` is hashed where it
/// lies, so a long message is never copied.
fn h_msg_inner(r: &[u8; N], pk_seed: &[u8; N], pk_root: &[u8; N], m: &[u8]) -> [u8; 32] {
    if m.len() >= N {
        let mut blk = [0u8; 64];
        blk[0..N].copy_from_slice(r);
        blk[N..2 * N].copy_from_slice(pk_seed);
        blk[2 * N..3 * N].copy_from_slice(pk_root);
        blk[3 * N..4 * N].copy_from_slice(&m[0..N]);
        let st = compress(&H0, &blk, 0);
        sha256_from(&st, 64, &m[N..m.len()])
    } else {
        let mut buf: Vec<u8> = Vec::new();
        buf.extend_from_slice(r);
        buf.extend_from_slice(pk_seed);
        buf.extend_from_slice(pk_root);
        buf.extend_from_slice(m);
        sha256(&buf)
    }
}

/// `H_msg(R, PK.seed, PK.root, M) =
///  MGF1-SHA-256(R ‖ PK.seed ‖ SHA-256(R ‖ PK.seed ‖ PK.root ‖ M), m)`.
///
/// Since m = 30 <= 32, MGF1 is a single SHA-256 call with counter 0.
pub fn h_msg(r: &[u8; N], pk_seed: &[u8; N], pk_root: &[u8; N], m: &[u8]) -> [u8; M] {
    let inner = h_msg_inner(r, pk_seed, pk_root, m);
    let mut seed: Vec<u8> = Vec::new();
    seed.extend_from_slice(r);
    seed.extend_from_slice(pk_seed);
    seed.extend_from_slice(&inner);
    seed.extend_from_slice(&[0u8; 4]);
    let d = sha256(&seed);
    let mut out = [0u8; M];
    out.copy_from_slice(&d[0..M]);
    out
}
