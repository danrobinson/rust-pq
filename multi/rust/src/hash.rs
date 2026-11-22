//! The SLH-DSA hash functions for SHA2 (FIPS 205 §11.2.1 and §11.2.2).
//!
//! `n = 16` (security category 1) uses SHA-256 throughout. `n = 24, 32`
//! (categories 3 and 5) use SHA-512 for `H`, `T_l`, `H_msg` and `PRF_msg`,
//! and SHA-256 for `F` and `PRF`. Every function here is generic in the hash
//! length `N` and branches on it only: `N` is a parameter, never a secret.

use alloc::vec::Vec;
use crate::address::Adrs;
use crate::params::Params;
use crate::sha256::{compress, digest, sha256, sha256_from, H0};
use crate::sha512;

/// `PK.seed` together with the hash states after the first block of every
/// tweakable hash: the SHA-256 state after `PK.seed ‖ toByte(0, 64 − n)`
/// (for `F` and `PRF`, and for every hash when `n = 16`), and for `n > 16`
/// the SHA-512 state after `PK.seed ‖ toByte(0, 128 − n)` (for `H` and
/// `T_l`). Computed once per key generation, signature or verification and
/// shared by all hash calls. For `n = 16` `state512` is unused and zero.
#[derive(Clone, Copy)]
pub struct Seed<const N: usize> {
    pub pk_seed: [u8; N],
    pub state: [u32; 8],
    pub state512: [u64; 8],
}

/// The `Seed` of `PK.seed`: one compression of `PK.seed ‖ toByte(0, 64 − n)`,
/// and for `n > 16` one SHA-512 compression of `PK.seed ‖ toByte(0, 128 − n)`.
pub fn seed_ctx<const N: usize>(pk_seed: &[u8; N]) -> Seed<N> {
    let mut blk = [0u8; 64];
    blk[0..N].copy_from_slice(pk_seed);
    let state = compress(&H0, &blk, 0);
    let mut state512 = [0u64; 8];
    if N != 16 {
        let mut blk512 = [0u8; 128];
        blk512[0..N].copy_from_slice(pk_seed);
        state512 = sha512::compress(&sha512::H0, &blk512, 0);
    }
    Seed { pk_seed: *pk_seed, state, state512 }
}

/// The one padded block that follows `PK.seed ‖ toByte(0, 64 − n)` when
/// hashing `ADRSc ‖ m` with SHA-256 for a short `m` (at most 33 bytes):
/// `ADRSc ‖ m ‖ 0x80 ‖ 0… ‖ bit length`.
#[inline(always)]
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

/// The first `n` bytes of the SHA-256 digest for a final state (`n <= 32`).
#[inline(always)]
pub fn trunc<const N: usize>(st: &[u32; 8]) -> [u8; N] {
    let d = digest(st);
    let mut out = [0u8; N];
    out.copy_from_slice(&d[0..N]);
    out
}

/// The first `n` bytes of the SHA-512 digest for a final state.
#[inline(always)]
pub fn trunc512<const N: usize>(st: &[u64; 8]) -> [u8; N] {
    let d = sha512::digest(st);
    let mut out = [0u8; N];
    out.copy_from_slice(&d[0..N]);
    out
}

/// Iterated single-block hashing in place, on several independent blocks.
///
/// Each `blocks[i]` is a `short_block` of an address and an `n`-byte value.
/// Block `i` takes steps `start[i]`, …, `end[i] − 1`: a step writes its
/// number into the last address word (bytes 18..22) and then replaces the
/// value (bytes 22..22 + n) by `Trunc_n` of the SHA-256 compression of the
/// block from `state`. With the seed state that is `F` (or `PRF`) at that
/// address, so a run of steps is Algorithm 5, `chain`. For `n = 16` it is
/// also `H` on a [`pair_block`].
///
/// The blocks do not depend on each other, which is what the opt-in
/// `hw-sha2` backend uses: it works on four of them at once.
pub fn chain_blocks<const N: usize>(state: &[u32; 8], blocks: &mut [[u8; 64]], start: &[u32], end: &[u32]) {
    #[cfg(all(feature = "hw-sha2", target_arch = "aarch64", target_endian = "little"))]
    {
        if crate::sha256::hw::chain_blocks::<N>(state, blocks, start, end) {
            return;
        }
    }
    chain_blocks_portable::<N>(state, blocks, start, end)
}

/// [`chain_blocks`] in portable code: one block after another, one step
/// after another.
pub fn chain_blocks_portable<const N: usize>(state: &[u32; 8], blocks: &mut [[u8; 64]], start: &[u32], end: &[u32]) {
    let mut i = 0;
    while i < blocks.len() {
        let mut t = start[i];
        while t < end[i] {
            blocks[i][18] = (t >> 24) as u8;
            blocks[i][19] = (t >> 16) as u8;
            blocks[i][20] = (t >> 8) as u8;
            blocks[i][21] = t as u8;
            let st = compress(state, &blocks[i], 0);
            let d = trunc::<N>(&st);
            blocks[i][22..22 + N].copy_from_slice(&d);
            t += 1;
        }
        i += 1;
    }
}

/// The `short_block` of `adrs` and `left ‖ right`: the single block of `H`
/// for `n = 16`. (Only called with `N = 16`.)
#[inline(always)]
pub fn pair_block<const N: usize>(adrs: &Adrs, left: &[u8; N], right: &[u8; N]) -> [u8; 64] {
    let mut blk = [0u8; 64];
    blk[0..22].copy_from_slice(&adrs.compress());
    blk[22..22 + N].copy_from_slice(left);
    blk[22 + N..22 + 2 * N].copy_from_slice(right);
    blk[22 + 2 * N] = 0x80;
    let bits = (86 + 2 * N) * 8;
    blk[62] = (bits >> 8) as u8;
    blk[63] = bits as u8;
    blk
}

/// The `n`-byte value held in a block (bytes 22..22 + n).
#[inline(always)]
pub fn value<const N: usize>(block: &[u8; 64]) -> [u8; N] {
    let mut out = [0u8; N];
    out.copy_from_slice(&block[22..22 + N]);
    out
}

/// `T_len`, the WOTS+ public key compression, on the values held in the
/// chain blocks: `Trunc_n(Hash(PK.seed ‖ toByte(0, b − n) ‖ ADRSc ‖ v_0 ‖ … ‖ v_{len−1}))`
/// where `v_i` is the value of `blocks[i]` (bytes 22..22 + n), `Hash` is
/// SHA-256 with `b = 64` for `n = 16` and SHA-512 with `b = 128` otherwise.
///
/// The message and its padding are built here on the stack: for `n = 16`,
/// 22 + 35·16 = 582 bytes, ten SHA-256 blocks; for `n = 24`, 22 + 51·24 =
/// 1246 bytes, ten SHA-512 blocks; for `n = 32`, 22 + 67·32 = 2166 bytes,
/// eighteen SHA-512 blocks.
pub fn thash_values<const N: usize>(seed: &Seed<N>, adrs: &Adrs, blocks: &[[u8; 64]]) -> [u8; N] {
    let mlen = 22 + N * blocks.len();
    if N == 16 {
        let mut buf = [0u8; 640];
        buf[0..22].copy_from_slice(&adrs.compress());
        let mut i = 0;
        while i < blocks.len() {
            buf[22 + N * i..22 + N * i + N].copy_from_slice(&blocks[i][22..22 + N]);
            i += 1;
        }
        buf[mlen] = 0x80;
        let total = (mlen + 9 + 63) / 64 * 64;
        let bits = (64 + mlen) * 8;
        buf[total - 2] = (bits >> 8) as u8;
        buf[total - 1] = bits as u8;
        let mut st = seed.state;
        let mut off = 0;
        while off < total {
            st = compress(&st, &buf, off);
            off += 64;
        }
        trunc::<N>(&st)
    } else {
        let mut buf = [0u8; 2304];
        buf[0..22].copy_from_slice(&adrs.compress());
        let mut i = 0;
        while i < blocks.len() {
            buf[22 + N * i..22 + N * i + N].copy_from_slice(&blocks[i][22..22 + N]);
            i += 1;
        }
        buf[mlen] = 0x80;
        let total = (mlen + 17 + 127) / 128 * 128;
        let bits = (128 + mlen) * 8;
        buf[total - 2] = (bits >> 8) as u8;
        buf[total - 1] = bits as u8;
        let mut st = seed.state512;
        let mut off = 0;
        while off < total {
            st = sha512::compress(&st, &buf, off);
            off += 128;
        }
        trunc512::<N>(&st)
    }
}

/// `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ m))` for a short
/// `m` (at most 33 bytes): `F` and `PRF` (|m| = n), for every parameter set.
///
/// `ADRSc ‖ m` and the SHA-256 padding fit in a single block after the first,
/// so the block is built on the stack and compressed once from the seed state.
pub fn thash_short<const N: usize>(seed: &Seed<N>, adrs: &Adrs, m: &[u8]) -> [u8; N] {
    let blk = short_block(adrs, m);
    let st = compress(&seed.state, &blk, 0);
    trunc::<N>(&st)
}

/// `H(PK.seed, ADRS, left ‖ right)`: one SHA-256 block from the seed state
/// for `n = 16`; for `n > 16` one SHA-512 block from the SHA-512 seed state,
/// `ADRSc ‖ left ‖ right ‖ 0x80 ‖ 0… ‖ bit length` (22 + 2n + 17 <= 128).
pub fn thash_pair<const N: usize>(seed: &Seed<N>, adrs: &Adrs, left: &[u8; N], right: &[u8; N]) -> [u8; N] {
    if N == 16 {
        let blk = pair_block::<N>(adrs, left, right);
        let st = compress(&seed.state, &blk, 0);
        trunc::<N>(&st)
    } else {
        let mut blk = [0u8; 128];
        blk[0..22].copy_from_slice(&adrs.compress());
        blk[22..22 + N].copy_from_slice(left);
        blk[22 + N..22 + 2 * N].copy_from_slice(right);
        blk[22 + 2 * N] = 0x80;
        let bits = (150 + 2 * N) * 8;
        blk[126] = (bits >> 8) as u8;
        blk[127] = bits as u8;
        let st = sha512::compress(&seed.state512, &blk, 0);
        trunc512::<N>(&st)
    }
}

/// `T_l(PK.seed, ADRS, m)` for any `m` (|m| = l·n), continuing from the
/// precomputed state of the first block: SHA-256 for `n = 16`, SHA-512
/// otherwise.
pub fn thash<const N: usize>(seed: &Seed<N>, adrs: &Adrs, m: &[u8]) -> [u8; N] {
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(&adrs.compress());
    buf.extend_from_slice(m);
    let mut out = [0u8; N];
    if N == 16 {
        let d = sha256_from(&seed.state, 64, &buf);
        out.copy_from_slice(&d[0..N]);
    } else {
        let d = sha512::sha512_from(&seed.state512, 128, &buf);
        out.copy_from_slice(&d[0..N]);
    }
    out
}

/// `PRF_msg(SK.prf, opt_rand, M) = Trunc_n(HMAC-SHA-x(SK.prf, opt_rand ‖ M))`,
/// SHA-256 for `n = 16` and SHA-512 otherwise.
///
/// HMAC hashes `(K ⊕ ipad) ‖ text` and then `(K ⊕ opad) ‖ that digest`. The
/// two key blocks are built here on the stack and compressed first, so
/// `SK.prf` itself is never written to the heap.
pub fn prf_msg<const N: usize>(sk_prf: &[u8; N], opt_rand: &[u8; N], m: &[u8]) -> [u8; N] {
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(opt_rand);
    buf.extend_from_slice(m);
    let mut out = [0u8; N];
    if N == 16 {
        let mut ipad = [0x36u8; 64];
        let mut opad = [0x5cu8; 64];
        let mut i = 0;
        while i < N {
            ipad[i] = sk_prf[i] ^ 0x36;
            opad[i] = sk_prf[i] ^ 0x5c;
            i += 1;
        }
        let inner_state = compress(&H0, &ipad, 0);
        let inner = sha256_from(&inner_state, 64, &buf);
        let outer_state = compress(&H0, &opad, 0);
        let d = sha256_from(&outer_state, 64, &inner);
        out.copy_from_slice(&d[0..N]);
    } else {
        let mut ipad = [0x36u8; 128];
        let mut opad = [0x5cu8; 128];
        let mut i = 0;
        while i < N {
            ipad[i] = sk_prf[i] ^ 0x36;
            opad[i] = sk_prf[i] ^ 0x5c;
            i += 1;
        }
        let inner_state = sha512::compress(&sha512::H0, &ipad, 0);
        let inner = sha512::sha512_from(&inner_state, 128, &buf);
        let outer_state = sha512::compress(&sha512::H0, &opad, 0);
        let d = sha512::sha512_from(&outer_state, 128, &inner);
        out.copy_from_slice(&d[0..N]);
    }
    out
}

/// `SHA-256(R ‖ PK.seed ‖ PK.root ‖ M)`, the inner hash of `H_msg` for
/// `n = 16`.
///
/// When `M` has at least 16 bytes, the first block is
/// `R ‖ PK.seed ‖ PK.root ‖ M[0..16]` and the rest of `M` is hashed where it
/// lies, so a long message is never copied.
fn h_msg_inner256<const N: usize>(r: &[u8; N], pk_seed: &[u8; N], pk_root: &[u8; N], m: &[u8]) -> [u8; 32] {
    let head = 64 - 3 * N;
    if m.len() >= head {
        let mut blk = [0u8; 64];
        blk[0..N].copy_from_slice(r);
        blk[N..2 * N].copy_from_slice(pk_seed);
        blk[2 * N..3 * N].copy_from_slice(pk_root);
        blk[3 * N..64].copy_from_slice(&m[0..head]);
        let st = compress(&H0, &blk, 0);
        sha256_from(&st, 64, &m[head..m.len()])
    } else {
        let mut buf: Vec<u8> = Vec::new();
        buf.extend_from_slice(r);
        buf.extend_from_slice(pk_seed);
        buf.extend_from_slice(pk_root);
        buf.extend_from_slice(m);
        sha256(&buf)
    }
}

/// `SHA-512(R ‖ PK.seed ‖ PK.root ‖ M)`, the inner hash of `H_msg` for
/// `n > 16`, likewise: the first block is `R ‖ PK.seed ‖ PK.root` and the
/// first `128 − 3n` bytes of `M`, and the rest of a long `M` is hashed where
/// it lies.
fn h_msg_inner512<const N: usize>(r: &[u8; N], pk_seed: &[u8; N], pk_root: &[u8; N], m: &[u8]) -> [u8; 64] {
    let head = 128 - 3 * N;
    if m.len() >= head {
        let mut blk = [0u8; 128];
        blk[0..N].copy_from_slice(r);
        blk[N..2 * N].copy_from_slice(pk_seed);
        blk[2 * N..3 * N].copy_from_slice(pk_root);
        blk[3 * N..128].copy_from_slice(&m[0..head]);
        let st = sha512::compress(&sha512::H0, &blk, 0);
        sha512::sha512_from(&st, 128, &m[head..m.len()])
    } else {
        let mut buf: Vec<u8> = Vec::new();
        buf.extend_from_slice(r);
        buf.extend_from_slice(pk_seed);
        buf.extend_from_slice(pk_root);
        buf.extend_from_slice(m);
        sha512::sha512(&buf)
    }
}

/// MGF1 with SHA-256 (RFC 8017 Appendix B.2.1): the first `len` bytes of
/// `SHA-256(seed ‖ 0) ‖ SHA-256(seed ‖ 1) ‖ …` with 4-byte counters.
pub fn mgf1_sha256(seed: &[u8], len: usize) -> Vec<u8> {
    let mut t: Vec<u8> = Vec::new();
    let mut c: u32 = 0;
    while t.len() < len {
        let mut buf: Vec<u8> = Vec::new();
        buf.extend_from_slice(seed);
        buf.extend_from_slice(&[(c >> 24) as u8, (c >> 16) as u8, (c >> 8) as u8, c as u8]);
        let d = sha256(&buf);
        t.extend_from_slice(&d);
        c += 1;
    }
    let mut out: Vec<u8> = Vec::new();
    out.extend_from_slice(&t[0..len]);
    out
}

/// MGF1 with SHA-512.
pub fn mgf1_sha512(seed: &[u8], len: usize) -> Vec<u8> {
    let mut t: Vec<u8> = Vec::new();
    let mut c: u32 = 0;
    while t.len() < len {
        let mut buf: Vec<u8> = Vec::new();
        buf.extend_from_slice(seed);
        buf.extend_from_slice(&[(c >> 24) as u8, (c >> 16) as u8, (c >> 8) as u8, c as u8]);
        let d = sha512::sha512(&buf);
        t.extend_from_slice(&d);
        c += 1;
    }
    let mut out: Vec<u8> = Vec::new();
    out.extend_from_slice(&t[0..len]);
    out
}

/// `H_msg(R, PK.seed, PK.root, M) =
///  MGF1-SHA-x(R ‖ PK.seed ‖ SHA-x(R ‖ PK.seed ‖ PK.root ‖ M), m)`,
/// with SHA-256 for `n = 16` and SHA-512 otherwise. Returns `m` bytes.
pub fn h_msg<const N: usize>(p: &Params, r: &[u8; N], pk_seed: &[u8; N], pk_root: &[u8; N], m: &[u8]) -> Vec<u8> {
    let mut seed: Vec<u8> = Vec::new();
    seed.extend_from_slice(r);
    seed.extend_from_slice(pk_seed);
    if N == 16 {
        let inner = h_msg_inner256::<N>(r, pk_seed, pk_root, m);
        seed.extend_from_slice(&inner);
        mgf1_sha256(&seed, p.m)
    } else {
        let inner = h_msg_inner512::<N>(r, pk_seed, pk_root, m);
        seed.extend_from_slice(&inner);
        mgf1_sha512(&seed, p.m)
    }
}
