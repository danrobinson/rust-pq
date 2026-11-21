//! The SLH-DSA hash functions for SHA2 (FIPS 205 §11.2.1 and §11.2.2).
//!
//! `n = 16` (security category 1) uses SHA-256 throughout. `n = 24, 32`
//! (categories 3 and 5) use SHA-512 for `H`, `T_l`, `H_msg` and `PRF_msg`,
//! and SHA-256 for `F` and `PRF`.

use crate::address::Adrs;
use crate::params::Params;
use crate::sha256::{hmac_sha256, sha256};
use crate::sha512::{hmac_sha512, sha512};

/// `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ m))`.
///
/// This is `F` (|m| = n) and, with `m = SK.seed`, `PRF`, for every
/// parameter set; for `n = 16` it is also `H` and `T_l`.
pub fn thash_f(p: &Params, pk_seed: &[u8], adrs: &Adrs, m: &[u8]) -> Vec<u8> {
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(pk_seed);
    let zeros = [0u8; 64];
    buf.extend_from_slice(&zeros[0..64 - p.n]);
    buf.extend_from_slice(&adrs.compress());
    buf.extend_from_slice(m);
    let d = sha256(&buf);
    let mut out: Vec<u8> = Vec::new();
    out.extend_from_slice(&d[0..p.n]);
    out
}

/// `H` (|m| = 2n) and `T_l` (|m| = l·n): as `thash_f` for `n = 16`, and
/// `Trunc_n(SHA-512(PK.seed ‖ toByte(0, 128 − n) ‖ ADRSc ‖ m))` otherwise.
pub fn thash_h(p: &Params, pk_seed: &[u8], adrs: &Adrs, m: &[u8]) -> Vec<u8> {
    if p.n == 16 {
        thash_f(p, pk_seed, adrs, m)
    } else {
        let mut buf: Vec<u8> = Vec::new();
        buf.extend_from_slice(pk_seed);
        let zeros = [0u8; 128];
        buf.extend_from_slice(&zeros[0..128 - p.n]);
        buf.extend_from_slice(&adrs.compress());
        buf.extend_from_slice(m);
        let d = sha512(&buf);
        let mut out: Vec<u8> = Vec::new();
        out.extend_from_slice(&d[0..p.n]);
        out
    }
}

/// `PRF_msg(SK.prf, opt_rand, M) = Trunc_n(HMAC-SHA-x(SK.prf, opt_rand ‖ M))`,
/// with SHA-256 for `n = 16` and SHA-512 otherwise.
pub fn prf_msg(p: &Params, sk_prf: &[u8], opt_rand: &[u8], m: &[u8]) -> Vec<u8> {
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(opt_rand);
    buf.extend_from_slice(m);
    let mut out: Vec<u8> = Vec::new();
    if p.n == 16 {
        let d = hmac_sha256(sk_prf, &buf);
        out.extend_from_slice(&d[0..p.n]);
    } else {
        let d = hmac_sha512(sk_prf, &buf);
        out.extend_from_slice(&d[0..p.n]);
    }
    out
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
        let d = sha512(&buf);
        t.extend_from_slice(&d);
        c += 1;
    }
    let mut out: Vec<u8> = Vec::new();
    out.extend_from_slice(&t[0..len]);
    out
}

/// `H_msg(R, PK.seed, PK.root, M) =
///  MGF1-SHA-x(R ‖ PK.seed ‖ SHA-x(R ‖ PK.seed ‖ PK.root ‖ M), m)`,
/// with SHA-256 for `n = 16` and SHA-512 otherwise.
pub fn h_msg(p: &Params, r: &[u8], pk_seed: &[u8], pk_root: &[u8], m: &[u8]) -> Vec<u8> {
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(r);
    buf.extend_from_slice(pk_seed);
    buf.extend_from_slice(pk_root);
    buf.extend_from_slice(m);
    let mut seed: Vec<u8> = Vec::new();
    seed.extend_from_slice(r);
    seed.extend_from_slice(pk_seed);
    if p.n == 16 {
        let inner = sha256(&buf);
        seed.extend_from_slice(&inner);
        mgf1_sha256(&seed, p.m)
    } else {
        let inner = sha512(&buf);
        seed.extend_from_slice(&inner);
        mgf1_sha512(&seed, p.m)
    }
}
