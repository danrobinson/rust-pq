//! The SLH-DSA hash functions for SHA2, security category 1 (FIPS 205 §11.2.1).

use crate::address::Adrs;
use crate::params::{M, N};
use crate::sha256::{hmac_sha256, sha256};

/// `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ m))`.
///
/// This one function is `F` (|m| = n), `H` (|m| = 2n), `T_l` (|m| = l·n) and,
/// with `m = SK.seed`, `PRF`.
pub fn thash(pk_seed: &[u8; N], adrs: &Adrs, m: &[u8]) -> [u8; N] {
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(pk_seed);
    buf.extend_from_slice(&[0u8; 48]);
    buf.extend_from_slice(&adrs.compress());
    buf.extend_from_slice(m);
    let d = sha256(&buf);
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

/// `H_msg(R, PK.seed, PK.root, M) =
///  MGF1-SHA-256(R ‖ PK.seed ‖ SHA-256(R ‖ PK.seed ‖ PK.root ‖ M), m)`.
///
/// Since m = 30 <= 32, MGF1 is a single SHA-256 call with counter 0.
pub fn h_msg(r: &[u8; N], pk_seed: &[u8; N], pk_root: &[u8; N], m: &[u8]) -> [u8; M] {
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(r);
    buf.extend_from_slice(pk_seed);
    buf.extend_from_slice(pk_root);
    buf.extend_from_slice(m);
    let inner = sha256(&buf);
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
