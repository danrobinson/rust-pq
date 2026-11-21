//! The SLH-DSA hash functions for SHA2, security category 1 (FIPS 205 §11.2.1).

use crate::address::Adrs;
use crate::params::{M, N};
use crate::sha256::{compress, hmac_sha256_parts, Sha256, H0};

/// Variant A: PK.seed together with the SHA-256 state after the constant
/// first block `PK.seed ‖ toByte(0, 48)`.
pub struct SeedCtx {
    pub seed: [u8; N],
    pub mid: [u32; 8],
}

impl SeedCtx {
    pub fn new(pk_seed: &[u8; N]) -> SeedCtx {
        let mut blk = [0u8; 64];
        blk[0..N].copy_from_slice(pk_seed);
        SeedCtx { seed: *pk_seed, mid: compress(&H0, &blk, 0) }
    }
}

/// `Trunc_n(SHA-256(PK.seed ‖ toByte(0, 64 − n) ‖ ADRSc ‖ m))`, from the midstate.
pub fn thash(pk_seed: &SeedCtx, adrs: &Adrs, m: &[u8]) -> [u8; N] {
    let mut h = Sha256::from_mid(&pk_seed.mid, 64);
    h.update(&adrs.compress());
    h.update(m);
    let d = h.finalize();
    let mut out = [0u8; N];
    out.copy_from_slice(&d[0..N]);
    out
}

/// `PRF_msg(SK.prf, opt_rand, M) = Trunc_n(HMAC-SHA-256(SK.prf, opt_rand ‖ M))`.
pub fn prf_msg(sk_prf: &[u8; N], opt_rand: &[u8; N], m: &[u8]) -> [u8; N] {
    let d = hmac_sha256_parts(sk_prf, opt_rand, m);
    let mut out = [0u8; N];
    out.copy_from_slice(&d[0..N]);
    out
}

/// `H_msg(R, PK.seed, PK.root, M) =
///  MGF1-SHA-256(R ‖ PK.seed ‖ SHA-256(R ‖ PK.seed ‖ PK.root ‖ M), m)`.
pub fn h_msg(r: &[u8; N], pk_seed: &[u8; N], pk_root: &[u8; N], m: &[u8]) -> [u8; M] {
    let mut h = Sha256::new();
    h.update(r);
    h.update(pk_seed);
    h.update(pk_root);
    h.update(m);
    let inner = h.finalize();
    let mut g = Sha256::new();
    g.update(r);
    g.update(pk_seed);
    g.update(&inner);
    g.update(&[0u8; 4]);
    let d = g.finalize();
    let mut out = [0u8; M];
    out.copy_from_slice(&d[0..M]);
    out
}
