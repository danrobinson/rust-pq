//! SLH-DSA key generation, signing and verification (FIPS 205 §9, §10),
//! for any parameter set.
//!
//! Private key: SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root (4n bytes). Public key:
//! PK.seed ‖ PK.root (2n bytes). Seeds and `addrnd` are n bytes. Randomness
//! is always supplied by the caller. These functions index into their
//! arguments and so require them to have those lengths; the modules
//! `sha2_128s` … `sha2_256f` wrap them with fixed-size array types.

use crate::address::{Adrs, FORS_TREE};
use crate::fors::{fors_pk_from_sig, fors_sign};
use crate::hash::{h_msg, prf_msg};
use crate::ht::{ht_sign, ht_verify};
use crate::params::Params;
use crate::util::{block, to_int};
use crate::xmss::xmss_node;

/// Algorithm 18, `slh_keygen_internal`. Returns `(SK, PK)`.
pub fn slh_keygen_internal(p: &Params, sk_seed: &[u8], sk_prf: &[u8], pk_seed: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let adrs = Adrs::new().with_layer(p.d - 1);
    let pk_root = xmss_node(p, sk_seed, 0, p.hp, pk_seed, adrs);
    let mut sk: Vec<u8> = Vec::new();
    sk.extend_from_slice(sk_seed);
    sk.extend_from_slice(sk_prf);
    sk.extend_from_slice(pk_seed);
    sk.extend_from_slice(&pk_root);
    let mut pk: Vec<u8> = Vec::new();
    pk.extend_from_slice(pk_seed);
    pk.extend_from_slice(&pk_root);
    (sk, pk)
}

/// The tree index encoded in the message digest: h − h/d bits (at most 64).
fn digest_tree(p: &Params, digest: &[u8]) -> u64 {
    let lo = p.md_bytes();
    to_int(&digest[lo..lo + p.tree_bytes()]) & (u64::MAX >> (64 - p.tree_bits()))
}

/// The leaf index encoded in the message digest: h/d bits.
fn digest_leaf(p: &Params, digest: &[u8]) -> u32 {
    let lo = p.md_bytes() + p.tree_bytes();
    (to_int(&digest[lo..lo + p.leaf_bytes()]) & ((1u64 << p.hp) - 1)) as u32
}

/// Algorithm 19, `slh_sign_internal`. `addrnd` is the per-signature
/// randomness; pass `PK.seed` for the deterministic variant.
pub fn slh_sign_internal(p: &Params, m: &[u8], sk: &[u8], addrnd: &[u8]) -> Vec<u8> {
    let sk_seed = block(sk, p.n, 0);
    let sk_prf = block(sk, p.n, 1);
    let pk_seed = block(sk, p.n, 2);
    let pk_root = block(sk, p.n, 3);
    let r = prf_msg(p, &sk_prf, addrnd, m);
    let digest = h_msg(p, &r, &pk_seed, &pk_root, m);
    let idx_tree = digest_tree(p, &digest);
    let idx_leaf = digest_leaf(p, &digest);
    let adrs = Adrs::new().with_tree(idx_tree).with_type(FORS_TREE).with_keypair(idx_leaf);
    let md = &digest[0..p.md_bytes()];
    let sig_fors = fors_sign(p, md, &sk_seed, &pk_seed, adrs);
    let pk_fors = fors_pk_from_sig(p, &sig_fors, md, &pk_seed, adrs);
    let sig_ht = ht_sign(p, &pk_fors, &sk_seed, &pk_seed, idx_tree, idx_leaf);
    let mut sig: Vec<u8> = Vec::new();
    sig.extend_from_slice(&r);
    sig.extend_from_slice(&sig_fors);
    sig.extend_from_slice(&sig_ht);
    sig
}

/// Algorithm 20, `slh_verify_internal`.
pub fn slh_verify_internal(p: &Params, m: &[u8], sig: &[u8], pk: &[u8]) -> bool {
    let sig_bytes = p.sig_bytes();
    if sig.len() != sig_bytes {
        return false;
    }
    let n = p.n;
    let fors_end = n + p.fors_sig_bytes();
    let pk_seed = block(pk, n, 0);
    let pk_root = block(pk, n, 1);
    let r = block(sig, n, 0);
    let digest = h_msg(p, &r, &pk_seed, &pk_root, m);
    let idx_tree = digest_tree(p, &digest);
    let idx_leaf = digest_leaf(p, &digest);
    let adrs = Adrs::new().with_tree(idx_tree).with_type(FORS_TREE).with_keypair(idx_leaf);
    let pk_fors = fors_pk_from_sig(p, &sig[n..fors_end], &digest[0..p.md_bytes()], &pk_seed, adrs);
    ht_verify(p, &pk_fors, &sig[fors_end..sig_bytes], &pk_seed, idx_tree, idx_leaf, &pk_root)
}

/// `M' = toByte(0, 1) ‖ toByte(|ctx|, 1) ‖ ctx ‖ M` (Algorithms 22 and 24).
fn with_context(m: &[u8], ctx: &[u8]) -> Vec<u8> {
    let mut mp: Vec<u8> = Vec::new();
    mp.push(0);
    mp.push(ctx.len() as u8);
    mp.extend_from_slice(ctx);
    mp.extend_from_slice(m);
    mp
}

/// Algorithm 22, `slh_sign` (pure signing), with caller-supplied randomness.
/// Returns `None` if the context string is longer than 255 bytes.
pub fn slh_sign(p: &Params, m: &[u8], ctx: &[u8], sk: &[u8], addrnd: &[u8]) -> Option<Vec<u8>> {
    if ctx.len() > 255 {
        return None;
    }
    let mp = with_context(m, ctx);
    Some(slh_sign_internal(p, &mp, sk, addrnd))
}

/// Algorithm 24, `slh_verify` (pure verification).
pub fn slh_verify(p: &Params, m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8]) -> bool {
    if ctx.len() > 255 {
        return false;
    }
    let mp = with_context(m, ctx);
    slh_verify_internal(p, &mp, sig, pk)
}
