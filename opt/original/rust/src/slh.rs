//! SLH-DSA key generation, signing and verification (FIPS 205 §9, §10).
//!
//! Private key: SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root. Public key: PK.seed ‖ PK.root.
//! Randomness is always supplied by the caller.

use crate::address::{Adrs, FORS_TREE};
use crate::fors::{fors_pk_from_sig, fors_sign};
use crate::hash::{h_msg, prf_msg};
use crate::ht::{ht_sign, ht_verify};
use crate::params::{
    D, FORS_SIG_BYTES, HP, LEAF_BYTES, MD_BYTES, N, PK_BYTES, SIG_BYTES, SK_BYTES, TREE_BYTES,
};
use crate::util::{block, to_int};
use crate::xmss::xmss_node;

/// Algorithm 18, `slh_keygen_internal`. Returns `(SK, PK)`.
pub fn slh_keygen_internal(
    sk_seed: &[u8; N],
    sk_prf: &[u8; N],
    pk_seed: &[u8; N],
) -> ([u8; SK_BYTES], [u8; PK_BYTES]) {
    let adrs = Adrs::new().with_layer(D - 1);
    let pk_root = xmss_node(sk_seed, 0, HP, pk_seed, adrs);
    let mut sk = [0u8; SK_BYTES];
    sk[0..N].copy_from_slice(sk_seed);
    sk[N..2 * N].copy_from_slice(sk_prf);
    sk[2 * N..3 * N].copy_from_slice(pk_seed);
    sk[3 * N..4 * N].copy_from_slice(&pk_root);
    let mut pk = [0u8; PK_BYTES];
    pk[0..N].copy_from_slice(pk_seed);
    pk[N..2 * N].copy_from_slice(&pk_root);
    (sk, pk)
}

/// The tree index encoded in the message digest: 54 bits.
fn digest_tree(digest: &[u8]) -> u64 {
    to_int(&digest[MD_BYTES..MD_BYTES + TREE_BYTES]) & ((1u64 << 54) - 1)
}

/// The leaf index encoded in the message digest: 9 bits.
fn digest_leaf(digest: &[u8]) -> u32 {
    (to_int(&digest[MD_BYTES + TREE_BYTES..MD_BYTES + TREE_BYTES + LEAF_BYTES]) & ((1u64 << HP) - 1)) as u32
}

/// Algorithm 19, `slh_sign_internal`. `addrnd` is the per-signature
/// randomness; pass `PK.seed` for the deterministic variant.
pub fn slh_sign_internal(m: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Vec<u8> {
    let sk_seed = block(sk, 0);
    let sk_prf = block(sk, 1);
    let pk_seed = block(sk, 2);
    let pk_root = block(sk, 3);
    let r = prf_msg(&sk_prf, addrnd, m);
    let digest = h_msg(&r, &pk_seed, &pk_root, m);
    let idx_tree = digest_tree(&digest);
    let idx_leaf = digest_leaf(&digest);
    let adrs = Adrs::new().with_tree(idx_tree).with_type(FORS_TREE).with_keypair(idx_leaf);
    let sig_fors = fors_sign(&digest[0..MD_BYTES], &sk_seed, &pk_seed, adrs);
    let pk_fors = fors_pk_from_sig(&sig_fors, &digest[0..MD_BYTES], &pk_seed, adrs);
    let sig_ht = ht_sign(&pk_fors, &sk_seed, &pk_seed, idx_tree, idx_leaf);
    let mut sig: Vec<u8> = Vec::new();
    sig.extend_from_slice(&r);
    sig.extend_from_slice(&sig_fors);
    sig.extend_from_slice(&sig_ht);
    sig
}

/// Algorithm 20, `slh_verify_internal`.
pub fn slh_verify_internal(m: &[u8], sig: &[u8], pk: &[u8; PK_BYTES]) -> bool {
    if sig.len() != SIG_BYTES {
        return false;
    }
    let pk_seed = block(pk, 0);
    let pk_root = block(pk, 1);
    let r = block(sig, 0);
    let digest = h_msg(&r, &pk_seed, &pk_root, m);
    let idx_tree = digest_tree(&digest);
    let idx_leaf = digest_leaf(&digest);
    let adrs = Adrs::new().with_tree(idx_tree).with_type(FORS_TREE).with_keypair(idx_leaf);
    let pk_fors = fors_pk_from_sig(&sig[N..N + FORS_SIG_BYTES], &digest[0..MD_BYTES], &pk_seed, adrs);
    ht_verify(&pk_fors, &sig[N + FORS_SIG_BYTES..SIG_BYTES], &pk_seed, idx_tree, idx_leaf, &pk_root)
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
pub fn slh_sign(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Option<Vec<u8>> {
    if ctx.len() > 255 {
        return None;
    }
    let mp = with_context(m, ctx);
    Some(slh_sign_internal(&mp, sk, addrnd))
}

/// Algorithm 24, `slh_verify` (pure verification).
pub fn slh_verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8; PK_BYTES]) -> bool {
    if ctx.len() > 255 {
        return false;
    }
    let mp = with_context(m, ctx);
    slh_verify_internal(&mp, sig, pk)
}
