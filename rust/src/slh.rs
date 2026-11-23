//! SLH-DSA key generation, signing and verification (FIPS 205 §9, §10),
//! for any parameter set.
//!
//! Private key: SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root (4n bytes). Public key:
//! PK.seed ‖ PK.root (2n bytes). Randomness is always supplied by the
//! caller. `N` must be `p.n`. Keys are slices here and must have those
//! lengths; the modules `sha2_128s` … `sha2_256f` wrap these functions with
//! fixed-size array types.

use alloc::vec::Vec;
use crate::address::{Adrs, FORS_TREE};
use crate::fors::{fors_pk_from_sig, fors_sign};
use crate::hash::{h_msg, prf_msg, seed_ctx};
use crate::ht::{ht_sign, ht_verify};
use crate::params::Params;
use crate::util::{block, to_int};
use crate::xmss::xmss_node;

/// Algorithm 18, `slh_keygen_internal`. Writes `SK` (4n bytes) to `sk` and
/// `PK` (2n bytes) to `pk`.
#[inline(never)]
pub fn slh_keygen_internal<const N: usize>(
    p: &Params,
    sk_seed: &[u8; N],
    sk_prf: &[u8; N],
    pk_seed: &[u8; N],
    sk: &mut [u8],
    pk: &mut [u8],
) {
    let adrs = Adrs::new().with_layer(p.d - 1);
    let seed = seed_ctx::<N>(pk_seed);
    let pk_root = xmss_node::<N>(sk_seed, 0, p.hp, &seed, adrs);
    sk[0..N].copy_from_slice(sk_seed);
    sk[N..2 * N].copy_from_slice(sk_prf);
    sk[2 * N..3 * N].copy_from_slice(pk_seed);
    sk[3 * N..4 * N].copy_from_slice(&pk_root);
    pk[0..N].copy_from_slice(pk_seed);
    pk[N..2 * N].copy_from_slice(&pk_root);
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

// These bodies also expand in the segmented-message entry points. Keeping
// the expansion here preserves the MIR translated by the existing proofs.
macro_rules! sign_digest {
    ($N:ident, $p:ident, $sk_seed:ident, $pk_seed:ident, $r:ident, $digest:ident) => {{
        let idx_tree = digest_tree($p, &$digest);
        let idx_leaf = digest_leaf($p, &$digest);
        let adrs = Adrs::new().with_tree(idx_tree).with_type(FORS_TREE).with_keypair(idx_leaf);
        let seed = seed_ctx::<$N>(&$pk_seed);
        let md = &$digest[0..$p.md_bytes()];
        let sig_fors = fors_sign::<$N>($p, md, &$sk_seed, &seed, adrs);
        let pk_fors = fors_pk_from_sig::<$N>($p, &sig_fors, md, &seed, adrs);
        let sig_ht = ht_sign::<$N>($p, &pk_fors, &$sk_seed, &seed, idx_tree, idx_leaf);
        let mut sig: Vec<u8> = Vec::new();
        sig.extend_from_slice(&$r);
        sig.extend_from_slice(&sig_fors);
        sig.extend_from_slice(&sig_ht);
        sig
    }};
}

macro_rules! verify_digest {
    ($N:ident, $p:ident, $pk_seed:ident, $pk_root:ident, $sig:ident, $sig_bytes:ident, $fors_end:ident, $digest:ident) => {{
        let idx_tree = digest_tree($p, &$digest);
        let idx_leaf = digest_leaf($p, &$digest);
        let adrs = Adrs::new().with_tree(idx_tree).with_type(FORS_TREE).with_keypair(idx_leaf);
        let seed = seed_ctx::<$N>(&$pk_seed);
        let pk_fors = fors_pk_from_sig::<$N>($p, &$sig[$N..$fors_end], &$digest[0..$p.md_bytes()], &seed, adrs);
        ht_verify::<$N>($p, &pk_fors, &$sig[$fors_end..$sig_bytes], &seed, idx_tree, idx_leaf, &$pk_root)
    }};
}

/// Algorithm 19, `slh_sign_internal`. `addrnd` is the per-signature
/// randomness; pass `PK.seed` for the deterministic variant.
#[inline(never)]
pub fn slh_sign_internal<const N: usize>(p: &Params, m: &[u8], sk: &[u8], addrnd: &[u8; N]) -> Vec<u8> {
    let sk_seed = block::<N>(sk, 0);
    let sk_prf = block::<N>(sk, 1);
    let pk_seed = block::<N>(sk, 2);
    let pk_root = block::<N>(sk, 3);
    let r = prf_msg::<N>(&sk_prf, addrnd, m);
    let digest = h_msg::<N>(p, &r, &pk_seed, &pk_root, m);
    sign_digest!(N, p, sk_seed, pk_seed, r, digest)
}

/// Algorithm 20, `slh_verify_internal`.
pub fn slh_verify_internal<const N: usize>(p: &Params, m: &[u8], sig: &[u8], pk: &[u8]) -> bool {
    let sig_bytes = p.sig_bytes();
    if sig.len() != sig_bytes {
        return false;
    }
    let fors_end = N + p.fors_sig_bytes();
    let pk_seed = block::<N>(pk, 0);
    let pk_root = block::<N>(pk, 1);
    let r = block::<N>(sig, 0);
    let digest = h_msg::<N>(p, &r, &pk_seed, &pk_root, m);
    verify_digest!(N, p, pk_seed, pk_root, sig, sig_bytes, fors_end, digest)
}

/// `M' = toByte(0, 1) ‖ toByte(|ctx|, 1) ‖ ctx ‖ M` (Algorithms 22 and 24).
pub(crate) fn with_context(m: &[u8], ctx: &[u8]) -> Vec<u8> {
    let mut mp: Vec<u8> = Vec::new();
    mp.push(0);
    mp.push(ctx.len() as u8);
    mp.extend_from_slice(ctx);
    mp.extend_from_slice(m);
    mp
}

/// Algorithm 22, `slh_sign` (pure signing), with caller-supplied randomness.
/// Returns `None` if the context string is longer than 255 bytes.
pub fn slh_sign<const N: usize>(p: &Params, m: &[u8], ctx: &[u8], sk: &[u8], addrnd: &[u8; N]) -> Option<Vec<u8>> {
    if ctx.len() > 255 {
        return None;
    }
    #[cfg(feature = "platform-sha2")]
    if m.len() >= 1024 {
        return Some(message::sign(p, m, ctx, sk, addrnd));
    }
    let mp = with_context(m, ctx);
    Some(slh_sign_internal::<N>(p, &mp, sk, addrnd))
}

/// Algorithm 24, `slh_verify` (pure verification).
pub fn slh_verify<const N: usize>(p: &Params, m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8]) -> bool {
    if ctx.len() > 255 {
        return false;
    }
    #[cfg(feature = "platform-sha2")]
    if m.len() >= 1024 {
        return message::verify::<N>(p, m, ctx, sig, pk);
    }
    let mp = with_context(m, ctx);
    slh_verify_internal::<N>(p, &mp, sig, pk)
}

#[cfg(feature = "platform-sha2")]
mod message;
