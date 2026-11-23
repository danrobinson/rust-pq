//! The hypertree (FIPS 205 §7).

use alloc::vec::Vec;
use crate::address::Adrs;
use super::hash::Seed;
use crate::params::Params;
use super::xmss::{xmss_pk_from_sig, xmss_sign};

/// Algorithm 12, `ht_sign`.
pub fn ht_sign<const N: usize>(
    p: &Params,
    m: &[u8; N],
    sk_seed: &[u8; N],
    seed: &Seed<N>,
    idx_tree: u64,
    idx_leaf: u32,
) -> Vec<u8> {
    let mut sig: Vec<u8> = Vec::new();
    let mut root = *m;
    let mut tree = idx_tree;
    let mut leaf = idx_leaf;
    let mut j: u32 = 0;
    while j < p.d {
        let adrs = Adrs::new().with_layer(j).with_tree(tree);
        let s = xmss_sign::<N>(p, &root, sk_seed, leaf, seed, adrs);
        root = next_message(p, j, leaf, &s, &root, seed, adrs);
        sig.extend_from_slice(&s);
        leaf = (tree & ((1u64 << p.hp) - 1)) as u32;
        tree >>= p.hp;
        j += 1;
    }
    sig
}

// The next layer signs this root. The final layer has no successor.
fn next_message<const N: usize>(
    p: &Params, j: u32, leaf: u32, sig: &[u8], message: &[u8; N], seed: &Seed<N>, adrs: Adrs,
) -> [u8; N] {
    if j + 1 < p.d {
        xmss_pk_from_sig(p, leaf, sig, message, seed, adrs)
    } else {
        *message
    }
}

/// Algorithm 13, `ht_verify`. `sig` holds `d` XMSS signatures.
pub fn ht_verify<const N: usize>(
    p: &Params,
    m: &[u8; N],
    sig: &[u8],
    seed: &Seed<N>,
    idx_tree: u64,
    idx_leaf: u32,
    pk_root: &[u8; N],
) -> bool {
    let xs = p.xmss_sig_bytes();
    let mut node = *m;
    let mut tree = idx_tree;
    let mut leaf = idx_leaf;
    let mut j: u32 = 0;
    while j < p.d {
        let adrs = Adrs::new().with_layer(j).with_tree(tree);
        let off = j as usize * xs;
        node = xmss_pk_from_sig::<N>(p, leaf, &sig[off..off + xs], &node, seed, adrs);
        leaf = (tree & ((1u64 << p.hp) - 1)) as u32;
        tree >>= p.hp;
        j += 1;
    }
    node == *pk_root
}
