//! The hypertree (FIPS 205 §7).

use crate::address::Adrs;
use crate::hash::Seed;
use crate::params::{D, HP, N, XMSS_SIG_BYTES};
use crate::xmss::{xmss_pk_from_sig, xmss_sign};

/// Algorithm 12, `ht_sign`.
pub fn ht_sign(m: &[u8; N], sk_seed: &[u8; N], seed: &Seed, idx_tree: u64, idx_leaf: u32) -> Vec<u8> {
    let mut sig: Vec<u8> = Vec::new();
    let mut root = *m;
    let mut tree = idx_tree;
    let mut leaf = idx_leaf;
    let mut j: u32 = 0;
    while j < D {
        let adrs = Adrs::new().with_layer(j).with_tree(tree);
        let s = xmss_sign(&root, sk_seed, leaf, seed, adrs);
        root = xmss_pk_from_sig(leaf, &s, &root, seed, adrs);
        sig.extend_from_slice(&s);
        leaf = (tree & ((1u64 << HP) - 1)) as u32;
        tree >>= HP;
        j += 1;
    }
    sig
}

/// Algorithm 13, `ht_verify`. `sig` holds `D` XMSS signatures.
pub fn ht_verify(
    m: &[u8; N],
    sig: &[u8],
    seed: &Seed,
    idx_tree: u64,
    idx_leaf: u32,
    pk_root: &[u8; N],
) -> bool {
    let mut node = *m;
    let mut tree = idx_tree;
    let mut leaf = idx_leaf;
    let mut j: u32 = 0;
    while j < D {
        let adrs = Adrs::new().with_layer(j).with_tree(tree);
        let off = j as usize * XMSS_SIG_BYTES;
        node = xmss_pk_from_sig(leaf, &sig[off..off + XMSS_SIG_BYTES], &node, seed, adrs);
        leaf = (tree & ((1u64 << HP) - 1)) as u32;
        tree >>= HP;
        j += 1;
    }
    node == *pk_root
}
