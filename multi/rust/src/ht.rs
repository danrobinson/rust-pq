//! The hypertree (FIPS 205 §7).

use crate::address::Adrs;
use crate::params::Params;
use crate::util::bytes_eq;
use crate::xmss::{xmss_pk_from_sig, xmss_sign};

/// Algorithm 12, `ht_sign`.
pub fn ht_sign(p: &Params, m: &[u8], sk_seed: &[u8], pk_seed: &[u8], idx_tree: u64, idx_leaf: u32) -> Vec<u8> {
    let mut sig: Vec<u8> = Vec::new();
    let mut root: Vec<u8> = Vec::new();
    root.extend_from_slice(m);
    let mut tree = idx_tree;
    let mut leaf = idx_leaf;
    let mut j: u32 = 0;
    while j < p.d {
        let adrs = Adrs::new().with_layer(j).with_tree(tree);
        let s = xmss_sign(p, &root, sk_seed, leaf, pk_seed, adrs);
        root = xmss_pk_from_sig(p, leaf, &s, &root, pk_seed, adrs);
        sig.extend_from_slice(&s);
        leaf = (tree & ((1u64 << p.hp) - 1)) as u32;
        tree >>= p.hp;
        j += 1;
    }
    sig
}

/// Algorithm 13, `ht_verify`. `sig` holds `d` XMSS signatures.
pub fn ht_verify(
    p: &Params,
    m: &[u8],
    sig: &[u8],
    pk_seed: &[u8],
    idx_tree: u64,
    idx_leaf: u32,
    pk_root: &[u8],
) -> bool {
    let xs = p.xmss_sig_bytes();
    let mut node: Vec<u8> = Vec::new();
    node.extend_from_slice(m);
    let mut tree = idx_tree;
    let mut leaf = idx_leaf;
    let mut j: u32 = 0;
    while j < p.d {
        let adrs = Adrs::new().with_layer(j).with_tree(tree);
        let off = j as usize * xs;
        node = xmss_pk_from_sig(p, leaf, &sig[off..off + xs], &node, pk_seed, adrs);
        leaf = (tree & ((1u64 << p.hp) - 1)) as u32;
        tree >>= p.hp;
        j += 1;
    }
    bytes_eq(&node, pk_root)
}
