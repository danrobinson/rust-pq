//! XMSS Merkle trees over WOTS+ keys (FIPS 205 §6).

use crate::address::{Adrs, TREE, WOTS_HASH};
use crate::hash::thash_h;
use crate::params::Params;
use crate::util::block;
use crate::wots::{wots_pk_from_sig, wots_pk_gen, wots_sign};

/// `H(PK.seed, ADRS, left ‖ right)`.
pub fn hash2(p: &Params, pk_seed: &[u8], adrs: &Adrs, left: &[u8], right: &[u8]) -> Vec<u8> {
    let mut buf: Vec<u8> = Vec::new();
    buf.extend_from_slice(left);
    buf.extend_from_slice(right);
    thash_h(p, pk_seed, adrs, &buf)
}

/// Algorithm 9, `xmss_node`: the node at height `z`, index `i`.
pub fn xmss_node(p: &Params, sk_seed: &[u8], i: u32, z: u32, pk_seed: &[u8], adrs: Adrs) -> Vec<u8> {
    if z == 0 {
        wots_pk_gen(p, sk_seed, pk_seed, adrs.with_type(WOTS_HASH).with_keypair(i))
    } else {
        let lnode = xmss_node(p, sk_seed, 2 * i, z - 1, pk_seed, adrs);
        let rnode = xmss_node(p, sk_seed, 2 * i + 1, z - 1, pk_seed, adrs);
        let a = adrs.with_type(TREE).with_word2(z).with_word3(i);
        hash2(p, pk_seed, &a, &lnode, &rnode)
    }
}

/// Algorithm 10, `xmss_sign`: WOTS+ signature followed by the authentication path.
pub fn xmss_sign(p: &Params, m: &[u8], sk_seed: &[u8], idx: u32, pk_seed: &[u8], adrs: Adrs) -> Vec<u8> {
    let mut sig = wots_sign(p, m, sk_seed, pk_seed, adrs.with_type(WOTS_HASH).with_keypair(idx));
    let mut j: u32 = 0;
    while j < p.hp {
        let k = (idx >> j) ^ 1;
        let node = xmss_node(p, sk_seed, k, j, pk_seed, adrs);
        sig.extend_from_slice(&node);
        j += 1;
    }
    sig
}

/// Climb an authentication path of `height` nodes, starting from `node` at
/// index `idx` on level 0. `auth` holds the path from block `first` onward.
/// Shared by XMSS and FORS (Algorithm 11 lines 8–18, Algorithm 17 lines 9–19).
pub fn climb(
    p: &Params,
    node: Vec<u8>,
    idx: u32,
    auth: &[u8],
    first: usize,
    height: u32,
    pk_seed: &[u8],
    adrs: Adrs,
) -> Vec<u8> {
    let mut node = node;
    let mut index = idx;
    let mut k: u32 = 0;
    while k < height {
        let sibling = block(auth, p.n, first + k as usize);
        let parent = index >> 1;
        let a = adrs.with_word2(k + 1).with_word3(parent);
        if index & 1 == 0 {
            node = hash2(p, pk_seed, &a, &node, &sibling);
        } else {
            node = hash2(p, pk_seed, &a, &sibling, &node);
        }
        index = parent;
        k += 1;
    }
    node
}

/// Algorithm 11, `xmss_pkFromSig`. `sig` holds `len + h'` blocks.
pub fn xmss_pk_from_sig(p: &Params, idx: u32, sig: &[u8], m: &[u8], pk_seed: &[u8], adrs: Adrs) -> Vec<u8> {
    let node = wots_pk_from_sig(p, sig, m, pk_seed, adrs.with_type(WOTS_HASH).with_keypair(idx));
    climb(p, node, idx, sig, p.len(), p.hp, pk_seed, adrs.with_type(TREE))
}
