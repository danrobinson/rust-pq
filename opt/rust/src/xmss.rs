//! XMSS Merkle trees over WOTS+ keys (FIPS 205 §6).

use crate::address::{Adrs, TREE, WOTS_HASH};
use crate::hash::{thash_short, Seed};
use crate::params::{HP, LEN, N};
use crate::util::block;
use crate::wots::{wots_pk_from_sig, wots_pk_gen, wots_sign};

/// `H(PK.seed, ADRS, left ‖ right)`.
pub fn hash2(seed: &Seed, adrs: &Adrs, left: &[u8; N], right: &[u8; N]) -> [u8; N] {
    let mut buf = [0u8; 2 * N];
    buf[0..N].copy_from_slice(left);
    buf[N..2 * N].copy_from_slice(right);
    thash_short(seed, adrs, &buf)
}

/// Algorithm 9, `xmss_node`: the node at height `z`, index `i`.
pub fn xmss_node(sk_seed: &[u8; N], i: u32, z: u32, seed: &Seed, adrs: Adrs) -> [u8; N] {
    if z == 0 {
        wots_pk_gen(sk_seed, seed, adrs.with_type(WOTS_HASH).with_keypair(i))
    } else {
        let lnode = xmss_node(sk_seed, 2 * i, z - 1, seed, adrs);
        let rnode = xmss_node(sk_seed, 2 * i + 1, z - 1, seed, adrs);
        let a = adrs.with_type(TREE).with_word2(z).with_word3(i);
        hash2(seed, &a, &lnode, &rnode)
    }
}

/// Algorithm 10, `xmss_sign`: WOTS+ signature followed by the authentication path.
pub fn xmss_sign(m: &[u8; N], sk_seed: &[u8; N], idx: u32, seed: &Seed, adrs: Adrs) -> Vec<u8> {
    let mut sig = wots_sign(m, sk_seed, seed, adrs.with_type(WOTS_HASH).with_keypair(idx));
    let mut j: u32 = 0;
    while j < HP {
        let k = (idx >> j) ^ 1;
        let node = xmss_node(sk_seed, k, j, seed, adrs);
        sig.extend_from_slice(&node);
        j += 1;
    }
    sig
}

/// Climb an authentication path of `height` nodes, starting from `node` at
/// index `idx` on level 0. `auth` holds the path from block `first` onward.
/// Shared by XMSS and FORS (Algorithm 11 lines 8–18, Algorithm 17 lines 9–19).
pub fn climb(
    node: [u8; N],
    idx: u32,
    auth: &[u8],
    first: usize,
    height: u32,
    seed: &Seed,
    adrs: Adrs,
) -> [u8; N] {
    let mut node = node;
    let mut index = idx;
    let mut k: u32 = 0;
    while k < height {
        let sibling = block(auth, first + k as usize);
        let parent = index >> 1;
        let a = adrs.with_word2(k + 1).with_word3(parent);
        if index & 1 == 0 {
            node = hash2(seed, &a, &node, &sibling);
        } else {
            node = hash2(seed, &a, &sibling, &node);
        }
        index = parent;
        k += 1;
    }
    node
}

/// Algorithm 11, `xmss_pkFromSig`. `sig` holds `LEN + HP` blocks.
pub fn xmss_pk_from_sig(idx: u32, sig: &[u8], m: &[u8; N], seed: &Seed, adrs: Adrs) -> [u8; N] {
    let node = wots_pk_from_sig(sig, m, seed, adrs.with_type(WOTS_HASH).with_keypair(idx));
    climb(node, idx, sig, LEN, HP, seed, adrs.with_type(TREE))
}
