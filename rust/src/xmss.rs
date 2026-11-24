//! XMSS Merkle trees over WOTS+ keys (FIPS 205 §6).

use alloc::vec::Vec;
use crate::address::{Adrs, TREE, WOTS_HASH};
use super::hash::{thash_pair, Seed};
use crate::params::{Params, LEN2};
use crate::util::block;
use super::wots::{wots_pk_from_sig, wots_pk_gen, wots_sign};

/// `H(PK.seed, ADRS, left ‖ right)`.
pub fn hash2<const N: usize>(seed: &Seed<N>, adrs: &Adrs, left: &[u8; N], right: &[u8; N]) -> [u8; N] {
    thash_pair::<N>(seed, adrs, left, right)
}

/// Algorithm 9, `xmss_node`: the node at height `z`, index `i`.
pub fn xmss_node<const N: usize>(sk_seed: &[u8; N], i: u32, z: u32, seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    sha2_only! {
        #[cfg(all(feature = "platform-sha2", target_arch = "x86_64", target_feature = "sse2"))]
        if matches!(N, 16 | 24 | 32) && (2..=4).contains(&z) && crate::sha256::x86::avx512_available() {
            return wide::batch_root(sk_seed, i, z, seed, adrs);
        }
        #[cfg(all(feature = "platform-sha2", target_arch = "aarch64", target_endian = "little"))]
        if matches!(N, 16 | 24 | 32) && (1..=4).contains(&z) && crate::sha256::arm_wide::available() {
            return arm::batch_root(sk_seed, i, z, seed, adrs);
        }
    }
    shake_only! {
        #[cfg(all(feature = "parallel", target_arch = "x86_64", target_feature = "sse2"))]
        if z == 3 && super::batch::available::<N>() {
            return super::batch::subtree8(sk_seed, seed, i, adrs);
        }
    }
    if z == 0 {
        wots_pk_gen::<N>(sk_seed, seed, adrs.with_type(WOTS_HASH).with_keypair(i))
    } else {
        let lnode = xmss_node::<N>(sk_seed, 2 * i, z - 1, seed, adrs);
        let rnode = xmss_node::<N>(sk_seed, 2 * i + 1, z - 1, seed, adrs);
        let a = adrs.with_type(TREE).with_word2(z).with_word3(i);
        hash2::<N>(seed, &a, &lnode, &rnode)
    }
}

/// Algorithm 10, `xmss_sign`: WOTS+ signature followed by the authentication path.
pub fn xmss_sign<const N: usize>(
    p: &Params,
    m: &[u8; N],
    sk_seed: &[u8; N],
    idx: u32,
    seed: &Seed<N>,
    adrs: Adrs,
) -> Vec<u8> {
    let mut sig = wots_sign::<N>(m, sk_seed, seed, adrs.with_type(WOTS_HASH).with_keypair(idx));
    let mut j: u32 = 0;
    while j < p.hp {
        let k = (idx >> j) ^ 1;
        let node = xmss_node::<N>(sk_seed, k, j, seed, adrs);
        sig.extend_from_slice(&node);
        j += 1;
    }
    sig
}

/// Climb an authentication path of `height` nodes, starting from `node` at
/// index `idx` on level 0. `auth` holds the path from block `first` onward.
/// (Algorithm 11 lines 8–18.)
pub fn climb<const N: usize>(
    node: [u8; N],
    idx: u32,
    auth: &[u8],
    first: usize,
    height: u32,
    seed: &Seed<N>,
    adrs: Adrs,
) -> [u8; N] {
    let mut node = node;
    let mut index = idx;
    let mut k: u32 = 0;
    while k < height {
        let sibling = block::<N>(auth, first + k as usize);
        let parent = index >> 1;
        let a = adrs.with_word2(k + 1).with_word3(parent);
        if index & 1 == 0 {
            node = hash2::<N>(seed, &a, &node, &sibling);
        } else {
            node = hash2::<N>(seed, &a, &sibling, &node);
        }
        index = parent;
        k += 1;
    }
    node
}

/// Algorithm 11, `xmss_pkFromSig`. `sig` holds `len + h'` blocks.
pub fn xmss_pk_from_sig<const N: usize>(
    p: &Params,
    idx: u32,
    sig: &[u8],
    m: &[u8; N],
    seed: &Seed<N>,
    adrs: Adrs,
) -> [u8; N] {
    let node = wots_pk_from_sig::<N>(sig, m, seed, adrs.with_type(WOTS_HASH).with_keypair(idx));
    climb::<N>(node, idx, sig, 2 * N + LEN2, p.hp, seed, adrs.with_type(TREE))
}

sha2_only! {
    #[cfg(all(feature = "platform-sha2", target_arch = "x86_64", target_feature = "sse2"))]
    mod wide;
    #[cfg(all(feature = "platform-sha2", target_arch = "aarch64", target_endian = "little"))]
    mod arm;
}
