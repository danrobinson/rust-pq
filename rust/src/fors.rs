//! FORS few-time signatures (FIPS 205 §8).

use alloc::vec::Vec;
use crate::address::{Adrs, FORS_PRF, FORS_ROOTS};
use crate::hash::{chain_blocks, pair_block, short_block, thash, thash_pair, thash_short, value, Seed};
use crate::params::{Params, K_MAX};
use crate::util::{base_2b, block};
use crate::xmss::hash2;

/// Algorithm 14, `fors_skGen`.
pub fn fors_sk_gen<const N: usize>(sk_seed: &[u8; N], seed: &Seed<N>, adrs: Adrs, idx: u32) -> [u8; N] {
    let sk_adrs = adrs.with_type(FORS_PRF).with_keypair(adrs.keypair).with_word3(idx);
    thash_short::<N>(seed, &sk_adrs, sk_seed)
}

/// Height of the subtrees that are computed in one batch: 128 leaves.
const BATCH_HEIGHT: u32 = 7;
const BATCH: usize = 128;

/// The node at height `z <= BATCH_HEIGHT`, index `i`: its `2^z` leaves
/// together, then one level at a time.
///
/// A leaf is `F` of `PRF` at the same tree index, and the two blocks differ
/// only in the address type. So each of the two is one step of
/// [`chain_blocks`] on all the leaf blocks, numbered by the tree index. A
/// node above the leaves is `H` of its children. For `n = 16` that is a
/// single SHA-256 block whose last address word is its tree index: again one
/// step, on the blocks of a level. For `n > 16` it is one SHA-512 block,
/// computed node by node.
fn fors_batch<const N: usize>(sk_seed: &[u8; N], i: u32, z: u32, seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    let n = 1usize << z;
    let prf_adrs = adrs.with_type(FORS_PRF).with_keypair(adrs.keypair);
    let mut blocks = [[0u8; 64]; BATCH];
    let mut start = [0u32; BATCH];
    let mut end = [0u32; BATCH];
    let mut j = 0;
    while j < n {
        let idx = (i << z) + j as u32;
        blocks[j] = short_block(&prf_adrs.with_word3(idx), sk_seed);
        start[j] = idx;
        end[j] = idx + 1;
        j += 1;
    }
    chain_blocks::<N>(&seed.state, &mut blocks[0..n], &start, &end);
    let mut j = 0;
    while j < n {
        blocks[j][9] = adrs.typ as u8;
        j += 1;
    }
    chain_blocks::<N>(&seed.state, &mut blocks[0..n], &start, &end);
    let mut vals = [[0u8; N]; BATCH];
    let mut j = 0;
    while j < n {
        vals[j] = value::<N>(&blocks[j]);
        j += 1;
    }
    let mut lvl: u32 = 1;
    let mut cnt = n / 2;
    while lvl <= z {
        if N == 16 {
            let mut j = 0;
            while j < cnt {
                let idx = (i << (z - lvl)) + j as u32;
                blocks[j] = pair_block::<N>(&adrs.with_word2(lvl).with_word3(idx), &vals[2 * j], &vals[2 * j + 1]);
                start[j] = idx;
                end[j] = idx + 1;
                j += 1;
            }
            chain_blocks::<N>(&seed.state, &mut blocks[0..cnt], &start, &end);
            let mut j = 0;
            while j < cnt {
                vals[j] = value::<N>(&blocks[j]);
                j += 1;
            }
        } else {
            let mut j = 0;
            while j < cnt {
                let idx = (i << (z - lvl)) + j as u32;
                vals[j] = thash_pair::<N>(seed, &adrs.with_word2(lvl).with_word3(idx), &vals[2 * j], &vals[2 * j + 1]);
                j += 1;
            }
        }
        cnt /= 2;
        lvl += 1;
    }
    vals[0]
}

/// Algorithm 15, `fors_node`: the node at height `z`, index `i`.
pub fn fors_node<const N: usize>(sk_seed: &[u8; N], i: u32, z: u32, seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    if z <= BATCH_HEIGHT {
        fors_batch::<N>(sk_seed, i, z, seed, adrs)
    } else {
        let lnode = fors_node::<N>(sk_seed, 2 * i, z - 1, seed, adrs);
        let rnode = fors_node::<N>(sk_seed, 2 * i + 1, z - 1, seed, adrs);
        hash2::<N>(seed, &adrs.with_word2(z).with_word3(i), &lnode, &rnode)
    }
}

/// Algorithm 16, `fors_sign`. `md` holds at least ceil(k·a/8) bytes.
pub fn fors_sign<const N: usize>(p: &Params, md: &[u8], sk_seed: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> Vec<u8> {
    let a = p.a;
    let indices = base_2b(md, a, p.k as usize);
    let mut sig: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < p.k {
        let idx = indices[i as usize];
        let sk = fors_sk_gen::<N>(sk_seed, seed, adrs, (i << a) + idx);
        sig.extend_from_slice(&sk);
        let mut j: u32 = 0;
        while j < a {
            let s = (idx >> j) ^ 1;
            let node = fors_node::<N>(sk_seed, (i << (a - j)) + s, j, seed, adrs);
            sig.extend_from_slice(&node);
            j += 1;
        }
        i += 1;
    }
    sig
}

/// Algorithm 17, `fors_pkFromSig`. `sig` holds `k·(1 + a)` blocks.
///
/// The `k` trees are independent, so they are climbed together: the leaves
/// are one step of [`chain_blocks`] on `k` blocks, and for `n = 16` so is
/// each level of the authentication paths. (For `n > 16` a level is `k`
/// SHA-512 blocks, one after another.)
pub fn fors_pk_from_sig<const N: usize>(p: &Params, sig: &[u8], md: &[u8], seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    let a = p.a;
    let k = p.k as usize;
    let indices = base_2b(md, a, k);
    let mut blocks = [[0u8; 64]; K_MAX];
    let mut idx = [0u32; K_MAX];
    let mut end = [0u32; K_MAX];
    let mut i = 0;
    while i < k {
        let leaf = ((i as u32) << a) + indices[i];
        let sk = block::<N>(sig, i * (a as usize + 1));
        blocks[i] = short_block(&adrs.with_word2(0).with_word3(leaf), &sk);
        idx[i] = leaf;
        end[i] = leaf + 1;
        i += 1;
    }
    chain_blocks::<N>(&seed.state, &mut blocks[0..k], &idx, &end);
    let mut vals = [[0u8; N]; K_MAX];
    let mut i = 0;
    while i < k {
        vals[i] = value::<N>(&blocks[i]);
        i += 1;
    }
    let mut h: u32 = 0;
    while h < a {
        if N == 16 {
            let mut i = 0;
            while i < k {
                let sibling = block::<N>(sig, i * (a as usize + 1) + 1 + h as usize);
                let parent = idx[i] >> 1;
                let adr = adrs.with_word2(h + 1).with_word3(parent);
                if idx[i] & 1 == 0 {
                    blocks[i] = pair_block::<N>(&adr, &vals[i], &sibling);
                } else {
                    blocks[i] = pair_block::<N>(&adr, &sibling, &vals[i]);
                }
                idx[i] = parent;
                end[i] = parent + 1;
                i += 1;
            }
            chain_blocks::<N>(&seed.state, &mut blocks[0..k], &idx, &end);
            let mut i = 0;
            while i < k {
                vals[i] = value::<N>(&blocks[i]);
                i += 1;
            }
        } else {
            let mut i = 0;
            while i < k {
                let sibling = block::<N>(sig, i * (a as usize + 1) + 1 + h as usize);
                let parent = idx[i] >> 1;
                let adr = adrs.with_word2(h + 1).with_word3(parent);
                if idx[i] & 1 == 0 {
                    vals[i] = thash_pair::<N>(seed, &adr, &vals[i], &sibling);
                } else {
                    vals[i] = thash_pair::<N>(seed, &adr, &sibling, &vals[i]);
                }
                idx[i] = parent;
                i += 1;
            }
        }
        h += 1;
    }
    let mut roots: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < k {
        roots.extend_from_slice(&vals[i]);
        i += 1;
    }
    let pk_adrs = adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair);
    thash::<N>(seed, &pk_adrs, &roots)
}

/// The FORS public key of the key pair at `adrs`, computed from the secret
/// seed alone: the roots of the `k` trees, compressed. It is what
/// [`fors_pk_from_sig`] returns for every signature [`fors_sign`] makes with
/// this key pair, reached by a different computation; the checked signer
/// compares the two.
pub fn fors_pk_gen<const N: usize>(p: &Params, sk_seed: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    let mut roots: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < p.k {
        let root = fors_node::<N>(sk_seed, i, p.a, seed, adrs);
        roots.extend_from_slice(&root);
        i += 1;
    }
    let pk_adrs = adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair);
    thash::<N>(seed, &pk_adrs, &roots)
}
