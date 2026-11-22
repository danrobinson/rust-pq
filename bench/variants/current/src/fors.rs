//! FORS few-time signatures (FIPS 205 §8).

use alloc::vec::Vec;
use crate::address::{Adrs, FORS_PRF, FORS_ROOTS};
use crate::hash::{chain_blocks, pair_block, short_block, thash, thash_short, value, Seed};
use crate::params::{A, K, N};
use crate::util::{base_2b, block};
use crate::xmss::hash2;

/// Algorithm 14, `fors_skGen`.
pub fn fors_sk_gen(sk_seed: &[u8; N], seed: &Seed, adrs: Adrs, idx: u32) -> [u8; N] {
    let sk_adrs = adrs.with_type(FORS_PRF).with_keypair(adrs.keypair).with_word3(idx);
    thash_short(seed, &sk_adrs, sk_seed)
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
/// node above the leaves is `H` of its children, a single block whose last
/// address word is its tree index: again one step, on the blocks of a level.
fn fors_batch(sk_seed: &[u8; N], i: u32, z: u32, seed: &Seed, adrs: Adrs) -> [u8; N] {
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
    chain_blocks(&seed.state, &mut blocks[0..n], &start, &end);
    let mut j = 0;
    while j < n {
        blocks[j][9] = adrs.typ as u8;
        j += 1;
    }
    chain_blocks(&seed.state, &mut blocks[0..n], &start, &end);
    let mut vals = [[0u8; N]; BATCH];
    let mut j = 0;
    while j < n {
        vals[j] = value(&blocks[j]);
        j += 1;
    }
    let mut lvl: u32 = 1;
    let mut cnt = n / 2;
    while lvl <= z {
        let mut j = 0;
        while j < cnt {
            let idx = (i << (z - lvl)) + j as u32;
            blocks[j] = pair_block(&adrs.with_word2(lvl).with_word3(idx), &vals[2 * j], &vals[2 * j + 1]);
            start[j] = idx;
            end[j] = idx + 1;
            j += 1;
        }
        chain_blocks(&seed.state, &mut blocks[0..cnt], &start, &end);
        let mut j = 0;
        while j < cnt {
            vals[j] = value(&blocks[j]);
            j += 1;
        }
        cnt /= 2;
        lvl += 1;
    }
    vals[0]
}

/// Algorithm 15, `fors_node`: the node at height `z`, index `i`.
pub fn fors_node(sk_seed: &[u8; N], i: u32, z: u32, seed: &Seed, adrs: Adrs) -> [u8; N] {
    if z <= BATCH_HEIGHT {
        fors_batch(sk_seed, i, z, seed, adrs)
    } else {
        let lnode = fors_node(sk_seed, 2 * i, z - 1, seed, adrs);
        let rnode = fors_node(sk_seed, 2 * i + 1, z - 1, seed, adrs);
        hash2(seed, &adrs.with_word2(z).with_word3(i), &lnode, &rnode)
    }
}

/// Algorithm 16, `fors_sign`. `md` holds at least ceil(K·A/8) bytes.
pub fn fors_sign(md: &[u8], sk_seed: &[u8; N], seed: &Seed, adrs: Adrs) -> Vec<u8> {
    let indices = base_2b(md, A, K as usize);
    let mut sig: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < K {
        let idx = indices[i as usize];
        let sk = fors_sk_gen(sk_seed, seed, adrs, (i << A) + idx);
        sig.extend_from_slice(&sk);
        let mut j: u32 = 0;
        while j < A {
            let s = (idx >> j) ^ 1;
            let node = fors_node(sk_seed, (i << (A - j)) + s, j, seed, adrs);
            sig.extend_from_slice(&node);
            j += 1;
        }
        i += 1;
    }
    sig
}

/// Algorithm 17, `fors_pkFromSig`. `sig` holds `K·(1 + A)` blocks.
///
/// The `K` trees are independent, so they are climbed together: the leaves
/// are one step of [`chain_blocks`] on `K` blocks, and so is each level of
/// the authentication paths.
pub fn fors_pk_from_sig(sig: &[u8], md: &[u8], seed: &Seed, adrs: Adrs) -> [u8; N] {
    let indices = base_2b(md, A, K as usize);
    let mut blocks = [[0u8; 64]; K as usize];
    let mut idx = [0u32; K as usize];
    let mut end = [0u32; K as usize];
    let mut i = 0;
    while i < K as usize {
        let leaf = ((i as u32) << A) + indices[i];
        let sk = block(sig, i * (A as usize + 1));
        blocks[i] = short_block(&adrs.with_word2(0).with_word3(leaf), &sk);
        idx[i] = leaf;
        end[i] = leaf + 1;
        i += 1;
    }
    chain_blocks(&seed.state, &mut blocks, &idx, &end);
    let mut vals = [[0u8; N]; K as usize];
    let mut i = 0;
    while i < K as usize {
        vals[i] = value(&blocks[i]);
        i += 1;
    }
    let mut k: u32 = 0;
    while k < A {
        let mut i = 0;
        while i < K as usize {
            let sibling = block(sig, i * (A as usize + 1) + 1 + k as usize);
            let parent = idx[i] >> 1;
            let a = adrs.with_word2(k + 1).with_word3(parent);
            if idx[i] & 1 == 0 {
                blocks[i] = pair_block(&a, &vals[i], &sibling);
            } else {
                blocks[i] = pair_block(&a, &sibling, &vals[i]);
            }
            idx[i] = parent;
            end[i] = parent + 1;
            i += 1;
        }
        chain_blocks(&seed.state, &mut blocks, &idx, &end);
        let mut i = 0;
        while i < K as usize {
            vals[i] = value(&blocks[i]);
            i += 1;
        }
        k += 1;
    }
    let mut roots: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < K as usize {
        roots.extend_from_slice(&vals[i]);
        i += 1;
    }
    let pk_adrs = adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair);
    thash(seed, &pk_adrs, &roots)
}

/// The FORS public key of the key pair at `adrs`, computed from the secret
/// seed alone: the roots of the `K` trees, compressed. It is what
/// [`fors_pk_from_sig`] returns for every signature [`fors_sign`] makes with
/// this key pair, reached by a different computation; the checked signer
/// compares the two.
pub fn fors_pk_gen(sk_seed: &[u8; N], seed: &Seed, adrs: Adrs) -> [u8; N] {
    let mut roots: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < K {
        let root = fors_node(sk_seed, i, A, seed, adrs);
        roots.extend_from_slice(&root);
        i += 1;
    }
    let pk_adrs = adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair);
    thash(seed, &pk_adrs, &roots)
}
