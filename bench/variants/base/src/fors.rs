//! FORS few-time signatures (FIPS 205 §8).

use crate::address::{Adrs, FORS_PRF, FORS_ROOTS};
use crate::hash::thash;
use crate::params::{A, K, N};
use crate::util::{base_2b, block};
use crate::xmss::{climb, hash2};

/// Algorithm 14, `fors_skGen`.
pub fn fors_sk_gen(sk_seed: &[u8; N], pk_seed: &[u8; N], adrs: Adrs, idx: u32) -> [u8; N] {
    let sk_adrs = adrs.with_type(FORS_PRF).with_keypair(adrs.keypair).with_word3(idx);
    thash(pk_seed, &sk_adrs, sk_seed)
}

/// Algorithm 15, `fors_node`: the node at height `z`, index `i`.
pub fn fors_node(sk_seed: &[u8; N], i: u32, z: u32, pk_seed: &[u8; N], adrs: Adrs) -> [u8; N] {
    if z == 0 {
        let sk = fors_sk_gen(sk_seed, pk_seed, adrs, i);
        thash(pk_seed, &adrs.with_word2(0).with_word3(i), &sk)
    } else {
        let lnode = fors_node(sk_seed, 2 * i, z - 1, pk_seed, adrs);
        let rnode = fors_node(sk_seed, 2 * i + 1, z - 1, pk_seed, adrs);
        hash2(pk_seed, &adrs.with_word2(z).with_word3(i), &lnode, &rnode)
    }
}

/// Algorithm 16, `fors_sign`. `md` holds at least ceil(K·A/8) bytes.
pub fn fors_sign(md: &[u8], sk_seed: &[u8; N], pk_seed: &[u8; N], adrs: Adrs) -> Vec<u8> {
    let indices = base_2b(md, A, K as usize);
    let mut sig: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < K {
        let idx = indices[i as usize];
        let sk = fors_sk_gen(sk_seed, pk_seed, adrs, (i << A) + idx);
        sig.extend_from_slice(&sk);
        let mut j: u32 = 0;
        while j < A {
            let s = (idx >> j) ^ 1;
            let node = fors_node(sk_seed, (i << (A - j)) + s, j, pk_seed, adrs);
            sig.extend_from_slice(&node);
            j += 1;
        }
        i += 1;
    }
    sig
}

/// Algorithm 17, `fors_pkFromSig`. `sig` holds `K·(1 + A)` blocks.
pub fn fors_pk_from_sig(sig: &[u8], md: &[u8], pk_seed: &[u8; N], adrs: Adrs) -> [u8; N] {
    let indices = base_2b(md, A, K as usize);
    let mut roots: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < K {
        let first = (i * (A + 1)) as usize;
        let leaf = (i << A) + indices[i as usize];
        let sk = block(sig, first);
        let node = thash(pk_seed, &adrs.with_word2(0).with_word3(leaf), &sk);
        let root = climb(node, leaf, sig, first + 1, A, pk_seed, adrs);
        roots.extend_from_slice(&root);
        i += 1;
    }
    let pk_adrs = adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair);
    thash(pk_seed, &pk_adrs, &roots)
}
