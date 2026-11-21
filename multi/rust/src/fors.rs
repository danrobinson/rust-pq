//! FORS few-time signatures (FIPS 205 §8).

use crate::address::{Adrs, FORS_PRF, FORS_ROOTS};
use crate::hash::{thash_f, thash_h};
use crate::params::Params;
use crate::util::{base_2b, block};
use crate::xmss::{climb, hash2};

/// Algorithm 14, `fors_skGen`.
pub fn fors_sk_gen(p: &Params, sk_seed: &[u8], pk_seed: &[u8], adrs: Adrs, idx: u32) -> Vec<u8> {
    let sk_adrs = adrs.with_type(FORS_PRF).with_keypair(adrs.keypair).with_word3(idx);
    thash_f(p, pk_seed, &sk_adrs, sk_seed)
}

/// Algorithm 15, `fors_node`: the node at height `z`, index `i`.
pub fn fors_node(p: &Params, sk_seed: &[u8], i: u32, z: u32, pk_seed: &[u8], adrs: Adrs) -> Vec<u8> {
    if z == 0 {
        let sk = fors_sk_gen(p, sk_seed, pk_seed, adrs, i);
        thash_f(p, pk_seed, &adrs.with_word2(0).with_word3(i), &sk)
    } else {
        let lnode = fors_node(p, sk_seed, 2 * i, z - 1, pk_seed, adrs);
        let rnode = fors_node(p, sk_seed, 2 * i + 1, z - 1, pk_seed, adrs);
        hash2(p, pk_seed, &adrs.with_word2(z).with_word3(i), &lnode, &rnode)
    }
}

/// Algorithm 16, `fors_sign`. `md` holds at least ceil(k·a/8) bytes.
pub fn fors_sign(p: &Params, md: &[u8], sk_seed: &[u8], pk_seed: &[u8], adrs: Adrs) -> Vec<u8> {
    let a = p.a;
    let indices = base_2b(md, a, p.k as usize);
    let mut sig: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < p.k {
        let idx = indices[i as usize];
        let sk = fors_sk_gen(p, sk_seed, pk_seed, adrs, (i << a) + idx);
        sig.extend_from_slice(&sk);
        let mut j: u32 = 0;
        while j < a {
            let s = (idx >> j) ^ 1;
            let node = fors_node(p, sk_seed, (i << (a - j)) + s, j, pk_seed, adrs);
            sig.extend_from_slice(&node);
            j += 1;
        }
        i += 1;
    }
    sig
}

/// Algorithm 17, `fors_pkFromSig`. `sig` holds `k·(1 + a)` blocks.
pub fn fors_pk_from_sig(p: &Params, sig: &[u8], md: &[u8], pk_seed: &[u8], adrs: Adrs) -> Vec<u8> {
    let a = p.a;
    let indices = base_2b(md, a, p.k as usize);
    let mut roots: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < p.k {
        let first = (i * (a + 1)) as usize;
        let leaf = (i << a) + indices[i as usize];
        let sk = block(sig, p.n, first);
        let node = thash_f(p, pk_seed, &adrs.with_word2(0).with_word3(leaf), &sk);
        let root = climb(p, node, leaf, sig, first + 1, a, pk_seed, adrs);
        roots.extend_from_slice(&root);
        i += 1;
    }
    let pk_adrs = adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair);
    thash_h(p, pk_seed, &pk_adrs, &roots)
}
