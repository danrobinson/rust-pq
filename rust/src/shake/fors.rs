//! FORS with SHAKE256, FIPS 205 Algorithms 14–17.
use super::hash::{digest, start, thash, thash_pair, Seed};
use super::xmss::climb;
use crate::address::{Adrs, FORS_PRF, FORS_ROOTS};
use crate::params::Params;
use crate::util::{base_2b, block};
use alloc::vec::Vec;

pub(super) fn fors_sk_gen<const N: usize>(sk: &[u8; N], seed: &Seed<N>, adrs: Adrs, idx: u32) -> [u8; N] {
    let a = adrs
        .with_type(FORS_PRF)
        .with_keypair(adrs.keypair)
        .with_word3(idx);
    thash(seed, &a, sk)
}

pub(super) fn fors_node<const N: usize>(sk: &[u8; N], i: u32, z: u32, seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    let a = adrs.with_word2(z).with_word3(i);
    if z == 0 {
        thash(seed, &a, &fors_sk_gen(sk, seed, adrs, i))
    } else {
        let left = fors_node(sk, 2 * i, z - 1, seed, adrs);
        let right = fors_node(sk, 2 * i + 1, z - 1, seed, adrs);
        thash_pair(seed, &a, &left, &right)
    }
}

/// Algorithm 16, `fors_sign`. `md` holds at least ceil(k·a/8) bytes.
pub fn fors_sign<const N: usize>(
    p: &Params,
    md: &[u8],
    sk_seed: &[u8; N],
    seed: &Seed<N>,
    adrs: Adrs,
) -> Vec<u8> {
    let a = p.a;
    let indices = base_2b(md, a, p.k as usize);
    #[cfg(all(feature = "platform-sha2", any(all(target_arch = "aarch64", target_endian = "little"), all(target_arch = "x86_64", target_feature = "sse2"))))]
    if super::batch::available::<N>() { return super::fors_batch::sign(p, &indices, sk_seed, seed, adrs); }
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

pub(super) fn fors_pk_from_sig<const N: usize>(
    p: &Params,
    sig: &[u8],
    md: &[u8],
    seed: &Seed<N>,
    adrs: Adrs,
) -> [u8; N] {
    let indices = base_2b(md, p.a, p.k as usize);
    #[cfg(all(feature = "platform-sha2", any(all(target_arch = "aarch64", target_endian = "little"), all(target_arch = "x86_64", target_feature = "sse2"))))]
    if super::batch::available::<N>() { return super::fors_batch::recover(p, &indices, sig, seed, adrs); }
    let mut roots = start(seed, &adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair));
    let mut i = 0;
    while i < indices.len() {
        let offset = i * (1 + p.a as usize);
        let idx = ((i as u32) << p.a) + indices[i];
        let value = thash(
            seed,
            &adrs.with_word2(0).with_word3(idx),
            &block(sig, offset),
        );
        let root = climb(value, idx, sig, offset + 1, p.a, seed, adrs);
        roots.absorb(&root);
        i += 1;
    }
    digest(roots)
}
