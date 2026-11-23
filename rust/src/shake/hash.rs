//! SHAKE256 hash functions of FIPS 205 §11.1.
use crate::address::Adrs;
use crate::params::Params;
use crate::shake256::Sponge;
use alloc::vec::Vec;

pub type Seed<const N: usize> = [u8; N];

pub fn seed_ctx<const N: usize>(pk_seed: &[u8; N]) -> Seed<N> {
    *pk_seed
}

pub(super) fn start<const N: usize>(seed: &Seed<N>, adrs: &Adrs) -> Sponge {
    let mut sponge = Sponge::new();
    sponge.absorb(seed);
    sponge.absorb(&adrs.full());
    sponge
}

pub(super) fn digest<const N: usize>(sponge: Sponge) -> [u8; N] {
    let mut out = [0; N];
    sponge.finish(&mut out);
    out
}

pub(super) fn thash<const N: usize>(seed: &Seed<N>, adrs: &Adrs, value: &[u8; N]) -> [u8; N] {
    let mut sponge = start(seed, adrs);
    sponge.absorb(value);
    digest(sponge)
}

pub(super) fn thash_pair<const N: usize>(
    seed: &Seed<N>,
    adrs: &Adrs,
    a: &[u8; N],
    b: &[u8; N],
) -> [u8; N] {
    let mut sponge = start(seed, adrs);
    sponge.absorb(a);
    sponge.absorb(b);
    digest(sponge)
}

pub(super) fn prf_msg<const N: usize>(sk_prf: &[u8; N], opt_rand: &[u8; N], msg: &[u8]) -> [u8; N] {
    let mut sponge = Sponge::new();
    sponge.absorb(sk_prf);
    sponge.absorb(opt_rand);
    sponge.absorb(msg);
    digest(sponge)
}

pub(super) fn h_msg<const N: usize>(
    p: &Params,
    r: &[u8; N],
    pk_seed: &[u8; N],
    pk_root: &[u8; N],
    msg: &[u8],
) -> Vec<u8> {
    let mut sponge = Sponge::new();
    sponge.absorb(r);
    sponge.absorb(pk_seed);
    sponge.absorb(pk_root);
    sponge.absorb(msg);
    let mut out = alloc::vec![0; p.m];
    sponge.finish(&mut out);
    out
}
