//! WOTS+ with SHAKE256, FIPS 205 Algorithms 5–8.
use super::hash::{digest, start, thash, Seed};
use crate::address::{Adrs, WOTS_PK, WOTS_PRF};
use crate::params::{LEN2, W};
use crate::util::block;
use crate::wots::wots_digits;
use alloc::vec::Vec;

fn secret<const N: usize>(sk: &[u8; N], seed: &Seed<N>, adrs: Adrs, i: usize) -> [u8; N] {
    let a = adrs
        .with_type(WOTS_PRF)
        .with_keypair(adrs.keypair)
        .with_word2(i as u32);
    thash(seed, &a, sk)
}

fn chain<const N: usize>(
    mut value: [u8; N],
    seed: &Seed<N>,
    adrs: Adrs,
    mut j: u32,
    end: u32,
) -> [u8; N] {
    while j < end {
        value = thash(seed, &adrs.with_word3(j), &value);
        j += 1;
    }
    value
}

pub(super) fn wots_pk_gen<const N: usize>(sk: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    let mut pk = start(seed, &adrs.with_type(WOTS_PK).with_keypair(adrs.keypair));
    let mut i = 0;
    while i < 2 * N + LEN2 {
        let end = chain(
            secret(sk, seed, adrs, i),
            seed,
            adrs.with_word2(i as u32),
            0,
            W - 1,
        );
        pk.absorb(&end);
        i += 1;
    }
    digest(pk)
}

pub(super) fn wots_sign<const N: usize>(
    msg: &[u8; N],
    sk: &[u8; N],
    seed: &Seed<N>,
    adrs: Adrs,
) -> Vec<u8> {
    let digits = wots_digits(msg);
    let mut sig = Vec::new();
    let mut i = 0;
    while i < digits.len() {
        let value = chain(
            secret(sk, seed, adrs, i),
            seed,
            adrs.with_word2(i as u32),
            0,
            digits[i],
        );
        sig.extend_from_slice(&value);
        i += 1;
    }
    sig
}

pub(super) fn wots_pk_from_sig<const N: usize>(
    sig: &[u8],
    msg: &[u8; N],
    seed: &Seed<N>,
    adrs: Adrs,
) -> [u8; N] {
    let digits = wots_digits(msg);
    let mut pk = start(seed, &adrs.with_type(WOTS_PK).with_keypair(adrs.keypair));
    let mut i = 0;
    while i < digits.len() {
        let end = chain(
            block::<N>(sig, i),
            seed,
            adrs.with_word2(i as u32),
            digits[i],
            W - 1,
        );
        pk.absorb(&end);
        i += 1;
    }
    digest(pk)
}
