//! WOTS+ one-time signatures (FIPS 205 §5).

use crate::address::{Adrs, WOTS_PK, WOTS_PRF};
use crate::hash::thash;
use crate::params::{LEN, LEN1, LEN2, LG_W, N, W};
use crate::util::{base_2b, block};

/// Algorithm 5, `chain`: apply `F` `s` times starting at step `i`.
pub fn chain(x: [u8; N], i: u32, s: u32, pk_seed: &[u8; N], adrs: Adrs) -> [u8; N] {
    let mut tmp = x;
    let mut j = i;
    let end = i + s;
    while j < end {
        tmp = thash(pk_seed, &adrs.with_word3(j), &tmp);
        j += 1;
    }
    tmp
}

/// The `LEN` base-w digits signed by WOTS+: the message digits followed by
/// the checksum digits (Algorithm 7, lines 1–7).
pub fn wots_digits(m: &[u8; N]) -> Vec<u32> {
    let mut msg = base_2b(m, LG_W, LEN1);
    let mut csum: u32 = 0;
    let mut i = 0;
    while i < LEN1 {
        csum += W - 1 - msg[i];
        i += 1;
    }
    csum <<= 4;
    let cb = [(csum >> 8) as u8, csum as u8];
    let tail = base_2b(&cb, LG_W, LEN2);
    msg.extend_from_slice(&tail);
    msg
}

/// Algorithm 6, `wots_pkGen`.
pub fn wots_pk_gen(sk_seed: &[u8; N], pk_seed: &[u8; N], adrs: Adrs) -> [u8; N] {
    let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let mut tmp: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < LEN as u32 {
        let sk = thash(pk_seed, &sk_adrs.with_word2(i), sk_seed);
        let t = chain(sk, 0, W - 1, pk_seed, adrs.with_word2(i));
        tmp.extend_from_slice(&t);
        i += 1;
    }
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    thash(pk_seed, &pk_adrs, &tmp)
}

/// Algorithm 7, `wots_sign`.
pub fn wots_sign(m: &[u8; N], sk_seed: &[u8; N], pk_seed: &[u8; N], adrs: Adrs) -> Vec<u8> {
    let msg = wots_digits(m);
    let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let mut sig: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < LEN as u32 {
        let sk = thash(pk_seed, &sk_adrs.with_word2(i), sk_seed);
        let t = chain(sk, 0, msg[i as usize], pk_seed, adrs.with_word2(i));
        sig.extend_from_slice(&t);
        i += 1;
    }
    sig
}

/// Algorithm 8, `wots_pkFromSig`. `sig` holds `LEN` blocks of `N` bytes.
pub fn wots_pk_from_sig(sig: &[u8], m: &[u8; N], pk_seed: &[u8; N], adrs: Adrs) -> [u8; N] {
    let msg = wots_digits(m);
    let mut tmp: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < LEN as u32 {
        let d = msg[i as usize];
        let t = chain(block(sig, i as usize), d, W - 1 - d, pk_seed, adrs.with_word2(i));
        tmp.extend_from_slice(&t);
        i += 1;
    }
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    thash(pk_seed, &pk_adrs, &tmp)
}
