//! WOTS+ one-time signatures (FIPS 205 §5).

use crate::address::{Adrs, WOTS_PK, WOTS_PRF};
use crate::hash::{thash_f, thash_h};
use crate::params::{Params, LEN2, LG_W, W};
use crate::util::{base_2b, block};

/// Algorithm 5, `chain`: apply `F` `s` times starting at step `i`.
pub fn chain(p: &Params, x: &[u8], i: u32, s: u32, pk_seed: &[u8], adrs: Adrs) -> Vec<u8> {
    let mut tmp: Vec<u8> = Vec::new();
    tmp.extend_from_slice(x);
    let mut j = i;
    let end = i + s;
    while j < end {
        tmp = thash_f(p, pk_seed, &adrs.with_word3(j), &tmp);
        j += 1;
    }
    tmp
}

/// The `len` base-w digits signed by WOTS+: the message digits followed by
/// the checksum digits (Algorithm 7, lines 1–7).
pub fn wots_digits(p: &Params, m: &[u8]) -> Vec<u32> {
    let len1 = p.len1();
    let mut msg = base_2b(m, LG_W, len1);
    let mut csum: u32 = 0;
    let mut i = 0;
    while i < len1 {
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
pub fn wots_pk_gen(p: &Params, sk_seed: &[u8], pk_seed: &[u8], adrs: Adrs) -> Vec<u8> {
    let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let len = p.len() as u32;
    let mut tmp: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < len {
        let sk = thash_f(p, pk_seed, &sk_adrs.with_word2(i), sk_seed);
        let t = chain(p, &sk, 0, W - 1, pk_seed, adrs.with_word2(i));
        tmp.extend_from_slice(&t);
        i += 1;
    }
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    thash_h(p, pk_seed, &pk_adrs, &tmp)
}

/// Algorithm 7, `wots_sign`.
pub fn wots_sign(p: &Params, m: &[u8], sk_seed: &[u8], pk_seed: &[u8], adrs: Adrs) -> Vec<u8> {
    let msg = wots_digits(p, m);
    let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let len = p.len() as u32;
    let mut sig: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < len {
        let sk = thash_f(p, pk_seed, &sk_adrs.with_word2(i), sk_seed);
        let t = chain(p, &sk, 0, msg[i as usize], pk_seed, adrs.with_word2(i));
        sig.extend_from_slice(&t);
        i += 1;
    }
    sig
}

/// Algorithm 8, `wots_pkFromSig`. `sig` holds `len` blocks of `n` bytes.
pub fn wots_pk_from_sig(p: &Params, sig: &[u8], m: &[u8], pk_seed: &[u8], adrs: Adrs) -> Vec<u8> {
    let msg = wots_digits(p, m);
    let len = p.len() as u32;
    let mut tmp: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < len {
        let d = msg[i as usize];
        let x = block(sig, p.n, i as usize);
        let t = chain(p, &x, d, W - 1 - d, pk_seed, adrs.with_word2(i));
        tmp.extend_from_slice(&t);
        i += 1;
    }
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    thash_h(p, pk_seed, &pk_adrs, &tmp)
}
