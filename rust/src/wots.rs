//! WOTS+ one-time signatures (FIPS 205 §5).

use crate::address::{Adrs, WOTS_PK, WOTS_PRF};
use crate::hash::{short_block, thash, trunc, Seed};
use crate::params::{LEN, LEN1, LEN2, LG_W, N, W};
use crate::sha256::compress_many;
use crate::util::{base_2b, block};

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

/// The `LEN` secret values of a WOTS+ key: `PRF` at every chain address.
pub fn wots_sks(sk_seed: &[u8; N], seed: &Seed, sk_adrs: Adrs) -> [[u8; N]; LEN] {
    let mut blocks = [[0u8; 64]; LEN];
    let mut i = 0;
    while i < LEN {
        blocks[i] = short_block(&sk_adrs.with_word2(i as u32), sk_seed);
        i += 1;
    }
    let mut st = [[0u32; 8]; LEN];
    compress_many(&seed.state, &blocks, &mut st);
    let mut sk = [[0u8; N]; LEN];
    let mut i = 0;
    while i < LEN {
        sk[i] = trunc(&st[i]);
        i += 1;
    }
    sk
}

/// Algorithm 5, `chain`, for all `LEN` chains of a WOTS+ key together:
/// chain `i` is taken from step `start[i]` to step `end[i]` (at most `W − 1`),
/// so `cur[i]` becomes `chain(cur[i], start[i], end[i] − start[i])` with
/// chain address `i`. A chain with `end[i] <= start[i]` is left as it is.
///
/// The chains advance in lockstep. Step `t` of every chain that has a step
/// `t` is one batch of independent `F` calls on single blocks, and the whole
/// batch goes to one [`compress_many`].
pub fn chains(cur: &mut [[u8; N]; LEN], start: &[u32], end: &[u32], seed: &Seed, adrs: Adrs) {
    let mut blocks = [[0u8; 64]; LEN];
    let mut st = [[0u32; 8]; LEN];
    let mut t: u32 = 0;
    while t < W - 1 {
        let mut k = 0;
        let mut i = 0;
        while i < LEN {
            if start[i] <= t && t < end[i] {
                blocks[k] = short_block(&adrs.with_word2(i as u32).with_word3(t), &cur[i]);
                k += 1;
            }
            i += 1;
        }
        compress_many(&seed.state, &blocks[0..k], &mut st);
        let mut k = 0;
        let mut i = 0;
        while i < LEN {
            if start[i] <= t && t < end[i] {
                cur[i] = trunc(&st[k]);
                k += 1;
            }
            i += 1;
        }
        t += 1;
    }
}

/// The concatenation of `LEN` blocks.
fn concat(x: &[[u8; N]; LEN]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < LEN {
        out.extend_from_slice(&x[i]);
        i += 1;
    }
    out
}

/// Algorithm 6, `wots_pkGen`.
pub fn wots_pk_gen(sk_seed: &[u8; N], seed: &Seed, adrs: Adrs) -> [u8; N] {
    let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let mut cur = wots_sks(sk_seed, seed, sk_adrs);
    chains(&mut cur, &[0u32; LEN], &[W - 1; LEN], seed, adrs);
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    thash(seed, &pk_adrs, &concat(&cur))
}

/// Algorithm 7, `wots_sign`.
pub fn wots_sign(m: &[u8; N], sk_seed: &[u8; N], seed: &Seed, adrs: Adrs) -> Vec<u8> {
    let msg = wots_digits(m);
    let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let mut cur = wots_sks(sk_seed, seed, sk_adrs);
    chains(&mut cur, &[0u32; LEN], &msg, seed, adrs);
    concat(&cur)
}

/// Algorithm 8, `wots_pkFromSig`. `sig` holds `LEN` blocks of `N` bytes.
pub fn wots_pk_from_sig(sig: &[u8], m: &[u8; N], seed: &Seed, adrs: Adrs) -> [u8; N] {
    let msg = wots_digits(m);
    let mut cur = [[0u8; N]; LEN];
    let mut i = 0;
    while i < LEN {
        cur[i] = block(sig, i);
        i += 1;
    }
    chains(&mut cur, &msg, &[W - 1; LEN], seed, adrs);
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    thash(seed, &pk_adrs, &concat(&cur))
}
