//! WOTS+ one-time signatures (FIPS 205 §5).

use crate::address::{Adrs, WOTS_PK, WOTS_PRF};
use crate::hash::{chain_blocks, short_block, thash_values, Seed};
use crate::params::{LEN, LEN1, LEN2, LG_W, N, W};
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

/// The blocks of the `LEN` chains of a WOTS+ key, each holding its secret
/// value: `PRF` at every chain address, computed in place as one step of
/// [`chain_blocks`] on the `PRF` blocks. A `PRF` block and the chain block
/// for the same chain differ only in the address type (byte 9), which is
/// then switched.
fn sk_blocks(sk_seed: &[u8; N], seed: &Seed, adrs: Adrs) -> [[u8; 64]; LEN] {
    let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let mut blocks = [[0u8; 64]; LEN];
    let mut i = 0;
    while i < LEN {
        blocks[i] = short_block(&sk_adrs.with_word2(i as u32), sk_seed);
        i += 1;
    }
    chain_blocks(&seed.state, &mut blocks, &[0u32; LEN], &[1u32; LEN]);
    let mut i = 0;
    while i < LEN {
        blocks[i][9] = adrs.typ as u8;
        i += 1;
    }
    blocks
}

/// Algorithm 6, `wots_pkGen`.
pub fn wots_pk_gen(sk_seed: &[u8; N], seed: &Seed, adrs: Adrs) -> [u8; N] {
    let mut blocks = sk_blocks(sk_seed, seed, adrs);
    chain_blocks(&seed.state, &mut blocks, &[0u32; LEN], &[W - 1; LEN]);
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    thash_values(seed, &pk_adrs, &blocks)
}

/// Algorithm 7, `wots_sign`.
pub fn wots_sign(m: &[u8; N], sk_seed: &[u8; N], seed: &Seed, adrs: Adrs) -> Vec<u8> {
    let msg = wots_digits(m);
    let mut blocks = sk_blocks(sk_seed, seed, adrs);
    chain_blocks(&seed.state, &mut blocks, &[0u32; LEN], &msg);
    let mut sig: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < LEN {
        sig.extend_from_slice(&blocks[i][22..38]);
        i += 1;
    }
    sig
}

/// Algorithm 8, `wots_pkFromSig`. `sig` holds `LEN` blocks of `N` bytes.
pub fn wots_pk_from_sig(sig: &[u8], m: &[u8; N], seed: &Seed, adrs: Adrs) -> [u8; N] {
    let msg = wots_digits(m);
    let mut blocks = [[0u8; 64]; LEN];
    let mut i = 0;
    while i < LEN {
        blocks[i] = short_block(&adrs.with_word2(i as u32), &block(sig, i));
        i += 1;
    }
    chain_blocks(&seed.state, &mut blocks, &msg, &[W - 1; LEN]);
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    thash_values(seed, &pk_adrs, &blocks)
}
