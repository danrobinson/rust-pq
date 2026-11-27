//! WOTS+ one-time signatures (FIPS 205 §5).
//!
//! The chains of a key are `len = 2n + 3` blocks of [`chain_blocks`]; the
//! block arrays have room for the largest `len` (67, for n = 32) and the
//! first `len` are used.

use alloc::vec::Vec;
use crate::address::{Adrs, WOTS_PK, WOTS_PRF};
use crate::hash::{chain_blocks, short_block, thash_values, Seed};
use crate::params::{LEN2, LEN_MAX, LG_W, W};
use crate::util::{base_2b, block};

/// The `len` base-w digits signed by WOTS+: the message digits followed by
/// the checksum digits (Algorithm 7, lines 1–7).
pub fn wots_digits<const N: usize>(m: &[u8; N]) -> Vec<u32> {
    let len1 = 2 * N;
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

/// The blocks of the `len` chains of a WOTS+ key, each holding its secret
/// value: `PRF` at every chain address, computed in place as one step of
/// [`chain_blocks`] on the `PRF` blocks. A `PRF` block and the chain block
/// for the same chain differ only in the address type (byte 9), which is
/// then switched.
fn sk_blocks<const N: usize>(sk_seed: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> [[u8; 64]; LEN_MAX] {
    let len = 2 * N + LEN2;
    let sk_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let mut blocks = [[0u8; 64]; LEN_MAX];
    let mut i = 0;
    while i < len {
        blocks[i] = short_block(&sk_adrs.with_word2(i as u32), sk_seed);
        i += 1;
    }
    chain_blocks::<N>(&seed.state, &mut blocks[0..len], &[0u32; LEN_MAX], &[1u32; LEN_MAX]);
    let mut i = 0;
    while i < len {
        blocks[i][9] = adrs.typ as u8;
        i += 1;
    }
    blocks
}

/// Algorithm 6, `wots_pkGen`.
pub fn wots_pk_gen<const N: usize>(sk_seed: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    #[cfg(all(feature = "platform-sha2", target_arch = "aarch64", target_endian = "little"))]
    if matches!(N, 16 | 24 | 32) && crate::sha256::arm_wide::available() {
        return arm::pk_gen(sk_seed, seed, adrs);
    }
    let len = 2 * N + LEN2;
    let mut blocks = sk_blocks::<N>(sk_seed, seed, adrs);
    chain_blocks::<N>(&seed.state, &mut blocks[0..len], &[0u32; LEN_MAX], &[W - 1; LEN_MAX]);
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    thash_values::<N>(seed, &pk_adrs, &blocks[0..len])
}

/// Algorithm 7, `wots_sign`.
pub fn wots_sign<const N: usize>(m: &[u8; N], sk_seed: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> Vec<u8> {
    #[cfg(all(feature = "platform-sha2", target_arch = "aarch64", target_endian = "little"))]
    if matches!(N, 16 | 24 | 32) && crate::sha256::arm_wide::available() {
        return arm::sign(m, sk_seed, seed, adrs);
    }
    let len = 2 * N + LEN2;
    let msg = wots_digits::<N>(m);
    let mut blocks = sk_blocks::<N>(sk_seed, seed, adrs);
    chain_blocks::<N>(&seed.state, &mut blocks[0..len], &[0u32; LEN_MAX], &msg);
    let mut sig: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < len {
        sig.extend_from_slice(&blocks[i][22..22 + N]);
        i += 1;
    }
    sig
}

/// Algorithm 8, `wots_pkFromSig`. `sig` holds `len` blocks of `n` bytes.
pub fn wots_pk_from_sig<const N: usize>(sig: &[u8], m: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    #[cfg(all(feature = "platform-sha2", target_arch = "aarch64", target_endian = "little"))]
    if matches!(N, 16 | 24 | 32) && crate::sha256::arm_wide::available() {
        return arm::recover(sig, m, seed, adrs);
    }
    let len = 2 * N + LEN2;
    let msg = wots_digits::<N>(m);
    #[cfg(all(feature = "platform-sha2", target_arch = "x86_64", target_feature = "sse2"))]
    if matches!(N, 16 | 24 | 32) && crate::sha256::x86::avx512_available() {
        return wide::recover(seed, adrs, sig, &msg);
    }
    let mut blocks = [[0u8; 64]; LEN_MAX];
    let mut i = 0;
    while i < len {
        blocks[i] = short_block(&adrs.with_word2(i as u32), &block::<N>(sig, i));
        i += 1;
    }
    chain_blocks::<N>(&seed.state, &mut blocks[0..len], &msg, &[W - 1; LEN_MAX]);
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    thash_values::<N>(seed, &pk_adrs, &blocks[0..len])
}

#[cfg(all(feature = "platform-sha2", target_arch = "x86_64", target_feature = "sse2"))]
mod wide;

#[cfg(all(feature = "platform-sha2", target_arch = "aarch64", target_endian = "little"))]
mod arm;
