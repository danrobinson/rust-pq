//! Batch consecutive WOTS keys across leaf boundaries to fill all 16 SHA-256 lanes.
use super::*;
pub(super) fn batch_root<const N: usize>(
    sk_seed: &[u8; N],
    index: u32,
    height: u32,
    seed: &Seed<N>,
    adrs: Adrs,
) -> [u8; N] {
    let first = index << height;
    let count = 1usize << height;
    let mut roots = [[0u8; N]; 16];
    if N == 16 {
        keys::<N, 16, 640>(seed, sk_seed, adrs, first, &mut roots[..count]);
    } else if N == 24 {
        keys::<N, 8, 1280>(seed, sk_seed, adrs, first, &mut roots[..count]);
    } else {
        keys::<N, 8, 2304>(seed, sk_seed, adrs, first, &mut roots[..count]);
    }
    for level in 1..=height {
        let adr = adrs.with_type(TREE).with_word2(level);
        for j in 0..count >> level {
            roots[j] = hash2(
                seed,
                &adr.with_word3((first >> level) + j as u32),
                &roots[2 * j],
                &roots[2 * j + 1],
            );
        }
    }
    roots[0]
}

fn keys<const N: usize, const G: usize, const L: usize>(
    seed: &Seed<N>,
    sk_seed: &[u8; N],
    adrs: Adrs,
    first: u32,
    roots: &mut [[u8; N]],
) {
    let len = 2 * N + LEN2;
    for (group, keys) in roots.chunks_mut(G).enumerate() {
        let first = first + (group * G) as u32;
        let mut messages = [[0u8; L]; G];
        let size = 22 + len * N;
        let block = if N == 16 { 64 } else { 128 };
        for (i, m) in messages.iter_mut().enumerate() {
            prepare_message(m, adrs, first + i as u32, size, block);
        }
        crate::sha256::x86::wots_endpoints(
            &seed.state,
            sk_seed,
            adrs,
            first,
            &mut messages[..keys.len()],
        );
        if N == 16 {
            crate::sha256::x86::key_digests(&seed.state, &messages[..keys.len()], keys);
        } else {
            crate::sha512::x86::key_digests(&seed.state512, &messages[..keys.len()], keys);
        }
    }
}

#[inline(always)]
fn prepare_message<const L: usize>(
    m: &mut [u8; L],
    adrs: Adrs,
    keypair: u32,
    size: usize,
    block: usize,
) {
    use crate::address::WOTS_PK;
    m[..22].copy_from_slice(&adrs.with_type(WOTS_PK).with_keypair(keypair).compress());
    m[size] = 0x80;
    m[L - 2..].copy_from_slice(&(((block + size) * 8) as u16).to_be_bytes());
}
