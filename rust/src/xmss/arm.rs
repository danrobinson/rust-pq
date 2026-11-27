//! Batched Armv8 SHA-256 / SHA-512 XMSS subtree computation.
use super::*;
use crate::address::WOTS_PK;
use crate::sha256::arm_wide;

/// Compute the XMSS node at `(index, height)` for `1 <= height <= 4` and `N in {16, 24, 32}`
/// using fused 4-lane (or 2-lane for height == 1) WOTS+ keygen, batched multi-block
/// `T_len`, and batched internal tree parent hashing.
pub(super) fn batch_root<const N: usize>(
    sk_seed: &[u8; N],
    index: u32,
    height: u32,
    seed: &Seed<N>,
    adrs: Adrs,
) -> [u8; N] {
    if N == 16 {
        let mut sk16 = [0u8; 16];
        sk16.copy_from_slice(sk_seed);
        let root16 = batch_root_16(&sk16, index, height, &seed.state, adrs);
        let mut out = [0u8; N];
        out.copy_from_slice(&root16);
        out
    } else if N == 24 {
        batch_root_512::<N, 1280>(sk_seed, index, height, seed, adrs)
    } else {
        batch_root_512::<N, 2304>(sk_seed, index, height, seed, adrs)
    }
}

#[inline(always)]
fn prepare_tlen<const L: usize>(m: &mut [u8; L], adrs: Adrs, keypair: u32, size: usize, block: usize) {
    m[..22].copy_from_slice(&adrs.with_type(WOTS_PK).with_keypair(keypair).compress());
    m[size] = 0x80;
    m[L - 2..].copy_from_slice(&(((block + size) * 8) as u16).to_be_bytes());
}

fn batch_root_16(
    sk_seed: &[u8; 16],
    index: u32,
    height: u32,
    state: &[u32; 8],
    adrs: Adrs,
) -> [u8; 16] {
    let first = index << height;
    let count = 1usize << height;
    let size = 22 + (2 * 16 + LEN2) * 16; // 582
    let mut roots = [[0u8; 16]; 16];

    if count == 2 {
        let mut msgs = [[0u8; 640]; 2];
        prepare_tlen(&mut msgs[0], adrs, first, size, 64);
        prepare_tlen(&mut msgs[1], adrs, first + 1, size, 64);
        arm_wide::wots_endpoints_2::<16, 640>(state, sk_seed, adrs, first, &mut msgs);
        arm_wide::compress_multi_2::<640>(state, &msgs, &mut roots[..2]);
    } else {
        let mut chunk = 0usize;
        while chunk < count {
            let base = first + chunk as u32;
            let mut msgs = [[0u8; 640]; 4];
            for l in 0..4 {
                prepare_tlen(&mut msgs[l], adrs, base + l as u32, size, 64);
            }
            arm_wide::wots_endpoints_4::<16, 640>(state, sk_seed, adrs, base, &mut msgs);
            arm_wide::compress_multi_4::<640>(state, &msgs, &mut roots[chunk..chunk + 4]);
            chunk += 4;
        }
    }

    for level in 1..=height {
        let adr = adrs.with_type(TREE).with_word2(level);
        arm_wide::parents_16(state, adr, first >> level, &mut roots, count >> level);
    }
    roots[0]
}

fn batch_root_512<const N: usize, const L: usize>(
    sk_seed: &[u8; N],
    index: u32,
    height: u32,
    seed: &Seed<N>,
    adrs: Adrs,
) -> [u8; N] {
    let first = index << height;
    let count = 1usize << height;
    let size = 22 + (2 * N + LEN2) * N;
    let mut roots = [[0u8; N]; 16];

    if count == 2 {
        let mut msgs = [[0u8; L]; 2];
        prepare_tlen(&mut msgs[0], adrs, first, size, 128);
        prepare_tlen(&mut msgs[1], adrs, first + 1, size, 128);
        arm_wide::wots_endpoints_2::<N, L>(&seed.state, sk_seed, adrs, first, &mut msgs);
        compress_tlen_pair::<N, L>(&seed.state512, &msgs, &mut roots[..2]);
    } else {
        let mut chunk = 0usize;
        while chunk < count {
            let base = first + chunk as u32;
            let mut msgs = [[0u8; L]; 4];
            for l in 0..4 {
                prepare_tlen(&mut msgs[l], adrs, base + l as u32, size, 128);
            }
            arm_wide::wots_endpoints_4::<N, L>(&seed.state, sk_seed, adrs, base, &mut msgs);
            compress_tlen_quad::<N, L>(&seed.state512, &msgs, &mut roots[chunk..chunk + 4]);
            chunk += 4;
        }
    }

    for level in 1..=height {
        let adr = adrs.with_type(TREE).with_word2(level);
        let level_first = first >> level;
        let level_count = count >> level;
        let done = crate::sha512::paired::parents_batch(&seed.state512, adr, level_first, &mut roots, level_count);
        for j in done..level_count {
            roots[j] = hash2(
                seed,
                &adr.with_word3(level_first + j as u32),
                &roots[2 * j],
                &roots[2 * j + 1],
            );
        }
    }
    roots[0]
}

#[inline]
fn compress_tlen_quad<const N: usize, const L: usize>(
    state512: &[u64; 8],
    msgs: &[[u8; L]; 4],
    out: &mut [[u8; N]],
) {
    if !crate::sha512::paired::compress_multi_4::<N, L>(state512, msgs, out) {
        for lane in 0..4 {
            let mut st = *state512;
            let mut off = 0;
            while off < L {
                st = crate::sha512::compress(&st, &msgs[lane], off);
                off += 128;
            }
            out[lane] = crate::hash::trunc512::<N>(&st);
        }
    }
}

#[inline]
fn compress_tlen_pair<const N: usize, const L: usize>(
    state512: &[u64; 8],
    msgs: &[[u8; L]; 2],
    out: &mut [[u8; N]],
) {
    if !crate::sha512::paired::compress_multi_2::<N, L>(state512, msgs, out) {
        for lane in 0..2 {
            let mut st = *state512;
            let mut off = 0;
            while off < L {
                st = crate::sha512::compress(&st, &msgs[lane], off);
                off += 128;
            }
            out[lane] = crate::hash::trunc512::<N>(&st);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::{chain_blocks_portable, seed_ctx, short_block, thash_values};

    fn ref_wots_pk<const N: usize>(sk_seed: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
        let len = 2 * N + LEN2;
        let sk_adrs = adrs.with_type(crate::address::WOTS_PRF).with_keypair(adrs.keypair);
        let mut blocks = [[0u8; 64]; crate::params::LEN_MAX];
        for i in 0..len {
            blocks[i] = short_block(&sk_adrs.with_word2(i as u32), sk_seed);
        }
        chain_blocks_portable::<N>(&seed.state, &mut blocks[..len], &[0; crate::params::LEN_MAX], &[1; crate::params::LEN_MAX]);
        for i in 0..len {
            blocks[i][9] = adrs.typ as u8;
        }
        chain_blocks_portable::<N>(&seed.state, &mut blocks[..len], &[0; crate::params::LEN_MAX], &[15; crate::params::LEN_MAX]);
        thash_values::<N>(seed, &adrs.with_type(WOTS_PK).with_keypair(adrs.keypair), &blocks[..len])
    }

    fn ref_node<const N: usize>(sk_seed: &[u8; N], i: u32, z: u32, seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
        if z == 0 {
            ref_wots_pk(sk_seed, seed, adrs.with_type(WOTS_HASH).with_keypair(i))
        } else {
            let l = ref_node(sk_seed, 2 * i, z - 1, seed, adrs);
            let r = ref_node(sk_seed, 2 * i + 1, z - 1, seed, adrs);
            hash2(seed, &adrs.with_type(TREE).with_word2(z).with_word3(i), &l, &r)
        }
    }

    fn check<const N: usize>() {
        if !arm_wide::available() {
            return;
        }
        let sk: [u8; N] = core::array::from_fn(|i| (i * 19 + 3) as u8);
        let seed = seed_ctx(&core::array::from_fn(|i| (i * 7 + 11) as u8));
        let adrs = Adrs::new().with_layer(3).with_tree(0x0123456789abcdef);
        for z in 0..=3 {
            let idx = 3;
            assert_eq!(xmss_node(&sk, idx, z, &seed, adrs), ref_node(&sk, idx, z, &seed, adrs));
        }
    }

    #[test]
    fn arm_xmss_subtrees_match_portable() {
        check::<16>();
        check::<24>();
        check::<32>();
    }
}
