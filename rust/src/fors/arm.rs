//! Fused Armv8 SHA-256 FORS leaf generation, subtree reduction, and verification.
use super::*;
use crate::sha256::arm_wide;

/// Compute the FORS subtree root at `(index, height)` (`height <= BATCH_HEIGHT`)
/// using fused 4-lane PRF + `F` leaf generation and batched parent hashing.
pub(super) fn subtree<const N: usize>(
    sk_seed: &[u8; N],
    index: u32,
    height: u32,
    seed: &Seed<N>,
    adrs: Adrs,
) -> [u8; N] {
    let n = 1usize << height;
    if N == 16 {
        let mut sk16 = [0u8; 16];
        sk16.copy_from_slice(sk_seed);
        let mut nodes = [[0u8; 16]; BATCH];
        arm_wide::fors_leaves::<16>(&seed.state, &sk16, adrs, index << height, &mut nodes[..n]);
        for level in 1..=height {
            let first = index << (height - level);
            let adr = adrs.with_word2(level);
            arm_wide::parents_16(&seed.state, adr, first, &mut nodes, n >> level);
        }
        let mut out = [0u8; N];
        out.copy_from_slice(&nodes[0]);
        out
    } else {
        let mut nodes = [[0u8; N]; BATCH];
        arm_wide::fors_leaves::<N>(&seed.state, sk_seed, adrs, index << height, &mut nodes[..n]);
        for level in 1..=height {
            let first = index << (height - level);
            let adr = adrs.with_word2(level);
            let count = n >> level;
            let done = crate::sha512::paired::parents_batch(&seed.state512, adr, first, &mut nodes, count);
            for j in done..count {
                nodes[j] = thash_pair(
                    seed,
                    &adr.with_word3(first + j as u32),
                    &nodes[2 * j],
                    &nodes[2 * j + 1],
                );
            }
        }
        nodes[0]
    }
}

/// Decode `k` `a`-bit big-endian indices from `md` directly onto the stack.
#[inline]
fn base_2b_stack(md: &[u8], b: u32, out_len: usize) -> [u32; K_MAX] {
    let mut out = [0u32; K_MAX];
    let mut inp = 0usize;
    let mut bits: u32 = 0;
    let mut total: u32 = 0;
    let mask = (1u32 << b) - 1;
    let mut i = 0usize;
    while i < out_len {
        while bits < b {
            total = (total << 8) + md[inp] as u32;
            inp += 1;
            bits += 8;
        }
        bits -= b;
        out[i] = (total >> bits) & mask;
        i += 1;
    }
    out
}

/// Armv8 accelerated `fors_pkFromSig` with zero heap allocations and 4-lane
/// lockstep SHA-256 leaves & paths (N = 16) / paired SHA-512 paths (N = 24, 32).
pub(super) fn pk_from_sig<const N: usize>(
    p: &Params,
    sig: &[u8],
    md: &[u8],
    seed: &Seed<N>,
    adrs: Adrs,
) -> [u8; N] {
    let a = p.a;
    let k = p.k as usize;
    let raw = base_2b_stack(md, a, k);
    let mut idx = [0u32; K_MAX];
    for i in 0..k {
        idx[i] = ((i as u32) << a) + raw[i];
    }

    let pk_adrs = adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair);
    if N == 16 {
        let mut vals = [[0u8; 16]; K_MAX];
        arm_wide::fors_verify_leaves::<16>(&seed.state, adrs, sig, &idx[..k], &mut vals[..k], a as usize);
        for h in 0..a as usize {
            arm_wide::fors_path_level_16(&seed.state, adrs, sig, &mut idx[..k], &mut vals[..k], a as usize, h);
        }
        // Stack-allocated T_k (max k=33 for N=16 -> 22 + 33*16 = 550 bytes <= 576 bytes).
        let mut buf = [0u8; 640];
        let size = 22 + k * 16;
        buf[..22].copy_from_slice(&pk_adrs.compress());
        for i in 0..k {
            buf[22 + 16 * i..22 + 16 * (i + 1)].copy_from_slice(&vals[i]);
        }
        buf[size] = 0x80;
        let total = (size + 9 + 63) / 64 * 64;
        buf[total - 2..total].copy_from_slice(&(((64 + size) * 8) as u16).to_be_bytes());
        let d = arm_wide::compress_multi_1(&seed.state, &buf[..total]);
        let mut out = [0u8; N];
        out.copy_from_slice(&d);
        out
    } else {
        let mut vals = [[0u8; N]; K_MAX];
        arm_wide::fors_verify_leaves::<N>(&seed.state, adrs, sig, &idx[..k], &mut vals[..k], a as usize);
        for h in 0..a as usize {
            let adr = adrs.with_word2(h as u32 + 1);
            let done = crate::sha512::paired::path_parents_batch(
                &seed.state512,
                adr,
                &mut vals[..k],
                &mut idx[..k],
                sig,
                a as usize,
                h,
            );
            for i in done..k {
                let sibling = block::<N>(sig, i * (a as usize + 1) + 1 + h);
                let parent = idx[i] >> 1;
                let a_node = adr.with_word3(parent);
                if idx[i] & 1 == 0 {
                    vals[i] = thash_pair::<N>(seed, &a_node, &vals[i], &sibling);
                } else {
                    vals[i] = thash_pair::<N>(seed, &a_node, &sibling, &vals[i]);
                }
                idx[i] = parent;
            }
        }
        // Stack-allocated T_k (max k=35, N=32 -> 22 + 35*32 = 1142 bytes <= 1280 bytes).
        let mut buf = [0u8; 1280];
        let size = 22 + k * N;
        buf[..22].copy_from_slice(&pk_adrs.compress());
        for i in 0..k {
            buf[22 + N * i..22 + N * (i + 1)].copy_from_slice(&vals[i]);
        }
        buf[size] = 0x80;
        let total = (size + 17 + 127) / 128 * 128;
        buf[total - 2..total].copy_from_slice(&(((128 + size) * 8) as u16).to_be_bytes());
        if let Some(out) = crate::sha512::paired::compress_multi_1::<N>(&seed.state512, &buf[..total]) {
            return out;
        }
        let mut st = seed.state512;
        let mut off = 0;
        while off < total {
            st = crate::sha512::compress(&st, &buf, off);
            off += 128;
        }
        crate::hash::trunc512::<N>(&st)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::address::FORS_TREE;
    use crate::hash::{seed_ctx, thash_pair, thash_short};

    fn ref_fors_node<const N: usize>(sk_seed: &[u8; N], i: u32, z: u32, seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
        if z == 0 {
            let sk = thash_short(seed, &adrs.with_type(FORS_PRF).with_keypair(adrs.keypair).with_word3(i), sk_seed);
            thash_short(seed, &adrs.with_word2(0).with_word3(i), &sk)
        } else {
            let l = ref_fors_node(sk_seed, 2 * i, z - 1, seed, adrs);
            let r = ref_fors_node(sk_seed, 2 * i + 1, z - 1, seed, adrs);
            thash_pair(seed, &adrs.with_word2(z).with_word3(i), &l, &r)
        }
    }

    fn check<const N: usize>() {
        if !arm_wide::available() {
            return;
        }
        let sk: [u8; N] = core::array::from_fn(|i| (i * 23 + 5) as u8);
        let seed = seed_ctx(&core::array::from_fn(|i| (i * 11 + 7) as u8));
        let adrs = Adrs::new().with_layer(0).with_tree(0xabcdef0123456789).with_type(FORS_TREE).with_keypair(42);
        for z in 0..=4 {
            assert_eq!(subtree(&sk, 5, z, &seed, adrs), ref_fors_node(&sk, 5, z, &seed, adrs));
        }
    }

    #[test]
    fn arm_fors_subtrees_match_portable() {
        check::<16>();
        check::<24>();
        check::<32>();
    }
}
