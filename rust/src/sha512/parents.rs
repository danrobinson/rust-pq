//! Batch independent FORS parents using the platform's SHA-512 kernel.
#[cfg(target_arch = "x86_64")]
use super::x86::compress_parents;
use crate::address::Adrs;
#[cfg(target_arch = "x86_64")]
use crate::sha256::x86::avx512_available as available;
#[cfg(target_arch = "x86_64")]
const LANES: usize = 8;
#[cfg(target_arch = "aarch64")]
use super::{hw::arm::available, paired::compress_parents};
#[cfg(target_arch = "aarch64")]
const LANES: usize = 2;

#[inline(always)]
fn parent_block<const N: usize>(block: &mut [u8; 128], adrs: Adrs, left: &[u8], right: &[u8]) {
    // The seeded state has consumed 128 bytes. The address and both children
    // fit in one final block for every SHA-512 parameter set.
    block[..22].copy_from_slice(&adrs.compress());
    block[22..22 + N].copy_from_slice(left);
    block[22 + N..22 + 2 * N].copy_from_slice(right);
    block[22 + 2 * N] = 0x80;
    block[120..].copy_from_slice(&(((150 + 2 * N) * 8) as u64).to_be_bytes());
}

pub(crate) fn parents<const N: usize>(
    state: &[u64; 8],
    adrs: Adrs,
    first: u32,
    values: &mut [[u8; N]],
    count: usize,
) -> usize {
    if !matches!(N, 24 | 32) || count < LANES || !available() {
        return 0;
    }
    // SAFETY: available() checked the CPU and OS features for this kernel.
    unsafe { parents_active(state, adrs, first, values, count) }
}
#[cfg_attr(target_arch = "x86_64", target_feature(enable = "avx512f,avx512bw"))]
#[cfg_attr(target_arch = "aarch64", target_feature(enable = "neon,sha3"))]
fn parents_active<const N: usize>(
    state: &[u64; 8],
    adrs: Adrs,
    first: u32,
    values: &mut [[u8; N]],
    count: usize,
) -> usize {
    let end = count / LANES * LANES;
    for j in (0..end).step_by(LANES) {
        let mut blocks = [[0u8; 128]; LANES];
        for (lane, block) in blocks.iter_mut().enumerate() {
            let i = j + lane;
            parent_block::<N>(
                block,
                adrs.with_word3(first + i as u32),
                &values[2 * i],
                &values[2 * i + 1],
            )
        }
        // SAFETY: available() checked the kernel's CPU and OS features.
        compress_parents(state, &blocks, &mut values[j..j + LANES]);
    }
    end
}

pub(crate) fn path_parents<const N: usize>(
    state: &[u64; 8],
    adrs: Adrs,
    values: &mut [[u8; N]],
    indices: &mut [u32],
    sig: &[u8],
    height: usize,
    offset: usize,
) -> usize {
    if !matches!(N, 24 | 32) || values.len() < LANES || !available() {
        return 0;
    }
    // SAFETY: available() checked the CPU and OS features for this kernel.
    unsafe { path_parents_active(state, adrs, values, indices, sig, height, offset) }
}
#[cfg_attr(target_arch = "x86_64", target_feature(enable = "avx512f,avx512bw"))]
#[cfg_attr(target_arch = "aarch64", target_feature(enable = "neon,sha3"))]
fn path_parents_active<const N: usize>(
    state: &[u64; 8],
    adrs: Adrs,
    values: &mut [[u8; N]],
    indices: &mut [u32],
    sig: &[u8],
    height: usize,
    offset: usize,
) -> usize {
    let end = values.len() / LANES * LANES;
    for j in (0..end).step_by(LANES) {
        let mut blocks = [[0u8; 128]; LANES];
        for (lane, block) in blocks.iter_mut().enumerate() {
            let i = j + lane;
            let position = indices[i];
            indices[i] >>= 1;
            let start = N * (i * (height + 1) + 1 + offset);
            let sibling = &sig[start..start + N];
            let node = values[i].as_slice();
            let (left, right) = if position & 1 == 0 {
                (node, sibling)
            } else {
                (sibling, node)
            };
            parent_block::<N>(block, adrs.with_word3(indices[i]), left, right)
        }
        // SAFETY: available() checked the kernel's CPU and OS features.
        compress_parents(state, &blocks, &mut values[j..j + LANES]);
    }
    end
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::{seed_ctx, thash_pair};

    fn check<const N: usize>() {
        let seed = seed_ctx(&core::array::from_fn::<_, N, _>(|i| (i * 13) as u8));
        let adrs = Adrs::new()
            .with_layer(7)
            .with_tree(0x1122334455667788)
            .with_type(crate::address::FORS_TREE)
            .with_keypair(257)
            .with_word2(8);
        for count in 0..=33 {
            let mut values: [[u8; N]; 66] =
                core::array::from_fn(|i| core::array::from_fn(|j| (i * 31 + j * 11) as u8));
            let mut expected = values;
            let processed = parents(&seed.state512, adrs, 65532, &mut values[..2 * count], count);
            assert_eq!(
                processed,
                if available() {
                    count / LANES * LANES
                } else {
                    0
                }
            );
            for i in 0..processed {
                expected[i] = thash_pair(
                    &seed,
                    &adrs.with_word3(65532 + i as u32),
                    &expected[2 * i],
                    &expected[2 * i + 1],
                );
            }
            assert_eq!(values, expected);
        }
    }

    #[test]
    fn in_place_fors_parent_batches_match_scalar() {
        check::<24>();
        check::<32>();
    }
}
