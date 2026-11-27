//! Interleaved multi-lane SHA-512 compression using Armv8.2 SHA-512 instructions.
use super::hw::arm;
use core::arch::aarch64::*;

/// Two SHA-512 rounds in one lane.
#[cfg_attr(target_feature = "sha3", inline(always))]
#[cfg_attr(not(target_feature = "sha3"), inline, target_feature(enable = "neon,sha3"))]
#[allow(unused_unsafe)]
unsafe fn lane_step<const I: usize>(v: &mut [arm::V; 4], w: &mut [arm::V; 8], k: arm::V) {
    let [ab, cd, ef, gh] = *v;
    let wk = arm::add(w[I % 8], k);
    let t = arm::sha512h(
        arm::add(arm::ext1(wk, wk), gh),
        arm::ext1(ef, gh),
        arm::ext1(cd, ef),
    );
    *v = [arm::sha512h2(t, cd, ab), ab, arm::add(cd, t), ef];
    if I < 32 {
        w[I % 8] = arm::sha512su1(
            arm::sha512su0(w[I % 8], w[(I + 1) % 8]),
            w[(I + 7) % 8],
            arm::ext1(w[(I + 4) % 8], w[(I + 5) % 8]),
        );
    }
}

struct Lane {
    state: [arm::V; 4],
    schedule: [arm::V; 8],
}

#[cfg_attr(target_feature = "sha3", inline(always))]
#[cfg_attr(not(target_feature = "sha3"), inline, target_feature(enable = "neon,sha3"))]
#[allow(unused_unsafe)]
unsafe fn rounds_lanes<const K_LANES: usize>(lanes: &mut [Lane; K_LANES], k_ptr: *const u64) {
    macro_rules! step {
        ($i:expr) => {{
            let k = vld1q_u64(k_ptr.add(2 * $i));
            let mut l = 0;
            while l < K_LANES {
                lane_step::<{ $i }>(&mut lanes[l].state, &mut lanes[l].schedule, k);
                l += 1;
            }
        }};
    }
    macro_rules! group {
        ($i:expr) => {
            step!($i);
            step!($i + 1);
            step!($i + 2);
            step!($i + 3);
        };
    }
    group!(0);
    group!(4);
    group!(8);
    group!(12);
    group!(16);
    group!(20);
    group!(24);
    group!(28);
    group!(32);
    group!(36);
}

/// Out-of-line K-lane single-block SHA-512 compression updating `acc` in place.
/// Keeping the 80-round body out of any outer loop prevents LLVM LICM from
/// hoisting all 40 `K` vectors and spilling active schedule registers.
#[inline(never)]
#[target_feature(enable = "neon,sha3")]
#[allow(unused_unsafe)]
fn compress_block_lanes_in_place<const K_LANES: usize, const L: usize>(
    acc: &mut [[u64; 8]; K_LANES],
    msgs: &[[u8; L]; K_LANES],
    off: usize,
) {
    let k_ptr = core::hint::black_box(super::K.as_ptr());
    let z = vdupq_n_u64(0);
    let mut lanes = core::array::from_fn::<Lane, K_LANES, _>(|l| Lane {
        state: [
            arm::load_words(&acc[l], 0),
            arm::load_words(&acc[l], 2),
            arm::load_words(&acc[l], 4),
            arm::load_words(&acc[l], 6),
        ],
        schedule: load_block(&msgs[l], off),
    });
    let _ = z;
    // SAFETY: target_feature enables neon,sha3.
    unsafe { rounds_lanes::<K_LANES>(&mut lanes, k_ptr) };
    for l in 0..K_LANES {
        add_store_state(&mut acc[l], &lanes[l].state);
    }
}

#[inline(never)]
#[target_feature(enable = "neon,sha3")]
#[allow(unused_unsafe)]
pub(super) fn compress_parents<const N: usize>(
    state: &[u64; 8],
    blocks: &[[u8; 128]; 2],
    out: &mut [[u8; N]],
) {
    let k_ptr = core::hint::black_box(super::K.as_ptr());
    let initial = [
        arm::load_words(state, 0),
        arm::load_words(state, 2),
        arm::load_words(state, 4),
        arm::load_words(state, 6),
    ];
    let mut lanes = [
        Lane { state: initial, schedule: load_block(&blocks[0], 0) },
        Lane { state: initial, schedule: load_block(&blocks[1], 0) },
    ];
    // SAFETY: target_feature enables neon,sha3.
    unsafe { rounds_lanes::<2>(&mut lanes, k_ptr) };
    let initial0 = arm::load_words(state, 0);
    let initial1 = arm::load_words(state, 2);
    store_trunc::<N>(arm::add(initial0, lanes[0].state[0]), arm::add(initial1, lanes[0].state[1]), &mut out[0]);
    store_trunc::<N>(arm::add(initial0, lanes[1].state[0]), arm::add(initial1, lanes[1].state[1]), &mut out[1]);
}

#[inline(always)]
fn parent_block_512<const N: usize>(block: &mut [u8; 128], adrs: crate::address::Adrs, left: &[u8], right: &[u8]) {
    block[..22].copy_from_slice(&adrs.compress());
    block[22..22 + N].copy_from_slice(left);
    block[22 + N..22 + 2 * N].copy_from_slice(right);
    block[22 + 2 * N] = 0x80;
    block[120..].copy_from_slice(&(((150 + 2 * N) * 8) as u64).to_be_bytes());
}

/// Batch SHA-512 internal tree parent hashes in groups of 4 (then 2), returning
/// the number of parent nodes written to `values[..done]`.
pub(crate) fn parents_batch<const N: usize>(
    state: &[u64; 8],
    adrs: crate::address::Adrs,
    first: u32,
    values: &mut [[u8; N]],
    count: usize,
) -> usize {
    if !matches!(N, 24 | 32) || count < 2 || !arm::available() {
        return 0;
    }
    // SAFETY: arm::available() verified neon and sha3 support.
    unsafe { parents_batch_active::<N>(state, adrs, first, values, count) }
}

#[target_feature(enable = "neon,sha3")]
#[allow(unused_unsafe)]
fn parents_batch_active<const N: usize>(
    state: &[u64; 8],
    adrs: crate::address::Adrs,
    first: u32,
    values: &mut [[u8; N]],
    count: usize,
) -> usize {
    let mut j = 0usize;
    while j + 4 <= count {
        let mut blocks = [[0u8; 128]; 4];
        for lane in 0..4 {
            let i = j + lane;
            parent_block_512::<N>(
                &mut blocks[lane],
                adrs.with_word3(first + i as u32),
                &values[2 * i],
                &values[2 * i + 1],
            );
        }
        compress_parents_4_active::<N>(state, &blocks, &mut values[j..j + 4]);
        j += 4;
    }
    if j + 2 <= count {
        let mut blocks = [[0u8; 128]; 2];
        for lane in 0..2 {
            let i = j + lane;
            parent_block_512::<N>(
                &mut blocks[lane],
                adrs.with_word3(first + i as u32),
                &values[2 * i],
                &values[2 * i + 1],
            );
        }
        compress_parents::<N>(state, &blocks, &mut values[j..j + 2]);
        j += 2;
    }
    j
}

/// Batch FORS authentication-path parent hashes in groups of 4 (then 2).
pub(crate) fn path_parents_batch<const N: usize>(
    state: &[u64; 8],
    adrs: crate::address::Adrs,
    values: &mut [[u8; N]],
    indices: &mut [u32],
    sig: &[u8],
    height: usize,
    offset: usize,
) -> usize {
    if !matches!(N, 24 | 32) || values.len() < 2 || !arm::available() {
        return 0;
    }
    // SAFETY: arm::available() verified neon and sha3 support.
    unsafe { path_parents_batch_active::<N>(state, adrs, values, indices, sig, height, offset) }
}

#[target_feature(enable = "neon,sha3")]
#[allow(unused_unsafe)]
fn path_parents_batch_active<const N: usize>(
    state: &[u64; 8],
    adrs: crate::address::Adrs,
    values: &mut [[u8; N]],
    indices: &mut [u32],
    sig: &[u8],
    height: usize,
    offset: usize,
) -> usize {
    let n = values.len();
    let mut j = 0usize;
    while j + 4 <= n {
        let mut blocks = [[0u8; 128]; 4];
        for lane in 0..4 {
            let i = j + lane;
            let pos = indices[i];
            indices[i] >>= 1;
            let start = N * (i * (height + 1) + 1 + offset);
            let sibling = &sig[start..start + N];
            let node = values[i].as_slice();
            let (left, right) = if pos & 1 == 0 { (node, sibling) } else { (sibling, node) };
            parent_block_512::<N>(&mut blocks[lane], adrs.with_word3(indices[i]), left, right);
        }
        compress_parents_4_active::<N>(state, &blocks, &mut values[j..j + 4]);
        j += 4;
    }
    if j + 2 <= n {
        let mut blocks = [[0u8; 128]; 2];
        for lane in 0..2 {
            let i = j + lane;
            let pos = indices[i];
            indices[i] >>= 1;
            let start = N * (i * (height + 1) + 1 + offset);
            let sibling = &sig[start..start + N];
            let node = values[i].as_slice();
            let (left, right) = if pos & 1 == 0 { (node, sibling) } else { (sibling, node) };
            parent_block_512::<N>(&mut blocks[lane], adrs.with_word3(indices[i]), left, right);
        }
        compress_parents::<N>(state, &blocks, &mut values[j..j + 2]);
        j += 2;
    }
    j
}

#[inline(never)]
#[target_feature(enable = "neon,sha3")]
#[allow(unused_unsafe)]
fn compress_parents_4_active<const N: usize>(
    state: &[u64; 8],
    blocks: &[[u8; 128]; 4],
    out: &mut [[u8; N]],
) {
    let k_ptr = core::hint::black_box(super::K.as_ptr());
    let initial = [
        arm::load_words(state, 0),
        arm::load_words(state, 2),
        arm::load_words(state, 4),
        arm::load_words(state, 6),
    ];
    let mut lanes = [
        Lane { state: initial, schedule: load_block(&blocks[0], 0) },
        Lane { state: initial, schedule: load_block(&blocks[1], 0) },
        Lane { state: initial, schedule: load_block(&blocks[2], 0) },
        Lane { state: initial, schedule: load_block(&blocks[3], 0) },
    ];
    // SAFETY: target_feature enables neon,sha3.
    unsafe { rounds_lanes::<4>(&mut lanes, k_ptr) };
    let initial0 = arm::load_words(state, 0);
    let initial1 = arm::load_words(state, 2);
    for l in 0..4 {
        store_trunc::<N>(
            arm::add(initial0, lanes[l].state[0]),
            arm::add(initial1, lanes[l].state[1]),
            &mut out[l],
        );
    }
}

/// Compress four equal-length multi-block padded SHA-512 messages in lockstep,
/// continuing from `state` and writing the first `N` digest bytes of each.
pub(crate) fn compress_multi_4<const N: usize, const L: usize>(
    state: &[u64; 8],
    msgs: &[[u8; L]; 4],
    out: &mut [[u8; N]],
) -> bool {
    if !matches!(N, 24 | 32) || L == 0 || L % 128 != 0 || out.len() < 4 || !arm::available() {
        return false;
    }
    // SAFETY: arm::available() verified neon and sha3 support.
    unsafe { compress_multi_lanes::<4, N, L>(state, msgs, out) };
    true
}

/// Compress two equal-length multi-block padded SHA-512 messages in lockstep,
/// continuing from `state` and writing the first `N` digest bytes of each.
pub(crate) fn compress_multi_2<const N: usize, const L: usize>(
    state: &[u64; 8],
    msgs: &[[u8; L]; 2],
    out: &mut [[u8; N]],
) -> bool {
    if !matches!(N, 24 | 32) || L == 0 || L % 128 != 0 || out.len() < 2 || !arm::available() {
        return false;
    }
    // SAFETY: arm::available() verified neon and sha3 support.
    unsafe { compress_multi_lanes::<2, N, L>(state, msgs, out) };
    true
}

#[target_feature(enable = "neon,sha3")]
#[allow(unused_unsafe)]
fn compress_multi_lanes<const K_LANES: usize, const N: usize, const L: usize>(
    state: &[u64; 8],
    msgs: &[[u8; L]; K_LANES],
    out: &mut [[u8; N]],
) {
    let mut acc = [*state; K_LANES];
    let mut off = 0;
    while off < L {
        compress_block_lanes_in_place::<K_LANES, L>(&mut acc, msgs, off);
        off += 128;
    }
    for l in 0..K_LANES {
        store_trunc::<N>(arm::load_words(&acc[l], 0), arm::load_words(&acc[l], 2), &mut out[l]);
    }
}

/// Compress a single multi-block padded SHA-512 message keeping the state in
/// NEON registers across all blocks, returning the first `N` digest bytes.
pub(crate) fn compress_multi_1<const N: usize>(state: &[u64; 8], msg: &[u8]) -> Option<[u8; N]> {
    if !matches!(N, 24 | 32) || msg.is_empty() || msg.len() % 128 != 0 || !arm::available() {
        return None;
    }
    // SAFETY: arm::available() verified neon and sha3 support.
    Some(unsafe { compress_multi_1_active::<N>(state, msg) })
}

#[target_feature(enable = "neon,sha3")]
#[allow(unused_unsafe)]
fn compress_multi_1_active<const N: usize>(state: &[u64; 8], msg: &[u8]) -> [u8; N] {
    let mut acc = [
        arm::load_words(state, 0),
        arm::load_words(state, 2),
        arm::load_words(state, 4),
        arm::load_words(state, 6),
    ];
    let len = msg.len();
    let mut off = 0;
    while off < len {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        let mut v = acc;
        let mut w = load_block(msg, off);
        macro_rules! step {
            ($i:expr) => {
                // SAFETY: target_feature enables neon,sha3.
                unsafe { lane_step::<{ $i }>(&mut v, &mut w, vld1q_u64(k_ptr.add(2 * $i))) };
            };
        }
        macro_rules! group {
            ($i:expr) => {
                step!($i);
                step!($i + 1);
                step!($i + 2);
                step!($i + 3);
            };
        }
        group!(0);
        group!(4);
        group!(8);
        group!(12);
        group!(16);
        group!(20);
        group!(24);
        group!(28);
        group!(32);
        group!(36);
        acc[0] = arm::add(acc[0], v[0]);
        acc[1] = arm::add(acc[1], v[1]);
        acc[2] = arm::add(acc[2], v[2]);
        acc[3] = arm::add(acc[3], v[3]);
        off += 128;
    }
    let mut out = [0u8; N];
    store_trunc::<N>(acc[0], acc[1], &mut out);
    out
}

#[cfg_attr(target_feature = "sha3", inline(always))]
#[cfg_attr(not(target_feature = "sha3"), inline, target_feature(enable = "neon,sha3"))]
#[allow(unused_unsafe)]
fn add_store_state(acc: &mut [u64; 8], delta: &[arm::V; 4]) {
    unsafe {
        let ptr = acc.as_mut_ptr();
        vst1q_u64(ptr, arm::add(vld1q_u64(ptr), delta[0]));
        vst1q_u64(ptr.add(2), arm::add(vld1q_u64(ptr.add(2)), delta[1]));
        vst1q_u64(ptr.add(4), arm::add(vld1q_u64(ptr.add(4)), delta[2]));
        vst1q_u64(ptr.add(6), arm::add(vld1q_u64(ptr.add(6)), delta[3]));
    }
}

#[cfg_attr(target_feature = "sha3", inline(always))]
#[cfg_attr(not(target_feature = "sha3"), inline, target_feature(enable = "neon,sha3"))]
#[allow(unused_unsafe)]
fn store_trunc<const N: usize>(ab: arm::V, cd: arm::V, out: &mut [u8; N]) {
    unsafe {
        let ab_be = vrev64q_u8(vreinterpretq_u8_u64(ab));
        let cd_be = vrev64q_u8(vreinterpretq_u8_u64(cd));
        vst1q_u8(out.as_mut_ptr(), ab_be);
        if N == 24 {
            vst1_u8(out.as_mut_ptr().add(16), vget_low_u8(cd_be));
        } else {
            vst1q_u8(out.as_mut_ptr().add(16), cd_be);
        }
    }
}

#[cfg_attr(target_feature = "sha3", inline(always))]
#[cfg_attr(not(target_feature = "sha3"), inline, target_feature(enable = "neon,sha3"))]
#[allow(unused_unsafe)]
fn load_block(block: &[u8], off: usize) -> [arm::V; 8] {
    [
        arm::load_be(block, off),
        arm::load_be(block, off + 16),
        arm::load_be(block, off + 32),
        arm::load_be(block, off + 48),
        arm::load_be(block, off + 64),
        arm::load_be(block, off + 80),
        arm::load_be(block, off + 96),
        arm::load_be(block, off + 112),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::trunc512;
    use crate::sha512::{compress_portable, H0};

    fn check_multi<const N: usize, const L: usize>() {
        let mut msgs = [[0u8; L]; 4];
        for lane in 0..4 {
            for i in 0..L {
                msgs[lane][i] = ((lane + 1) * 37 + i * 13 + (i >> 3)) as u8;
            }
        }
        let mut expected = [[0u8; N]; 4];
        for lane in 0..4 {
            let mut st = H0;
            for off in (0..L).step_by(128) {
                st = compress_portable(&st, &msgs[lane], off);
            }
            expected[lane] = trunc512::<N>(&st);
        }
        let mut actual4 = [[0u8; N]; 4];
        assert!(compress_multi_4::<N, L>(&H0, &msgs, &mut actual4));
        assert_eq!(actual4, expected);
        let mut actual2 = [[0u8; N]; 2];
        let p0: &[[u8; L]; 2] = (&msgs[0..2]).try_into().unwrap();
        assert!(compress_multi_2::<N, L>(&H0, p0, &mut actual2));
        assert_eq!(actual2, expected[0..2]);
        assert_eq!(compress_multi_1::<N>(&H0, &msgs[0]).unwrap(), expected[0]);
    }

    #[test]
    fn multi_block_paired_sha512_matches_portable() {
        check_multi::<24, 1280>();
        check_multi::<32, 2304>();
    }
}
