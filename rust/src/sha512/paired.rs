//! Interleave two complete SHA-512 compressions using Arm SHA-512 instructions.
use super::hw::arm;

// Two SHA-512 rounds in one lane pair. Inlining exposes both independent chains.
#[inline(always)]
unsafe fn lane_step<const I: usize>(v: &mut [arm::V; 4], w: &mut [arm::V; 8], k: arm::V) {
    unsafe {
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
}

struct Lane {
    state: [arm::V; 4],
    schedule: [arm::V; 8],
}

// Both lanes consume the same two constants.
#[inline(always)]
unsafe fn paired_step<const I: usize>(left: &mut Lane, right: &mut Lane) {
    unsafe {
        let k = arm::load_words(&super::K, 2 * I);
        lane_step::<I>(&mut left.state, &mut left.schedule, k);
        lane_step::<I>(&mut right.state, &mut right.schedule, k);
    }
}

#[inline]
#[target_feature(enable = "neon,sha3")]
pub(super) fn compress_parents<const N: usize>(
    state: &[u64; 8],
    blocks: &[[u8; 128]; 2],
    out: &mut [[u8; N]],
) {
    let initial = [
        arm::load_words(state, 0),
        arm::load_words(state, 2),
        arm::load_words(state, 4),
        arm::load_words(state, 6),
    ];
    let mut left = Lane {
        state: initial,
        schedule: load_block(&blocks[0]),
    };
    let mut right = Lane {
        state: initial,
        schedule: load_block(&blocks[1]),
    };
    macro_rules! step {
        ($i:expr) => {{
            // SAFETY: this kernel runs with Arm SHA-512 enabled.
            unsafe { paired_step::<{ $i }>(&mut left, &mut right) };
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
    store_parent(initial, left.state, &mut out[0]);
    store_parent(initial, right.state, &mut out[1]);
}

#[inline]
#[target_feature(enable = "neon,sha3")]
fn store_parent<const N: usize>(initial: [arm::V; 4], state: [arm::V; 4], out: &mut [u8; N]) {
    let words = arm::store_words(
        arm::add(initial[0], state[0]),
        arm::add(initial[1], state[1]),
    );
    let mut i = 0;
    while i < N / 8 {
        out[8 * i..8 * i + 8].copy_from_slice(&words[i].to_be_bytes());
        i += 1;
    }
}

#[inline]
#[target_feature(enable = "neon,sha3")]
fn load_block(block: &[u8; 128]) -> [arm::V; 8] {
    [
        arm::load_be(block, 0),
        arm::load_be(block, 16),
        arm::load_be(block, 32),
        arm::load_be(block, 48),
        arm::load_be(block, 64),
        arm::load_be(block, 80),
        arm::load_be(block, 96),
        arm::load_be(block, 112),
    ]
}
