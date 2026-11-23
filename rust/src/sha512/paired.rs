//! Interleave two complete SHA-512 compressions using Arm SHA-512 instructions.
use super::hw::arm;

#[inline]
#[target_feature(enable = "neon,sha3")]
pub(super) fn compress_parents<const N: usize>(
    state: &[u64; 8],
    blocks: &[[u8; 128]; 2],
    out: &mut [[u8; N]],
) {
    let initial: [arm::V; 4] = core::array::from_fn(|i| arm::load_words(state, 2 * i));
    let mut v = [initial; 2];
    let mut m: [[arm::V; 8]; 2] =
        core::array::from_fn(|l| core::array::from_fn(|i| arm::load_be(&blocks[l], 16 * i)));
    macro_rules! step {
        ($i:expr) => {{
            const I: usize = $i;
            let k = arm::load_words(&super::K, 2 * I);
            for l in 0..2 {
                let [ab, cd, ef, gh] = v[l];
                let w = &mut m[l];
                let wk = arm::add(w[I % 8], k);
                let t = arm::sha512h(
                    arm::add(arm::ext1(wk, wk), gh),
                    arm::ext1(ef, gh),
                    arm::ext1(cd, ef),
                );
                v[l] = [arm::sha512h2(t, cd, ab), ab, arm::add(cd, t), ef];
                if I < 32 {
                    w[I % 8] = arm::sha512su1(
                        arm::sha512su0(w[I % 8], w[(I + 1) % 8]),
                        w[(I + 7) % 8],
                        arm::ext1(w[(I + 4) % 8], w[(I + 5) % 8]),
                    );
                }
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
    for l in 0..2 {
        let words = arm::store_words(arm::add(initial[0], v[l][0]), arm::add(initial[1], v[l][1]));
        for i in 0..N / 8 {
            out[l][8 * i..8 * i + 8].copy_from_slice(&words[i].to_be_bytes());
        }
    }
}
