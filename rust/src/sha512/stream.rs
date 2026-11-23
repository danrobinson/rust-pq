//! Expand schedules for consecutive message blocks in parallel, then run
//! the dependent SHA-512 rounds in their original stream order.
cpufeatures::new!(available, "avx512f", "avx512bw", "bmi2");

macro_rules! rounds {
    ($step:ident) => {{
        macro_rules! eight {
            ($i:expr) => {
                $step!($i);
                $step!($i + 1);
                $step!($i + 2);
                $step!($i + 3);
                $step!($i + 4);
                $step!($i + 5);
                $step!($i + 6);
                $step!($i + 7);
            };
        }
        eight!(0);
        eight!(8);
        eight!(16);
        eight!(24);
        eight!(32);
        eight!(40);
        eight!(48);
        eight!(56);
        eight!(64);
        eight!(72);
    }};
}

#[inline(always)]
fn round(v: [u64; 8], wk: u64) -> [u64; 8] {
    let [a, b, c, d, e, f, g, h] = v;
    let t1 = h
        .wrapping_add(e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41))
        .wrapping_add(g ^ (e & (f ^ g)))
        .wrapping_add(wk);
    let t2 = (a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39))
        .wrapping_add((a & b) ^ (c & (a ^ b)));
    [t1.wrapping_add(t2), a, b, c, d.wrapping_add(t1), e, f, g]
}

cpufeatures::new!(dedicated, "sha");
pub(super) fn prefix<'a>(state: &mut [u64; 8], blocks: &'a [[u8; 128]]) -> &'a [[u8; 128]] {
    if blocks.len() < 8 || !available::get() {
        return blocks;
    }
    let (groups, tail) = blocks.as_chunks::<8>();
    // SAFETY: available() checks the vector and scalar instruction sets.
    unsafe {
        prescheduled(state, groups);
    }
    tail
}
#[target_feature(enable = "avx512f,avx512bw,bmi2")]
fn prescheduled(state: &mut [u64; 8], groups: &[[[u8; 128]; 8]]) {
    use core::arch::x86_64::*;
    let offsets = _mm256_set_epi32(112, 96, 80, 64, 48, 32, 16, 0);
    let swap = _mm512_broadcast_i32x4(_mm_set_epi32(
        0x08090a0b, 0x0c0d0e0f, 0x00010203, 0x04050607,
    ));
    for blocks in groups {
        let ptr = blocks.as_ptr().cast::<u8>();
        let mut ordered = [[0u64; 8]; 80];
        // Each gather reads the same word from every complete block in this group.
        let mut w: [__m512i; 16] = core::array::from_fn(|i| unsafe {
            _mm512_shuffle_epi8(
                _mm512_i32gather_epi64::<8>(offsets, ptr.add(i * 8).cast()),
                swap,
            )
        });
        for i in 0..80 {
            if i >= 16 {
                let x = w[(i + 1) % 16];
                let y = w[(i + 14) % 16];
                let a = _mm512_ternarylogic_epi64::<0x96>(
                    _mm512_ror_epi64::<1>(x),
                    _mm512_ror_epi64::<8>(x),
                    _mm512_srli_epi64::<7>(x),
                );
                let b = _mm512_ternarylogic_epi64::<0x96>(
                    _mm512_ror_epi64::<19>(y),
                    _mm512_ror_epi64::<61>(y),
                    _mm512_srli_epi64::<6>(y),
                );
                w[i % 16] = _mm512_add_epi64(
                    _mm512_add_epi64(a, b),
                    _mm512_add_epi64(w[i % 16], w[(i + 9) % 16]),
                );
            }
            let wk = _mm512_add_epi64(w[i % 16], _mm512_set1_epi64(super::K[i] as i64));
            // One row holds exactly one complete vector of schedule words.
            unsafe { _mm512_storeu_si512(ordered[i].as_mut_ptr().cast(), wk) };
        }
        for lane in 0..8 {
            let mut v = *state;
            macro_rules! step {
                ($i:expr) => {{
                    v = round(v, ordered[$i][lane]);
                }};
            }
            rounds!(step);
            for i in 0..8 {
                state[i] = state[i].wrapping_add(v[i]);
            }
        }
    }
}

cpufeatures::new!(has_bmi2, "bmi2");
pub(super) fn remainder(state: &mut [u64; 8], blocks: &[[u8; 128]]) {
    if has_bmi2::get() && !dedicated::get() {
        // SAFETY: the scalar rounds require only BMI2.
        unsafe { scalar(state, blocks) };
    } else {
        sha2_platform::block_api::compress512(state, blocks);
    }
}
#[target_feature(enable = "bmi2")]
fn scalar(state: &mut [u64; 8], blocks: &[[u8; 128]]) {
    for block in blocks {
        let mut w = core::array::from_fn(|i| read_word(block, i));
        let mut v = *state;
        macro_rules! step {
            ($i:expr) => {
                v = scalar_step::<{ $i }>(v, &mut w)
            };
        }
        rounds!(step);
        for i in 0..8 {
            state[i] = state[i].wrapping_add(v[i]);
        }
    }
}

#[inline(always)]
fn read_word(block: &[u8; 128], i: usize) -> u64 {
    u64::from_be_bytes(block[i * 8..(i + 1) * 8].try_into().unwrap())
}

#[inline(always)]
fn scalar_step<const I: usize>(v: [u64; 8], w: &mut [u64; 16]) -> [u64; 8] {
    if I >= 16 {
        let x = w[(I + 1) % 16];
        let y = w[(I + 14) % 16];
        w[I % 16] = w[I % 16]
            .wrapping_add(w[(I + 9) % 16])
            .wrapping_add(x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7))
            .wrapping_add(y.rotate_right(19) ^ y.rotate_right(61) ^ (y >> 6));
    }
    round(v, w[I % 16].wrapping_add(super::K[I]))
}
