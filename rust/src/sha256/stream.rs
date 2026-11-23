//! Expand schedules for consecutive message blocks in parallel, then run
//! the dependent SHA-256 rounds in their original stream order.
cpufeatures::new!(available, "avx512f", "avx512bw", "avx512vl", "avx2", "bmi2");
cpufeatures::new!(dedicated, "sha");

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
    }};
}

#[inline(always)]
fn round(v: [u32; 8], wk: u32) -> [u32; 8] {
    let [a, b, c, d, e, f, g, h] = v;
    let t1 = h
        .wrapping_add(e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25))
        .wrapping_add(g ^ (e & (f ^ g)))
        .wrapping_add(wk);
    let t2 = (a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22))
        .wrapping_add((a & b) ^ (c & (a ^ b)));
    [t1.wrapping_add(t2), a, b, c, d.wrapping_add(t1), e, f, g]
}

pub(super) fn prefix<'a>(state: &mut [u32; 8], blocks: &'a [[u8; 64]]) -> &'a [[u8; 64]] {
    if FORCE_SOFT || blocks.len() < 8 || !available::get() || dedicated::get() {
        return blocks;
    }
    let (groups, tail) = blocks.as_chunks::<8>();
    // The eight-lane schedule reduced long SHA-256 latency on the older Xeons.
    // SAFETY: available() checks the vector and scalar instruction sets.
    unsafe {
        prescheduled(state, groups);
    }
    tail
}
#[target_feature(enable = "avx512f,avx512bw,avx512vl,avx2,bmi2")]
fn expand<const I: usize>(
    mut w: [core::arch::x86_64::__m256i; 16],
) -> ([core::arch::x86_64::__m256i; 16], [u32; 8]) {
    use core::arch::x86_64::*;
    if I >= 16 {
        let x = w[(I + 1) % 16];
        let y = w[(I + 14) % 16];
        let a = _mm256_ternarylogic_epi32::<0x96>(
            _mm256_ror_epi32::<7>(x),
            _mm256_ror_epi32::<18>(x),
            _mm256_srli_epi32::<3>(x),
        );
        let b = _mm256_ternarylogic_epi32::<0x96>(
            _mm256_ror_epi32::<17>(y),
            _mm256_ror_epi32::<19>(y),
            _mm256_srli_epi32::<10>(y),
        );
        w[I % 16] = _mm256_add_epi32(
            _mm256_add_epi32(a, b),
            _mm256_add_epi32(w[I % 16], w[(I + 9) % 16]),
        );
    }
    let wk = _mm256_add_epi32(w[I % 16], _mm256_set1_epi32(super::K[I] as i32));
    // SAFETY: the row and vector have the same size and x86 lane order.
    (w, unsafe { core::mem::transmute(wk) })
}

#[target_feature(enable = "avx512f,avx512bw,avx512vl,avx2,bmi2")]
fn schedule(blocks: &[[u8; 64]; 8]) -> [[u32; 8]; 64] {
    use core::arch::x86_64::*;
    let offsets = _mm256_set_epi32(112, 96, 80, 64, 48, 32, 16, 0);
    let swap = _mm256_broadcastsi128_si256(_mm_set_epi32(
        0x0c0d0e0f, 0x08090a0b, 0x04050607, 0x00010203,
    ));
    let mut ordered = [[0u32; 8]; 64];
    // Each gather reads the same word from every complete block in this group.
    let mut w: [__m256i; 16] = core::array::from_fn(|i| unsafe {
        let ptr = blocks.as_ptr().cast::<u8>();
        _mm256_shuffle_epi8(
            _mm256_i32gather_epi32::<4>(ptr.add(i * 4).cast(), offsets),
            swap,
        )
    });
    macro_rules! put {
        ($i:expr) => {{
            let (next, row) = expand::<{ $i }>(w);
            w = next;
            ordered[$i] = row;
        }};
    }
    rounds!(put);
    let _ = w;
    ordered
}

#[target_feature(enable = "avx512f,avx512bw,avx512vl,avx2,bmi2")]
fn prescheduled(state: &mut [u32; 8], groups: &[[[u8; 64]; 8]]) {
    for blocks in groups {
        let ordered = schedule(blocks);
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
cpufeatures::new!(hardware_backend, "sha", "ssse3", "sse4.1");
// RustCrypto also honors these build-time overrides before runtime detection.
#[allow(unexpected_cfgs)]
const FORCE_SOFT: bool = cfg!(any(sha2_backend = "soft", sha2_256_backend = "soft"));

pub(super) fn remainder(state: &mut [u32; 8], blocks: &[[u8; 64]]) {
    if FORCE_SOFT {
        scalar(state, blocks);
    } else if hardware_backend::get() {
        sha2_platform::block_api::compress256(state, blocks);
    } else if has_bmi2::get() {
        // SAFETY: the checked feature enables the BMI2-specialized code generation.
        unsafe { scalar_bmi2(state, blocks) };
    } else {
        scalar(state, blocks);
    }
}

#[target_feature(enable = "bmi2")]
fn scalar_bmi2(state: &mut [u32; 8], blocks: &[[u8; 64]]) {
    scalar(state, blocks);
}

#[inline(always)]
fn scalar(state: &mut [u32; 8], blocks: &[[u8; 64]]) {
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
fn read_word(block: &[u8; 64], i: usize) -> u32 {
    u32::from_be_bytes(block[i * 4..(i + 1) * 4].try_into().unwrap())
}

#[inline(always)]
fn scalar_step<const I: usize>(v: [u32; 8], w: &mut [u32; 16]) -> [u32; 8] {
    if I >= 16 {
        let x = w[(I + 1) % 16];
        let y = w[(I + 14) % 16];
        w[I % 16] = w[I % 16]
            .wrapping_add(w[(I + 9) % 16])
            .wrapping_add(x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3))
            .wrapping_add(y.rotate_right(17) ^ y.rotate_right(19) ^ (y >> 10));
    }
    round(v, w[I % 16].wrapping_add(super::K[I]))
}
