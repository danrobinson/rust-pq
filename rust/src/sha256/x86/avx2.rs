//! Eight independent SHA-256 messages, one per AVX2 lane. This is the
//! multi-buffer fallback for x86-64 CPUs without SHA-NI.
use core::arch::x86_64::*;

#[target_feature(enable = "avx2")]
pub(super) fn chains<const N: usize>(
    state: &[u32; 8],
    blocks: &mut [[u8; 64]],
    start: &[u32],
    end: &[u32],
) {
    let initial = state.map(|x| _mm256_set1_epi32(x as i32));
    let (groups, tail) = blocks.as_chunks_mut::<8>();
    let consumed = 8 * groups.len();
    for group in 0..groups.len() {
        let batch = &mut groups[group];
        let offset = group * 8;
        let lengths: [u32; 8] =
            core::array::from_fn(|i| end[offset + i].saturating_sub(start[offset + i]));
        let mut longest = 0;
        for lane in 0..8 {
            longest = longest.max(lengths[lane]);
        }
        for step in 0..longest {
            for lane in 0..8 {
                if step < lengths[lane] {
                    batch[lane][18..22]
                        .copy_from_slice(&(start[offset + lane] + step).to_be_bytes());
                }
            }
            let hash = compress8(initial, batch);
            // SAFETY: each AVX2 register contains eight native-endian u32 lanes.
            let digest: [[u32; 8]; 8] = unsafe { core::mem::transmute(hash) };
            for lane in 0..8 {
                if step < lengths[lane] {
                    for word in 0..N.div_ceil(4).min(8) {
                        let count = 4.min(N - 4 * word);
                        let pos = 22 + 4 * word;
                        batch[lane][pos..pos + count]
                            .copy_from_slice(&digest[word][lane].to_be_bytes()[..count]);
                    }
                }
            }
        }
    }
    crate::hash::chain_blocks_portable::<N>(state, tail, &start[consumed..], &end[consumed..]);
}

#[inline]
#[target_feature(enable = "avx2")]
fn compress8(initial: [__m256i; 8], blocks: &[[u8; 64]; 8]) -> [__m256i; 8] {
    let mut w = [_mm256_setzero_si256(); 16];
    let mut i = 0;
    while i < 16 {
        let pos = 4 * i;
        w[i] = _mm256_set_epi32(
            read_word(&blocks[7], pos) as i32,
            read_word(&blocks[6], pos) as i32,
            read_word(&blocks[5], pos) as i32,
            read_word(&blocks[4], pos) as i32,
            read_word(&blocks[3], pos) as i32,
            read_word(&blocks[2], pos) as i32,
            read_word(&blocks[1], pos) as i32,
            read_word(&blocks[0], pos) as i32,
        );
        i += 1;
    }
    compress_words(initial, w)
}

#[inline(always)]
fn read_word(block: &[u8; 64], pos: usize) -> u32 {
    u32::from_be_bytes([block[pos], block[pos + 1], block[pos + 2], block[pos + 3]])
}

#[inline]
#[target_feature(enable = "avx2")]
fn compress_words(initial: [__m256i; 8], mut w: [__m256i; 16]) -> [__m256i; 8] {
    let mut state = initial;
    let mut i = 0;
    while i < 64 {
        // SAFETY: the caller has AVX2 enabled.
        unsafe { compression_step(i, &mut state, &mut w) };
        i += 1;
    }
    let [a, b, c, d, e, f, g, h] = state;
    [
        _mm256_add_epi32(initial[0], a),
        _mm256_add_epi32(initial[1], b),
        _mm256_add_epi32(initial[2], c),
        _mm256_add_epi32(initial[3], d),
        _mm256_add_epi32(initial[4], e),
        _mm256_add_epi32(initial[5], f),
        _mm256_add_epi32(initial[6], g),
        _mm256_add_epi32(initial[7], h),
    ]
}

// Called from the AVX2 kernel with round indices in 0..64.
#[inline(always)]
unsafe fn compression_step(i: usize, state: &mut [__m256i; 8], w: &mut [__m256i; 16]) {
    unsafe {
        macro_rules! ror {
            ($x:expr, $n:literal) => {
                _mm256_or_si256(
                    _mm256_srli_epi32::<$n>($x),
                    _mm256_slli_epi32::<{ 32 - $n }>($x),
                )
            };
        }
        let [a, b, c, d, e, f, g, h] = *state;
        let k = super::super::K[i];
        let slot = i % 16;
        if i >= 16 {
            let x = w[(i + 1) % 16];
            let y = w[(i + 14) % 16];
            let s0 = _mm256_xor_si256(
                _mm256_xor_si256(ror!(x, 7), ror!(x, 18)),
                _mm256_srli_epi32::<3>(x),
            );
            let s1 = _mm256_xor_si256(
                _mm256_xor_si256(ror!(y, 17), ror!(y, 19)),
                _mm256_srli_epi32::<10>(y),
            );
            w[slot] = _mm256_add_epi32(
                _mm256_add_epi32(s0, s1),
                _mm256_add_epi32(w[slot], w[(i + 9) % 16]),
            );
        }
        let sum1 = _mm256_xor_si256(_mm256_xor_si256(ror!(e, 6), ror!(e, 11)), ror!(e, 25));
        let ch = _mm256_xor_si256(_mm256_and_si256(e, f), _mm256_andnot_si256(e, g));
        let wk = _mm256_add_epi32(w[slot], _mm256_set1_epi32(k as i32));
        let t1 = _mm256_add_epi32(_mm256_add_epi32(h, sum1), _mm256_add_epi32(ch, wk));
        let sum0 = _mm256_xor_si256(_mm256_xor_si256(ror!(a, 2), ror!(a, 13)), ror!(a, 22));
        let maj = _mm256_xor_si256(
            _mm256_and_si256(a, b),
            _mm256_and_si256(c, _mm256_xor_si256(a, b)),
        );
        let t2 = _mm256_add_epi32(sum0, maj);
        *state = [
            _mm256_add_epi32(t1, t2),
            a,
            b,
            c,
            _mm256_add_epi32(d, t1),
            e,
            f,
            g,
        ];
    }
}
