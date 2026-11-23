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
    for (group, batch) in groups.iter_mut().enumerate() {
        let offset = group * 8;
        let lengths: [u32; 8] =
            core::array::from_fn(|i| end[offset + i].saturating_sub(start[offset + i]));
        for step in 0..*lengths.iter().max().unwrap() {
            for (lane, block) in batch.iter_mut().enumerate() {
                if step < lengths[lane] {
                    block[18..22].copy_from_slice(&(start[offset + lane] + step).to_be_bytes());
                }
            }
            let hash = compress8(initial, batch);
            for (word, values) in hash.iter().take(N.div_ceil(4)).enumerate() {
                // SAFETY: an AVX2 integer vector holds eight native-endian u32s.
                let lanes: [u32; 8] = unsafe { core::mem::transmute(*values) };
                let count = 4.min(N - 4 * word);
                let pos = 22 + 4 * word;
                for (lane, block) in batch.iter_mut().enumerate() {
                    if step < lengths[lane] {
                        block[pos..pos + count]
                            .copy_from_slice(&lanes[lane].to_be_bytes()[..count]);
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
    macro_rules! ror {
        ($x:expr, $n:literal) => {
            _mm256_or_si256(
                _mm256_srli_epi32::<$n>($x),
                _mm256_slli_epi32::<{ 32 - $n }>($x),
            )
        };
    }
    let mut w = [_mm256_setzero_si256(); 16];
    for (i, word) in w.iter_mut().enumerate() {
        let lanes: [u32; 8] = core::array::from_fn(|lane| {
            u32::from_be_bytes(blocks[lane][4 * i..4 * i + 4].try_into().unwrap())
        });
        // SAFETY: all bit patterns are valid, and lane order is little-endian x86.
        *word = unsafe { core::mem::transmute::<[u32; 8], __m256i>(lanes) };
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = initial;
    for (i, &k) in super::super::K.iter().enumerate() {
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
        [a, b, c, d, e, f, g, h] = [
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
    let rounds = [a, b, c, d, e, f, g, h];
    core::array::from_fn(|i| _mm256_add_epi32(initial[i], rounds[i]))
}
