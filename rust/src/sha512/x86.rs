//! Eight independent SHA-512 compressions across the 64-bit AVX-512 lanes.
use core::arch::x86_64::*;

#[inline]
#[target_feature(enable = "avx512f,avx512bw")]
pub(super) fn compress_parents<const N: usize>(
    state: &[u64; 8],
    blocks: &[[u8; 128]; 8],
    output: &mut [[u8; N]],
) {
    let initial = state.map(|x| _mm512_set1_epi64(x as i64));
    let w: [__m512i; 16] = core::array::from_fn(|i| {
        let lanes: [u64; 8] = core::array::from_fn(|l| {
            u64::from_be_bytes(blocks[l][8 * i..8 * i + 8].try_into().unwrap())
        });
        // SAFETY: a vector contains eight native-endian u64 lanes.
        unsafe { core::mem::transmute(lanes) }
    });
    let digest = compress(initial, w);
    for i in 0..N / 8 {
        // SAFETY: all bit patterns are valid for the eight u64 words.
        let lanes: [u64; 8] = unsafe { core::mem::transmute(digest[i]) };
        for (lane, x) in lanes.into_iter().enumerate() {
            output[lane][8 * i..8 * i + 8].copy_from_slice(&x.to_be_bytes());
        }
    }
}

#[target_feature(enable = "avx512f")]
fn compress(initial: [__m512i; 8], mut w: [__m512i; 16]) -> [__m512i; 8] {
    let mut s = initial;
    macro_rules! step {
        ($i:expr) => {{
            const I: usize = $i;
            if I >= 16 {
                let x = w[(I + 1) % 16];
                let y = w[(I + 14) % 16];
                let s0 = _mm512_ternarylogic_epi64::<0x96>(
                    _mm512_ror_epi64::<1>(x),
                    _mm512_ror_epi64::<8>(x),
                    _mm512_srli_epi64::<7>(x),
                );
                let s1 = _mm512_ternarylogic_epi64::<0x96>(
                    _mm512_ror_epi64::<19>(y),
                    _mm512_ror_epi64::<61>(y),
                    _mm512_srli_epi64::<6>(y),
                );
                w[I % 16] = _mm512_add_epi64(
                    _mm512_add_epi64(w[I % 16], w[(I + 9) % 16]),
                    _mm512_add_epi64(s0, s1),
                );
            }
            let [a, b, c, d, e, f, g, h] = s;
            let sum1 = _mm512_ternarylogic_epi64::<0x96>(
                _mm512_ror_epi64::<14>(e),
                _mm512_ror_epi64::<18>(e),
                _mm512_ror_epi64::<41>(e),
            );
            let ch = _mm512_ternarylogic_epi64::<0xca>(e, f, g);
            let wk = _mm512_add_epi64(w[I % 16], _mm512_set1_epi64(super::K[I] as i64));
            let t1 = _mm512_add_epi64(_mm512_add_epi64(h, sum1), _mm512_add_epi64(ch, wk));
            let sum0 = _mm512_ternarylogic_epi64::<0x96>(
                _mm512_ror_epi64::<28>(a),
                _mm512_ror_epi64::<34>(a),
                _mm512_ror_epi64::<39>(a),
            );
            let maj = _mm512_ternarylogic_epi64::<0xe8>(a, b, c);
            s = [
                _mm512_add_epi64(t1, _mm512_add_epi64(sum0, maj)),
                a,
                b,
                c,
                _mm512_add_epi64(d, t1),
                e,
                f,
                g,
            ];
        }};
    }
    macro_rules! four {
        ($i:expr) => {
            step!($i);
            step!($i + 1);
            step!($i + 2);
            step!($i + 3);
        };
    }
    four!(0);
    four!(4);
    four!(8);
    four!(12);
    four!(16);
    four!(20);
    four!(24);
    four!(28);
    four!(32);
    four!(36);
    four!(40);
    four!(44);
    four!(48);
    four!(52);
    four!(56);
    four!(60);
    four!(64);
    four!(68);
    four!(72);
    four!(76);
    core::array::from_fn(|i| _mm512_add_epi64(initial[i], s[i]))
}

pub(crate) fn key_digests<const N: usize, const L: usize>(
    state: &[u64; 8],
    inputs: &[[u8; L]],
    out: &mut [[u8; N]],
) {
    assert!(
        crate::sha256::x86::avx512_available()
            && matches!((N, L), (24, 1280) | (32, 2304))
            && inputs.len() == out.len()
            && !inputs.is_empty()
            && inputs.len() <= 8
    );
    // SAFETY: feature detection, slice dimensions and complete blocks checked above.
    unsafe { digest_groups(state, inputs, out) };
}
#[target_feature(enable = "avx512f,avx512bw")]
fn digest_groups<const N: usize, const L: usize>(
    seed: &[u64; 8],
    inputs: &[[u8; L]],
    out: &mut [[u8; N]],
) {
    let mask = u8::MAX >> (8 - inputs.len());
    let mut state = seed.map(|x| _mm512_set1_epi64(x as i64));
    let lanes = _mm256_set_epi32(7, 6, 5, 4, 3, 2, 1, 0);
    let stride = _mm256_mullo_epi32(lanes, _mm256_set1_epi32((L / 8) as i32));
    let swap = _mm512_broadcast_i32x4(_mm_set_epi32(
        0x08090a0b, 0x0c0d0e0f, 0x00010203, 0x04050607,
    ));
    for off in (0..L).step_by(128) {
        // Each active lane reads one word from its own complete message block.
        let words = core::array::from_fn(|i| unsafe {
            _mm512_shuffle_epi8(
                _mm512_mask_i32gather_epi64::<8>(
                    _mm512_setzero_si512(),
                    mask,
                    stride,
                    inputs.as_ptr().cast::<u8>().add(off + 8 * i).cast(),
                ),
                swap,
            )
        });
        state = compress(state, words);
    }
    for i in 0..N / 8 {
        // The mask selects initialized output lanes, each with N/8 words.
        unsafe {
            _mm512_mask_i32scatter_epi64::<8>(
                out.as_mut_ptr().cast::<u8>().add(8 * i).cast(),
                mask,
                _mm256_mullo_epi32(lanes, _mm256_set1_epi32((N / 8) as i32)),
                _mm512_shuffle_epi8(state[i], swap),
            )
        };
    }
}
