//! Sixteen independent SHA-256 chains. Keep message words transposed across
//! steps. Only the counter and the truncated digest change between steps.
use core::arch::x86_64::*;

// Called only by AVX-512F kernels. Forced inlining keeps each schedule slot constant.
#[inline(always)]
unsafe fn compression_step<const I: usize>(state: &mut [__m512i; 8], w: &mut [__m512i; 16]) {
    unsafe {
        if I >= 16 {
            let x = w[(I + 1) % 16];
            let y = w[(I + 14) % 16];
            let s0 = _mm512_ternarylogic_epi32::<0x96>(
                _mm512_ror_epi32::<7>(x),
                _mm512_ror_epi32::<18>(x),
                _mm512_srli_epi32::<3>(x),
            );
            let s1 = _mm512_ternarylogic_epi32::<0x96>(
                _mm512_ror_epi32::<17>(y),
                _mm512_ror_epi32::<19>(y),
                _mm512_srli_epi32::<10>(y),
            );
            w[I % 16] = _mm512_add_epi32(
                _mm512_add_epi32(w[I % 16], w[(I + 9) % 16]),
                _mm512_add_epi32(s0, s1),
            );
        }
        *state = round(*state, w[I % 16], super::super::K[I]);
    }
}

// Expand within the chain loop so the compiler can specialize digest truncation.
macro_rules! compression {
    ($initial:expr,$state:expr,$words:expr) => {{
        let initial = $initial;
        let mut state = $state;
        let mut w = $words;

        // Constant indices expose the rolling schedule to register allocation.
        macro_rules! step {
            ($i:expr) => {{
                const I: usize = $i;
                // SAFETY: all expansion sites run under AVX-512F.
                unsafe { compression_step::<I>(&mut state, &mut w) };
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
        macro_rules! add {
            ($i:expr) => {
                _mm512_add_epi32(initial[$i], state[$i])
            };
        }
        [
            add!(0),
            add!(1),
            add!(2),
            add!(3),
            add!(4),
            add!(5),
            add!(6),
            add!(7),
        ]
    }};
}

#[target_feature(enable = "avx512f,avx512bw")]
pub(super) fn chains<const N: usize>(
    state: &[u32; 8],
    blocks: &mut [[u8; 64]],
    start: &[u32],
    end: &[u32],
) {
    debug_assert!(matches!(N, 16 | 24 | 32));
    let initial = state.map(|v| _mm512_set1_epi32(v as i32));
    let stride = _mm512_set_epi32(
        240, 224, 208, 192, 176, 160, 144, 128, 112, 96, 80, 64, 48, 32, 16, 0,
    );
    let swap = _mm512_broadcast_i32x4(_mm_set_epi32(
        0x0c0d0e0f, 0x08090a0b, 0x04050607, 0x00010203,
    ));
    for offset in (0..blocks.len()).step_by(16) {
        let len = (blocks.len() - offset).min(16);
        let batch = &mut blocks[offset..offset + len];
        // A short last batch has too few useful lanes on SHA-NI machines.
        if batch.len() < 8 && super::sha_ni::get() {
            // SAFETY: SHA-NI, SSSE3 and SSE4.1 are present.
            unsafe { super::chains::<N>(state, batch, &start[offset..], &end[offset..]) };
            continue;
        }
        let mask = (u16::MAX >> (16 - batch.len())) as __mmask16;
        let ptr = batch.as_ptr().cast::<u8>();
        // SAFETY: each enabled lane addresses a distinct 64-byte block. For
        // the counters the caller checked that both slices cover all blocks.
        let mut counter =
            unsafe { _mm512_maskz_loadu_epi32(mask, start.as_ptr().add(offset).cast()) };
        let ends = unsafe { _mm512_maskz_loadu_epi32(mask, end.as_ptr().add(offset).cast()) };
        let mut active = _mm512_cmplt_epu32_mask(counter, ends) & mask;
        if active == 0 {
            continue;
        }
        // Each active lane contributes exactly its final digest to the output.
        let original = active;
        let mut saved = [_mm512_setzero_si512(); 8];
        let mut words: [__m512i; 16] = core::array::from_fn(|i| {
            let v = unsafe {
                _mm512_mask_i32gather_epi32::<4>(
                    _mm512_setzero_si512(),
                    active,
                    stride,
                    ptr.add(i * 4).cast(),
                )
            };
            _mm512_shuffle_epi8(v, swap)
        });
        let fixed4 = _mm512_and_si512(words[4], _mm512_set1_epi32(0xffff0000u32 as i32));
        let half = _mm512_set1_epi32(0xffff);
        // W0..W3 hold the unchanged prefix. The first four rounds depend only on it.
        let mut prefix = initial;
        for i in 0..4 {
            prefix = round(prefix, words[i], super::super::K[i]);
        }
        loop {
            words = chain_address(words, fixed4, counter, half);
            let hash: [__m512i; 8] = compression!(initial, prefix, words);
            let next = _mm512_add_epi32(counter, _mm512_set1_epi32(1));
            let finished = active & _mm512_cmpeq_epi32_mask(next, ends);
            if finished != 0 {
                if finished == original {
                    write_finished::<N>(&hash, batch, &end[offset..], finished);
                    break;
                }
                saved = chain_done::<N>(saved, hash, finished);
                active &= !finished;
                if active == 0 {
                    write_finished::<N>(&saved, batch, &end[offset..], original);
                    break;
                }
            }
            words = chain_value::<N>(words, hash, half);
            counter = next;
        }
    }
}

#[inline]
#[target_feature(enable = "avx512f,avx512bw")]
fn chain_address(
    mut words: [__m512i; 16],
    fixed4: __m512i,
    counter: __m512i,
    half: __m512i,
) -> [__m512i; 16] {
    words[4] = _mm512_or_si512(fixed4, _mm512_srli_epi32::<16>(counter));
    words[5] = _mm512_or_si512(
        _mm512_slli_epi32::<16>(counter),
        _mm512_and_si512(words[5], half),
    );
    words
}
#[inline]
#[target_feature(enable = "avx512f,avx512bw")]
fn chain_value<const N: usize>(
    mut words: [__m512i; 16],
    hash: [__m512i; 8],
    half: __m512i,
) -> [__m512i; 16] {
    // Digest byte zero starts halfway through W5. Preserve the
    // padding after its last half-word (at W9, W11 or W13).
    words[5] = _mm512_srli_epi32::<16>(hash[0]);
    for i in 1..N / 4 {
        words[5 + i] = _mm512_or_si512(
            _mm512_slli_epi32::<16>(hash[i - 1]),
            _mm512_srli_epi32::<16>(hash[i]),
        );
    }
    words[5 + N / 4] = _mm512_or_si512(
        _mm512_slli_epi32::<16>(hash[N / 4 - 1]),
        _mm512_and_si512(words[5 + N / 4], half),
    );
    words
}
#[inline]
#[target_feature(enable = "avx512f,avx512bw")]
fn chain_done<const N: usize>(
    mut saved: [__m512i; 8],
    hash: [__m512i; 8],
    finished: u16,
) -> [__m512i; 8] {
    for i in 0..N / 4 {
        saved[i] = _mm512_mask_mov_epi32(saved[i], finished, hash[i]);
    }
    saved
}
#[inline]
#[target_feature(enable = "avx512f,avx512bw")]
fn write_finished<const N: usize>(
    hash: &[__m512i; 8],
    batch: &mut [[u8; 64]],
    ends: &[u32],
    mut lanes: u16,
) {
    let swap = _mm512_broadcast_i32x4(_mm_set_epi32(
        0x0c0d0e0f, 0x08090a0b, 0x04050607, 0x00010203,
    ));
    let mask = lanes;
    while lanes != 0 {
        let lane = lanes.trailing_zeros() as usize;
        batch[lane][18..22].copy_from_slice(&(ends[lane] - 1).to_be_bytes());
        lanes &= lanes - 1;
    }
    for offset in (0..N).step_by(16) {
        let [a, b, c, d] =
            core::array::from_fn(|i| _mm512_shuffle_epi8(hash[offset / 4 + i], swap));
        let rows = transpose_rows(a, b, c, d);
        let width = (N - offset).min(16);
        let mut lanes = mask;
        while lanes != 0 {
            let lane = lanes.trailing_zeros() as usize;
            batch[lane][22 + offset..22 + offset + width]
                .copy_from_slice(&rows[lane % 4][lane / 4][..width]);
            lanes &= lanes - 1;
        }
    }
}

#[inline]
#[target_feature(enable = "avx512f")]
fn round([a, b, c, d, e, f, g, h]: [__m512i; 8], w: __m512i, k: u32) -> [__m512i; 8] {
    let sum1 = _mm512_ternarylogic_epi32::<0x96>(
        _mm512_ror_epi32::<6>(e),
        _mm512_ror_epi32::<11>(e),
        _mm512_ror_epi32::<25>(e),
    );
    let ch = _mm512_ternarylogic_epi32::<0xca>(e, f, g);
    let t1 = _mm512_add_epi32(
        _mm512_add_epi32(h, sum1),
        _mm512_add_epi32(ch, _mm512_add_epi32(w, _mm512_set1_epi32(k as i32))),
    );
    let sum0 = _mm512_ternarylogic_epi32::<0x96>(
        _mm512_ror_epi32::<2>(a),
        _mm512_ror_epi32::<13>(a),
        _mm512_ror_epi32::<22>(a),
    );
    let maj = _mm512_ternarylogic_epi32::<0xe8>(a, b, c);
    [
        _mm512_add_epi32(t1, _mm512_add_epi32(sum0, maj)),
        a,
        b,
        c,
        _mm512_add_epi32(d, t1),
        e,
        f,
        g,
    ]
}

#[inline]
#[target_feature(enable = "avx512f")]
fn compress(initial: [__m512i; 8], state: [__m512i; 8], w: [__m512i; 16]) -> [__m512i; 8] {
    compression!(initial, state, w)
}

#[target_feature(enable = "avx512f,avx512bw")]
pub(super) fn fors_leaves<const N: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: crate::address::Adrs,
    first: u32,
    out: &mut [[u8; N]],
) {
    use crate::address::FORS_PRF;
    let template = crate::hash::short_block(
        &adrs.with_type(FORS_PRF).with_keypair(adrs.keypair),
        sk_seed,
    );
    let base: [__m512i; 16] = core::array::from_fn(|i| {
        _mm512_set1_epi32(i32::from_be_bytes(
            template[4 * i..4 * i + 4].try_into().unwrap(),
        ))
    });
    let state = state.map(|x| _mm512_set1_epi32(x as i32));
    let change = _mm512_set1_epi32(((adrs.typ as u8 ^ FORS_PRF as u8) as i32) << 16);
    // The address type first changes word two. Both hashes share the first two rounds.
    let mut prefix = state;
    for i in 0..2 {
        prefix = round(prefix, base[i], super::super::K[i]);
    }
    let prefix_prf = round(
        round(prefix, base[2], super::super::K[2]),
        base[3],
        super::super::K[3],
    );
    let prefix_f = round(
        round(
            prefix,
            _mm512_xor_si512(base[2], change),
            super::super::K[2],
        ),
        base[3],
        super::super::K[3],
    );
    let lanes = _mm512_set_epi32(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);
    let half = _mm512_set1_epi32(0xffff);
    for offset in (0..out.len()).step_by(16) {
        let size = (out.len() - offset).min(16);
        let batch = &mut out[offset..offset + size];
        let mut w = base;
        let idx = _mm512_add_epi32(lanes, _mm512_set1_epi32((first + offset as u32) as i32));
        w[4] = _mm512_or_si512(w[4], _mm512_srli_epi32::<16>(idx));
        let high = _mm512_slli_epi32::<16>(idx);
        w[5] = _mm512_or_si512(high, _mm512_and_si512(w[5], half));
        let prf = compress(state, prefix_prf, w);
        w[2] = _mm512_xor_si512(w[2], change);
        w[5] = _mm512_or_si512(high, _mm512_srli_epi32::<16>(prf[0]));
        for k in 1..N / 4 {
            w[5 + k] = _mm512_or_si512(
                _mm512_slli_epi32::<16>(prf[k - 1]),
                _mm512_srli_epi32::<16>(prf[k]),
            );
        }
        w[5 + N / 4] = _mm512_or_si512(
            _mm512_slli_epi32::<16>(prf[N / 4 - 1]),
            _mm512_and_si512(w[5 + N / 4], half),
        );
        let leaf = compress(state, prefix_f, w);
        write_words(&leaf, batch);
    }
}

#[target_feature(enable = "avx512f,avx512bw")]
pub(super) fn fors_parents<const N: usize>(
    state: &[u32; 8],
    adrs: crate::address::Adrs,
    first: u32,
    values: &mut [[u8; N]],
    count: usize,
) {
    // With N=16 the two 16-byte children fit in a single continuation block.
    let template = crate::hash::pair_block(&adrs.with_word3(0), &[0u8; N], &[0u8; N]);
    let base: [__m512i; 16] = core::array::from_fn(|i| {
        _mm512_set1_epi32(i32::from_be_bytes(
            template[4 * i..4 * i + 4].try_into().unwrap(),
        ))
    });
    let state = state.map(|x| _mm512_set1_epi32(x as i32));
    let mut prefix = state;
    for i in 0..4 {
        prefix = round(prefix, base[i], super::super::K[i]);
    }
    let lanes = _mm512_set_epi32(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);
    let children = _mm512_slli_epi32::<3>(lanes);
    let swap = _mm512_broadcast_i32x4(_mm_set_epi32(
        0x0c0d0e0f, 0x08090a0b, 0x04050607, 0x00010203,
    ));
    for j in (0..count).step_by(16) {
        let mask = u16::MAX >> (16 - (count - j).min(16));
        let indices = _mm512_add_epi32(lanes, _mm512_set1_epi32((first + j as u32) as i32));
        let mut w = base;
        w[4] = _mm512_or_si512(w[4], _mm512_srli_epi32::<16>(indices));
        let mut high = _mm512_slli_epi32::<16>(indices);
        for k in 0..8 {
            // SAFETY: the input contains two 16-byte nodes per active lane.
            let ptr = unsafe { values.as_ptr().cast::<u8>().add(32 * j + 4 * k) };
            let input = unsafe {
                _mm512_mask_i32gather_epi32::<4>(_mm512_setzero_si512(), mask, children, ptr.cast())
            };
            let word = _mm512_shuffle_epi8(input, swap);
            w[5 + k] = _mm512_or_si512(high, _mm512_srli_epi32::<16>(word));
            high = _mm512_slli_epi32::<16>(word);
        }
        w[13] = _mm512_or_si512(high, w[13]);
        let output = compress(state, prefix, w);
        write_words(&output, &mut values[j..count.min(j + 16)]);
    }
}

#[target_feature(enable = "avx512f,avx512bw")]
pub(super) fn key_digests<const N: usize, const L: usize>(
    seed: &[u32; 8],
    inputs: &[[u8; L]],
    out: &mut [[u8; N]],
) {
    let mut state = seed.map(|v| _mm512_set1_epi32(v as i32));
    let mask = u16::MAX >> (16 - inputs.len());
    let lanes = _mm512_set_epi32(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);
    let stride = _mm512_mullo_epi32(lanes, _mm512_set1_epi32((L / 4) as i32));
    let swap = _mm512_broadcast_i32x4(_mm_set_epi32(
        0x0c0d0e0f, 0x08090a0b, 0x04050607, 0x00010203,
    ));
    for off in (0..L).step_by(64) {
        let words = core::array::from_fn(|i| unsafe {
            _mm512_shuffle_epi8(
                _mm512_mask_i32gather_epi32::<4>(
                    _mm512_setzero_si512(),
                    mask,
                    stride,
                    inputs.as_ptr().cast::<u8>().add(off + 4 * i).cast(),
                ),
                swap,
            )
        });
        let mut prefix = state;
        for i in 0..4 {
            prefix = round(prefix, words[i], super::super::K[i]);
        }
        state = compress(state, prefix, words);
    }
    write_words(&state, out);
}

#[target_feature(enable = "avx512f,avx512bw")]
pub(super) fn wots_endpoints<const N: usize, const L: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: crate::address::Adrs,
    first: u32,
    out: &mut [[u8; L]],
) {
    use crate::address::{WOTS_HASH, WOTS_PRF};
    let template = crate::hash::short_block(&adrs.with_type(WOTS_PRF), sk_seed);
    let base: [__m512i; 16] = core::array::from_fn(|i| {
        _mm512_set1_epi32(i32::from_be_bytes(
            template[4 * i..4 * i + 4].try_into().unwrap(),
        ))
    });
    let initial = state.map(|x| _mm512_set1_epi32(x as i32));
    let lanes = _mm512_set_epi32(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);
    let half = _mm512_set1_epi32(0xffff);
    let change = _mm512_set1_epi32(((WOTS_HASH ^ WOTS_PRF) << 16) as i32);
    let len = 2 * N + crate::params::LEN2;
    let mut first_two = initial;
    for i in 0..2 {
        first_two = round(first_two, base[i], super::super::K[i]);
    }
    // At most one key boundary falls in a group of 16 consecutive chains.
    // Crossed lanes advance the keypair word and restart the chain word.
    for at in (0..len * out.len()).step_by(16) {
        let used = 16.min(len * out.len() - at);
        let mut w = base;
        let chain = _mm512_add_epi32(lanes, _mm512_set1_epi32((at % len) as i32));
        let cross = _mm512_cmpge_epi32_mask(chain, _mm512_set1_epi32(len as i32));
        let first_key = _mm512_set1_epi32((first + (at / len) as u32) as i32);
        let key = _mm512_mask_add_epi32(first_key, cross, first_key, _mm512_set1_epi32(1));
        let chain = _mm512_mask_sub_epi32(chain, cross, chain, _mm512_set1_epi32(len as i32));
        w[2] = _mm512_or_si512(w[2], _mm512_srli_epi32::<16>(key));
        w[3] = _mm512_slli_epi32::<16>(key);
        w[4] = _mm512_slli_epi32::<16>(chain);
        let prf = round(
            round(first_two, w[2], super::super::K[2]),
            w[3],
            super::super::K[3],
        );
        // The PRF output feeds 15 F calls directly in transposed form.
        let mut hash: [__m512i; 8] = compression!(initial, prf, w);
        w[2] = _mm512_xor_si512(w[2], change);
        let prefix = round(
            round(first_two, w[2], super::super::K[2]),
            w[3],
            super::super::K[3],
        );
        for t in 0..15 {
            w[5] = _mm512_or_si512(_mm512_set1_epi32(t << 16), _mm512_srli_epi32::<16>(hash[0]));
            for j in 1..N / 4 {
                w[5 + j] = _mm512_or_si512(
                    _mm512_slli_epi32::<16>(hash[j - 1]),
                    _mm512_srli_epi32::<16>(hash[j]),
                );
            }
            w[5 + N / 4] = _mm512_or_si512(
                _mm512_slli_epi32::<16>(hash[N / 4 - 1]),
                _mm512_and_si512(w[5 + N / 4], half),
            );
            hash = compression!(initial, prefix, w);
        }

        let key = at / len;
        let slot = at % len;
        let first_width = used.min(len - slot);
        let mut values = [[0u8; N]; 16];
        write_words(&hash, &mut values[..used]);
        let pos = 22 + slot * N;
        out[key][pos..pos + first_width * N].copy_from_slice(values[..first_width].as_flattened());
        if first_width < used {
            out[key + 1][22..22 + (used - first_width) * N]
                .copy_from_slice(values[first_width..used].as_flattened());
        }
    }
}

#[target_feature(enable = "avx512f,avx512bw")]
pub(super) fn recover<const N: usize>(
    state: &[u32; 8],
    adrs: crate::address::Adrs,
    sig: &[u8],
    digits: &[u32],
    out: &mut [[u8; 64]],
) {
    use crate::params::LEN_MAX;
    let mut counts = [0usize; 16];
    for &d in digits {
        counts[d as usize] += 1;
    }
    let mut at = [0usize; 16];
    for j in 1..16 {
        at[j] = at[j - 1] + counts[j - 1];
    }
    let mut order = [0usize; LEN_MAX];
    for (i, &digit) in digits.iter().enumerate() {
        order[at[digit as usize]] = i;
        at[digit as usize] += 1;
    }
    // A chain with start 15 already holds its endpoint.
    let workload = digits.len() - counts[15];
    for &i in &order[workload..digits.len()] {
        out[i][22..22 + N].copy_from_slice(&sig[N * i..N * (i + 1)]);
    }
    let template = crate::hash::short_block(&adrs.with_word2(0).with_word3(0), &[0u8; N]);
    let mut w: [__m512i; 16] = core::array::from_fn(|i| {
        _mm512_set1_epi32(i32::from_be_bytes(
            template[4 * i..4 * i + 4].try_into().unwrap(),
        ))
    });
    let initial = state.map(|x| _mm512_set1_epi32(x as i32));
    let mut prefix = initial;
    for i in 0..4 {
        prefix = round(prefix, w[i], super::super::K[i]);
    }
    let half = _mm512_set1_epi32(0xffff);
    let swap = _mm512_broadcast_i32x4(_mm_set_epi32(
        0x0c0d0e0f, 0x08090a0b, 0x04050607, 0x00010203,
    ));
    let mut indices = [0i32; 16];
    let mut starts = [0i32; 16];
    let mut idx = _mm512_setzero_si512();
    let mut counter = idx;
    let mut active = 0u16;
    let mut next = 0;
    let mut hash = [_mm512_setzero_si512(); 8];
    // Longest chains enter first. Refill a lane as soon as its endpoint is stored.
    while active != 0 || next < workload {
        let mut assigned = 0u16;
        while active != u16::MAX && next < workload {
            let lane = (!active).trailing_zeros() as usize;
            let i = order[next];
            next += 1;
            indices[lane] = i as i32;
            starts[lane] = digits[i] as i32;
            active |= 1 << lane;
            assigned |= 1 << lane;
        }
        if assigned != 0 {
            // Both arrays contain exactly 16 initialized 32-bit lanes.
            idx = unsafe { _mm512_loadu_si512(indices.as_ptr().cast()) };
            counter = _mm512_mask_mov_epi32(counter, assigned, unsafe {
                _mm512_loadu_si512(starts.as_ptr().cast())
            });
            let off = _mm512_mullo_epi32(idx, _mm512_set1_epi32(N as i32));
            for j in 0..N / 4 {
                // Only newly assigned lanes read a signature element.
                let input = unsafe {
                    _mm512_mask_i32gather_epi32::<1>(
                        _mm512_setzero_si512(),
                        assigned,
                        off,
                        sig.as_ptr().add(4 * j).cast(),
                    )
                };
                hash[j] =
                    _mm512_mask_mov_epi32(hash[j], assigned, _mm512_shuffle_epi8(input, swap));
            }
            w[4] = _mm512_slli_epi32::<16>(idx);
        }
        w[5] = _mm512_or_si512(
            _mm512_slli_epi32::<16>(counter),
            _mm512_srli_epi32::<16>(hash[0]),
        );
        for j in 1..N / 4 {
            w[5 + j] = _mm512_or_si512(
                _mm512_slli_epi32::<16>(hash[j - 1]),
                _mm512_srli_epi32::<16>(hash[j]),
            );
        }
        w[5 + N / 4] = _mm512_or_si512(
            _mm512_slli_epi32::<16>(hash[N / 4 - 1]),
            _mm512_and_si512(w[5 + N / 4], half),
        );
        hash = compression!(initial, prefix, w);
        counter = _mm512_add_epi32(counter, _mm512_set1_epi32(1));
        let finished = active & _mm512_cmpeq_epi32_mask(counter, _mm512_set1_epi32(15));
        if finished != 0 {
            let mut values = [[0u8; N]; 16];
            write_words(&hash, &mut values);
            let mut lanes = finished;
            while lanes != 0 {
                let lane = lanes.trailing_zeros() as usize;
                out[indices[lane] as usize][22..22 + N].copy_from_slice(&values[lane]);
                lanes &= lanes - 1;
            }
            active &= !finished;
        }
    }
}

#[target_feature(enable = "avx512f,avx512bw")]
fn write_words<const N: usize>(state: &[__m512i; 8], out: &mut [[u8; N]]) {
    let swap = _mm512_broadcast_i32x4(_mm_set_epi32(
        0x0c0d0e0f, 0x08090a0b, 0x04050607, 0x00010203,
    ));
    for offset in (0..N).step_by(16) {
        let [a, b, c, d] =
            core::array::from_fn(|i| _mm512_shuffle_epi8(state[offset / 4 + i], swap));
        let rows = transpose_rows(a, b, c, d);
        let width = (N - offset).min(16);
        let mut j = 0;
        for row in out.iter_mut() {
            row[offset..offset + width].copy_from_slice(&rows[j % 4][j / 4][..width]);
            j += 1;
        }
    }
}

#[inline]
#[target_feature(enable = "avx512f,avx512bw")]
fn transpose_rows(a: __m512i, b: __m512i, c: __m512i, d: __m512i) -> [[[u8; 16]; 4]; 4] {
    let ab0 = _mm512_unpacklo_epi32(a, b);
    let ab1 = _mm512_unpackhi_epi32(a, b);
    let cd0 = _mm512_unpacklo_epi32(c, d);
    let cd1 = _mm512_unpackhi_epi32(c, d);
    let groups = [
        _mm512_unpacklo_epi64(ab0, cd0),
        _mm512_unpackhi_epi64(ab0, cd0),
        _mm512_unpacklo_epi64(ab1, cd1),
        _mm512_unpackhi_epi64(ab1, cd1),
    ];
    // Each group holds four 16-byte rows. The first group holds lanes
    // 0, 4, 8 and 12, the second lanes 1, 5, 9 and 13, and so on.
    // SAFETY: both layouts contain the same 256 bytes with no padding.
    unsafe { core::mem::transmute(groups) }
}
