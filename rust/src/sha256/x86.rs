//! Dispatch independent chains to AVX-512, SHA-NI pairs or AVX2. Intel's SHA256RNDS2
//! expects ABEF/CDGH rather than the digest's ABCD/EFGH layout. The shuffle
//! conventions follow RustCrypto sha2 0.11.1 (src/sha256/x86_sha.rs).
//! See LICENSE-MIT-RustCrypto in the crate root.
use core::arch::x86_64::*;

mod avx2;
mod avx512;
cpufeatures::new!(has_avx512, "avx512f", "avx512bw");

#[inline]
pub(crate) fn avx512_available() -> bool {
    has_avx512::get()
}
cpufeatures::new!(has_avx2, "avx2");
cpufeatures::new!(sha_ni, "sha", "ssse3", "sse4.1");

pub fn chain_blocks<const N: usize>(
    state: &[u32; 8],
    blocks: &mut [[u8; 64]],
    start: &[u32],
    end: &[u32],
) {
    if N > 32 || start.len() < blocks.len() || end.len() < blocks.len() {
        return crate::hash::chain_blocks_portable::<N>(state, blocks, start, end);
    }
    if matches!(N, 16 | 24 | 32) && blocks.len() >= 8 && has_avx512::get() {
        // SAFETY: CPUID and the OS register-state check enable AVX-512F/BW.
        unsafe { avx512::chains::<N>(state, blocks, start, end) }
    } else if sha_ni::get() {
        // SAFETY: the CPU supports SHA-NI, SSSE3 and SSE4.1.
        unsafe { chains::<N>(state, blocks, start, end) }
    } else if has_avx2::get() {
        // SAFETY: the CPU and OS support AVX2.
        unsafe { avx2::chains::<N>(state, blocks, start, end) }
    } else {
        crate::hash::chain_blocks_portable::<N>(state, blocks, start, end)
    }
}

#[target_feature(enable = "sha,ssse3,sse4.1")]
fn chains<const N: usize>(state: &[u32; 8], blocks: &mut [[u8; 64]], start: &[u32], end: &[u32]) {
    // SAFETY: the two unaligned 16-byte loads cover the 32-byte state.
    let ptr = state.as_ptr().cast::<__m128i>();
    let (abcd, efgh) = unsafe { (_mm_loadu_si128(ptr), _mm_loadu_si128(ptr.add(1))) };
    let cdab = _mm_shuffle_epi32::<0xb1>(abcd);
    let hgfe = _mm_shuffle_epi32::<0x1b>(efgh);
    let initial = [
        _mm_alignr_epi8::<8>(cdab, hgfe),
        _mm_blend_epi16::<0xf0>(hgfe, cdab),
    ];
    for (i, pair) in blocks.chunks_mut(2).enumerate() {
        let offset = 2 * i;
        let starts = &start[offset..offset + pair.len()];
        let ends = &end[offset..offset + pair.len()];
        let [left, right] = pair else {
            crate::hash::chain_blocks_portable::<N>(state, pair, starts, ends);
            continue;
        };
        let shared = ends[0]
            .saturating_sub(starts[0])
            .min(ends[1].saturating_sub(starts[1]));
        for step in 0..shared {
            left[18..22].copy_from_slice(&(starts[0] + step).to_be_bytes());
            right[18..22].copy_from_slice(&(starts[1] + step).to_be_bytes());
            let hashes = compress_pair(initial, left, right);
            left[22..22 + N].copy_from_slice(&hashes[0][..N]);
            right[22..22 + N].copy_from_slice(&hashes[1][..N]);
        }
        let next = [starts[0] + shared, starts[1] + shared];
        if next[0] < ends[0] || next[1] < ends[1] {
            crate::hash::chain_blocks_portable::<N>(state, pair, &next, ends);
        }
    }
}

#[inline]
#[target_feature(enable = "sha,ssse3,sse4.1")]
fn compress_pair(initial: [__m128i; 2], left: &[u8; 64], right: &[u8; 64]) -> [[u8; 32]; 2] {
    let swap = _mm_set_epi64x(0x0c0d0e0f08090a0b, 0x0405060700010203);
    let mut result = [[0u8; 32]; 2];
    let mut work = [initial; 2];
    let mut schedule = [[_mm_setzero_si128(); 4]; 2];
    for (lane, block) in [left, right].into_iter().enumerate() {
        for (slot, bytes) in schedule[lane].iter_mut().zip(block.as_chunks::<16>().0) {
            // SAFETY: bytes contains exactly 16 bytes.
            *slot = _mm_shuffle_epi8(unsafe { _mm_loadu_si128(bytes.as_ptr().cast()) }, swap);
        }
    }
    // Expand these fixed groups at compile time. This keeps the two rolling
    // message schedules in registers and exposes independent SHA instructions.
    macro_rules! group {
        ($r:literal) => {{
            const I: usize = $r % 4;
            // SAFETY: four constants per group, from offsets 0 through 60.
            let k = unsafe { _mm_loadu_si128(super::K[4 * $r..].as_ptr().cast()) };
            for lane in 0..2 {
                let w = &mut schedule[lane];
                if $r >= 4 {
                    let sum = _mm_sha256msg1_epu32(w[I], w[(I + 1) % 4]);
                    let cross = _mm_alignr_epi8::<4>(w[(I + 3) % 4], w[(I + 2) % 4]);
                    w[I] = _mm_sha256msg2_epu32(_mm_add_epi32(sum, cross), w[(I + 3) % 4]);
                }
                let wk = _mm_add_epi32(w[I], k);
                let [abef, cdgh] = &mut work[lane];
                *cdgh = _mm_sha256rnds2_epu32(*cdgh, *abef, wk);
                *abef = _mm_sha256rnds2_epu32(*abef, *cdgh, _mm_shuffle_epi32::<0x0e>(wk));
            }
        }};
    }
    group!(0);
    group!(1);
    group!(2);
    group!(3);
    group!(4);
    group!(5);
    group!(6);
    group!(7);
    group!(8);
    group!(9);
    group!(10);
    group!(11);
    group!(12);
    group!(13);
    group!(14);
    group!(15);
    for (dst, [abef, cdgh]) in result.iter_mut().zip(work) {
        let feba = _mm_shuffle_epi32::<0x1b>(_mm_add_epi32(abef, initial[0]));
        let dchg = _mm_shuffle_epi32::<0xb1>(_mm_add_epi32(cdgh, initial[1]));
        let lo = _mm_shuffle_epi8(_mm_blend_epi16::<0xf0>(feba, dchg), swap);
        let hi = _mm_shuffle_epi8(_mm_alignr_epi8::<8>(dchg, feba), swap);
        // SAFETY: two unaligned 16-byte stores fill this 32-byte digest.
        let ptr = dst.as_mut_ptr().cast::<__m128i>();
        unsafe {
            _mm_storeu_si128(ptr, lo);
            _mm_storeu_si128(ptr.add(1), hi);
        }
    }
    result
}

pub(crate) fn fors_leaves<const N: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: crate::address::Adrs,
    first: u32,
    out: &mut [[u8; N]],
) {
    assert!(matches!(N, 16 | 24 | 32) && avx512_available());
    // SAFETY: AVX-512F/BW has been checked.
    unsafe { avx512::fors_leaves(state, sk_seed, adrs, first, out) };
}

pub(crate) fn fors_parents<const N: usize>(
    state: &[u32; 8],
    adrs: crate::address::Adrs,
    first: u32,
    values: &mut [[u8; N]],
    count: usize,
) -> usize {
    if N != 16 || count < 2 {
        return 0;
    }
    assert!(avx512_available() && count <= values.len() / 2);
    // SAFETY: CPUID and the OS register-state check enable AVX-512F/BW.
    unsafe { avx512::fors_parents(state, adrs, first, values, count) };
    count
}

pub(crate) fn key_digests<const N: usize, const L: usize>(
    state: &[u32; 8],
    inputs: &[[u8; L]],
    out: &mut [[u8; N]],
) {
    assert!(
        avx512_available()
            && N == 16
            && inputs.len() == out.len()
            && inputs.len() <= 16
            && !inputs.is_empty()
            && L == 640
    );
    // SAFETY: feature detection and both slice dimensions were checked above.
    unsafe { avx512::key_digests(state, inputs, out) }
}

pub(crate) fn wots_endpoints<const N: usize, const L: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: crate::address::Adrs,
    first: u32,
    out: &mut [[u8; L]],
) {
    assert!(
        avx512_available()
            && matches!((N, L), (16, 640) | (24, 1280) | (32, 2304))
            && out.len() <= 16
    );
    // SAFETY: each WOTS endpoint fits in its padded output row, and AVX-512 is available.
    unsafe { avx512::wots_endpoints(state, sk_seed, adrs, first, out) };
}

pub(crate) fn recover<const N: usize>(
    state: &[u32; 8],
    adrs: crate::address::Adrs,
    sig: &[u8],
    digits: &[u32],
    out: &mut [[u8; 64]],
) {
    assert!(
        avx512_available()
            && matches!(N, 16 | 24 | 32)
            && digits.len() == 2 * N + 3
            && sig.len() >= digits.len() * N
            && out.len() >= digits.len()
    );
    // SAFETY: all platform, input length and output bounds were checked above.
    unsafe {
        avx512::recover::<N>(state, adrs, sig, digits, out);
    }
}
