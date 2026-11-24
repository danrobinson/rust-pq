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
    let abcd = _mm_set_epi32(
        state[3] as i32,
        state[2] as i32,
        state[1] as i32,
        state[0] as i32,
    );
    let efgh = _mm_set_epi32(
        state[7] as i32,
        state[6] as i32,
        state[5] as i32,
        state[4] as i32,
    );
    let cdab = _mm_shuffle_epi32::<0xb1>(abcd);
    let hgfe = _mm_shuffle_epi32::<0x1b>(efgh);
    let initial = [
        _mm_alignr_epi8::<8>(cdab, hgfe),
        _mm_blend_epi16::<0xf0>(hgfe, cdab),
    ];
    let pairs = blocks.len() / 2;
    for i in 0..pairs {
        let offset = 2 * i;
        let pair = &mut blocks[offset..offset + 2];
        let starts = &start[offset..offset + 2];
        let ends = &end[offset..offset + 2];
        let shared = ends[0]
            .saturating_sub(starts[0])
            .min(ends[1].saturating_sub(starts[1]));
        for step in 0..shared {
            pair[0][18..22].copy_from_slice(&(starts[0] + step).to_be_bytes());
            pair[1][18..22].copy_from_slice(&(starts[1] + step).to_be_bytes());
            let hashes = compress_pair(initial, &pair[0], &pair[1]);
            pair[0][22..22 + N].copy_from_slice(&hashes[0][..N]);
            pair[1][22..22 + N].copy_from_slice(&hashes[1][..N]);
        }
        let next = [starts[0] + shared, starts[1] + shared];
        if next[0] < ends[0] || next[1] < ends[1] {
            crate::hash::chain_blocks_portable::<N>(state, pair, &next, ends);
        }
    }
    let offset = 2 * pairs;
    if offset < blocks.len() {
        crate::hash::chain_blocks_portable::<N>(
            state,
            &mut blocks[offset..],
            &start[offset..],
            &end[offset..],
        );
    }
}

#[inline]
#[target_feature(enable = "sha,ssse3,sse4.1")]
fn compress_pair(initial: [__m128i; 2], left: &[u8; 64], right: &[u8; 64]) -> [[u8; 32]; 2] {
    let load = |block: &[u8; 64]| {
        [
            load_group(block, 0),
            load_group(block, 16),
            load_group(block, 32),
            load_group(block, 48),
        ]
    };
    let mut a = ShaLane {
        work: initial,
        words: load(left),
    };
    let mut b = ShaLane {
        work: initial,
        words: load(right),
    };
    macro_rules! group {
        ($r:literal) => {{
            // SAFETY: the enclosing function enables SHA-NI, SSSE3 and SSE4.1.
            unsafe { pair_group::<$r>(&mut a, &mut b) };
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
    [digest_pair(initial, a.work), digest_pair(initial, b.work)]
}

struct ShaLane {
    work: [__m128i; 2],
    words: [__m128i; 4],
}

#[inline(always)]
unsafe fn pair_group<const R: usize>(a: &mut ShaLane, b: &mut ShaLane) {
    unsafe {
        let k = _mm_set_epi32(
            super::K[4 * R + 3] as i32,
            super::K[4 * R + 2] as i32,
            super::K[4 * R + 1] as i32,
            super::K[4 * R] as i32,
        );
        lane_group::<R>(a, k);
        lane_group::<R>(b, k);
    }
}

#[inline(always)]
unsafe fn lane_group<const R: usize>(lane: &mut ShaLane, k: __m128i) {
    unsafe {
        let i = R % 4;
        let w = &mut lane.words;
        if R >= 4 {
            let sum = _mm_sha256msg1_epu32(w[i], w[(i + 1) % 4]);
            let cross = _mm_alignr_epi8::<4>(w[(i + 3) % 4], w[(i + 2) % 4]);
            w[i] = _mm_sha256msg2_epu32(_mm_add_epi32(sum, cross), w[(i + 3) % 4]);
        }
        let wk = _mm_add_epi32(w[i], k);
        let [abef, cdgh] = lane.work;
        let cdgh = _mm_sha256rnds2_epu32(cdgh, abef, wk);
        lane.work = [
            _mm_sha256rnds2_epu32(abef, cdgh, _mm_shuffle_epi32::<0x0e>(wk)),
            cdgh,
        ];
    }
}

#[inline]
#[target_feature(enable = "sse2")]
fn load_group(b: &[u8; 64], i: usize) -> __m128i {
    #[inline(always)]
    fn word(b: &[u8; 64], i: usize) -> i32 {
        i32::from_be_bytes([b[i], b[i + 1], b[i + 2], b[i + 3]])
    }
    _mm_set_epi32(word(b, i + 12), word(b, i + 8), word(b, i + 4), word(b, i))
}

#[inline]
#[target_feature(enable = "sse4.1")]
fn digest_pair(initial: [__m128i; 2], work: [__m128i; 2]) -> [u8; 32] {
    let abef = _mm_add_epi32(initial[0], work[0]);
    let cdgh = _mm_add_epi32(initial[1], work[1]);
    let mut dst = [0; 32];
    dst[0..4].copy_from_slice(&_mm_extract_epi32::<3>(abef).to_be_bytes());
    dst[4..8].copy_from_slice(&_mm_extract_epi32::<2>(abef).to_be_bytes());
    dst[8..12].copy_from_slice(&_mm_extract_epi32::<3>(cdgh).to_be_bytes());
    dst[12..16].copy_from_slice(&_mm_extract_epi32::<2>(cdgh).to_be_bytes());
    dst[16..20].copy_from_slice(&_mm_extract_epi32::<1>(abef).to_be_bytes());
    dst[20..24].copy_from_slice(&_mm_extract_epi32::<0>(abef).to_be_bytes());
    dst[24..28].copy_from_slice(&_mm_extract_epi32::<1>(cdgh).to_be_bytes());
    dst[28..32].copy_from_slice(&_mm_extract_epi32::<0>(cdgh).to_be_bytes());
    dst
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
