//! Sequential SHAKE absorption. Five active lanes of each AVX-512 register hold
//! one row. Between the two rounds of each pair they instead hold a diagonal.
use super::{RATE, RC};
use core::arch::x86_64::*;
type V = __m512i;
type Grid = [V; 5];

const ROT: [[u64; 5]; 5] = [
    [0, 1, 62, 28, 27],
    [36, 44, 6, 55, 20],
    [3, 10, 43, 25, 39],
    [41, 45, 15, 21, 8],
    [18, 2, 61, 56, 14],
];

#[inline]
#[target_feature(enable = "avx512f")]
fn indices<const BASE: usize, const STEP: usize>() -> V {
    let lanes: [u64; 8] = core::array::from_fn(|i| ((BASE + i * STEP) % 5) as u64);
    unsafe { core::mem::transmute(lanes) }
}

#[inline]
#[target_feature(enable = "avx512f")]
fn move_lanes<const BASE: usize, const STEP: usize>(x: V) -> V {
    _mm512_permutexvar_epi64(indices::<BASE, STEP>(), x)
}

#[inline]
#[target_feature(enable = "avx512f")]
fn delta(a: Grid) -> V {
    let c = _mm512_ternarylogic_epi64::<0x96>(
        _mm512_ternarylogic_epi64::<0x96>(a[0], a[1], a[2]),
        a[3],
        a[4],
    );
    _mm512_xor_si512(
        move_lanes::<4, 1>(c),
        move_lanes::<1, 1>(_mm512_rol_epi64::<1>(c)),
    )
}

#[inline]
#[target_feature(enable = "avx512f")]
fn rho<const DIAG: bool, const I: usize>(x: V, d: V) -> V {
    let rotations: [u64; 8] = core::array::from_fn(|j| {
        if j < 5 {
            ROT[if DIAG { (j + I) % 5 } else { I }][j]
        } else {
            0
        }
    });
    _mm512_rolv_epi64(_mm512_xor_si512(x, d), unsafe {
        core::mem::transmute(rotations)
    })
}

#[inline]
#[target_feature(enable = "avx512f")]
fn diagonal<const T: usize>(c: Grid) -> V {
    // Lane y of E belongs to column x = y-t. Rotate E so the output lanes
    // use x as their coordinate again. This makes the next theta vertical.
    let mut e = c[0];
    e = _mm512_mask_blend_epi64(1 << ((1 + T) % 5), e, c[1]);
    e = _mm512_mask_blend_epi64(1 << ((2 + T) % 5), e, c[2]);
    e = _mm512_mask_blend_epi64(1 << ((3 + T) % 5), e, c[3]);
    e = _mm512_mask_blend_epi64(1 << ((4 + T) % 5), e, c[4]);
    move_lanes::<T, 1>(e)
}

#[inline]
#[target_feature(enable = "avx512f")]
fn even(a: Grid, rc: u64) -> Grid {
    let d = delta(a);
    let b = [
        move_lanes::<0, 3>(rho::<false, 0>(a[0], d)),
        move_lanes::<1, 3>(rho::<false, 1>(a[1], d)),
        move_lanes::<2, 3>(rho::<false, 2>(a[2], d)),
        move_lanes::<3, 3>(rho::<false, 3>(a[3], d)),
        move_lanes::<4, 3>(rho::<false, 4>(a[4], d)),
    ];
    let mut c: Grid = core::array::from_fn(|x| {
        _mm512_ternarylogic_epi64::<0xd2>(b[x], b[(x + 1) % 5], b[(x + 2) % 5])
    });
    c[0] = _mm512_mask_xor_epi64(c[0], 1, c[0], _mm512_set1_epi64(rc as i64));
    [
        diagonal::<0>(c),
        diagonal::<1>(c),
        diagonal::<2>(c),
        diagonal::<3>(c),
        diagonal::<4>(c),
    ]
}

#[inline]
#[target_feature(enable = "avx512f")]
fn odd(a: Grid, rc: u64) -> Grid {
    let d = delta(a);
    // The image under pi of (x,x+t) is (x+t,3t).
    let b = [
        rho::<true, 0>(a[0], d),
        move_lanes::<3, 1>(rho::<true, 2>(a[2], d)),
        move_lanes::<1, 1>(rho::<true, 4>(a[4], d)),
        move_lanes::<4, 1>(rho::<true, 1>(a[1], d)),
        move_lanes::<2, 1>(rho::<true, 3>(a[3], d)),
    ];
    let mut out = b.map(|x| {
        _mm512_ternarylogic_epi64::<0xd2>(x, move_lanes::<1, 1>(x), move_lanes::<2, 1>(x))
    });
    out[0] = _mm512_mask_xor_epi64(out[0], 1, out[0], _mm512_set1_epi64(rc as i64));
    out
}

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn write_row(state: &mut [u64; 25], y: usize, row: V) {
    unsafe { _mm512_mask_storeu_epi64(state.as_mut_ptr().add(5 * y).cast(), 31, row) }
}

#[target_feature(enable = "avx512f")]
unsafe fn absorb(s: &mut [u64; 25], blocks: &[u8]) {
    // Each state row has five words and the rate contains 17 words. The mask
    // restricts every memory operation to exactly the words in its row.
    let mut a: Grid = core::array::from_fn(|y| unsafe {
        _mm512_maskz_loadu_epi64(31, s.as_ptr().add(5 * y).cast())
    });
    for block in blocks.chunks_exact(RATE) {
        unsafe {
            for y in 0..3 {
                a[y] = _mm512_xor_si512(
                    a[y],
                    _mm512_maskz_loadu_epi64(31, block.as_ptr().add(40 * y).cast()),
                );
            }
            a[3] = _mm512_xor_si512(
                a[3],
                _mm512_maskz_loadu_epi64(3, block.as_ptr().add(120).cast()),
            );
        }
        for r in (0..24).step_by(2) {
            a = odd(even(a, RC[r]), RC[r + 1]);
        }
    }
    for y in 0..5 {
        unsafe { write_row(s, y, a[y]) }
    }
}

pub(super) fn blocks(state: &mut [u64; 25], blocks: &[u8]) {
    assert!(crate::sha256::x86::avx512_available() && blocks.len() % RATE == 0);
    unsafe { absorb(state, blocks) }
}
