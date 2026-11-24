//! Keccak-f[1600] on independent sponge states in SIMD lanes.
use super::RC;

#[cfg(target_arch = "x86_64")]
pub(crate) const WIDTH: usize = 8;
#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
pub(crate) const WIDTH: usize = 8;
#[cfg(all(target_arch = "aarch64", not(target_vendor = "apple")))]
pub(crate) const WIDTH: usize = 3;
pub(crate) type States = [[u64; WIDTH]; 25];

/// One copy of the FIPS 202 coordinates serves all instruction sets.
/// The operators implement theta's column parity, rho/pi, and chi on each lane.
macro_rules! round_function {
    ($feature:literal) => {
        #[inline]
        #[target_feature(enable = $feature)]
        unsafe fn round(mut a: [V; 25], rc: u64) -> [V; 25] {
            let c = [
                xor3!(a[0], a[5], xor3!(a[10], a[15], a[20])),
                xor3!(a[1], a[6], xor3!(a[11], a[16], a[21])),
                xor3!(a[2], a[7], xor3!(a[12], a[17], a[22])),
                xor3!(a[3], a[8], xor3!(a[13], a[18], a[23])),
                xor3!(a[4], a[9], xor3!(a[14], a[19], a[24])),
            ];
            let d = [
                theta!(c[4], c[1]),
                theta!(c[0], c[2]),
                theta!(c[1], c[3]),
                theta!(c[2], c[4]),
                theta!(c[3], c[0]),
            ];
            let b = [
                rho!(a[0], d[0], 0),
                rho!(a[6], d[1], 44),
                rho!(a[12], d[2], 43),
                rho!(a[18], d[3], 21),
                rho!(a[24], d[4], 14),
                rho!(a[3], d[3], 28),
                rho!(a[9], d[4], 20),
                rho!(a[10], d[0], 3),
                rho!(a[16], d[1], 45),
                rho!(a[22], d[2], 61),
                rho!(a[1], d[1], 1),
                rho!(a[7], d[2], 6),
                rho!(a[13], d[3], 25),
                rho!(a[19], d[4], 8),
                rho!(a[20], d[0], 18),
                rho!(a[4], d[4], 27),
                rho!(a[5], d[0], 36),
                rho!(a[11], d[1], 10),
                rho!(a[17], d[2], 15),
                rho!(a[23], d[3], 56),
                rho!(a[2], d[2], 62),
                rho!(a[8], d[3], 55),
                rho!(a[14], d[4], 39),
                rho!(a[15], d[0], 41),
                rho!(a[21], d[1], 2),
            ];
            macro_rules! chi_row {
                ($i:literal) => {{
                    let i = $i;
                    a[i] = chi!(b[i], b[i + 1], b[i + 2]);
                    a[i + 1] = chi!(b[i + 1], b[i + 2], b[i + 3]);
                    a[i + 2] = chi!(b[i + 2], b[i + 3], b[i + 4]);
                    a[i + 3] = chi!(b[i + 3], b[i + 4], b[i]);
                    a[i + 4] = chi!(b[i + 4], b[i], b[i + 1]);
                }};
            }
            chi_row!(0);
            chi_row!(5);
            chi_row!(10);
            chi_row!(15);
            chi_row!(20);
            a[0] = iota!(a[0], rc);
            a
        }
    };
}

#[cfg(target_arch = "x86_64")]
macro_rules! permutation {
    ($feature:literal) => {
        round_function!($feature);
        #[target_feature(enable = $feature)]
        pub(super) unsafe fn permute(words: &mut States) {
            // Register conversions preserve lane order and cover exactly one word per state.
            let mut a: [V; 25] = unsafe { core::mem::transmute(*words) };
            for &rc in &RC {
                a = unsafe { round(a, rc) };
            }
            *words = unsafe { core::mem::transmute(a) };
        }
    };
}

#[cfg(target_arch = "x86_64")]
mod avx512 {
    use super::*;
    use core::arch::x86_64::*;
    type V = __m512i;
    macro_rules! xor3 {
        ($a:expr,$b:expr,$c:expr) => {
            _mm512_ternarylogic_epi64::<0x96>($a, $b, $c)
        };
    }
    macro_rules! theta {
        ($a:expr,$b:expr) => {
            _mm512_xor_si512($a, _mm512_rol_epi64::<1>($b))
        };
    }
    macro_rules! rho {
        ($a:expr,$d:expr,$r:literal) => {
            _mm512_rol_epi64::<$r>(_mm512_xor_si512($a, $d))
        };
    }
    macro_rules! chi {
        ($a:expr,$b:expr,$c:expr) => {
            _mm512_ternarylogic_epi64::<0xd2>($a, $b, $c)
        };
    }
    macro_rules! iota {
        ($a:expr,$rc:expr) => {
            _mm512_xor_si512($a, _mm512_set1_epi64($rc as i64))
        };
    }
    permutation!("avx512f");
}

/// On Apple Silicon, pair 2-way FEAT_SHA3 vector execution with scalar ALU execution
/// to run up to 8 independent states (3x2 NEON SHA3 + 2x1 scalar) simultaneously.
#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
mod sha3 {
    use super::*;
    use core::arch::aarch64::*;
    type V = uint64x2_t;

    macro_rules! xor3 {
        ($a:expr,$b:expr,$c:expr) => {
            veor3q_u64($a, $b, $c)
        };
    }
    macro_rules! theta {
        ($a:expr,$b:expr) => {
            vrax1q_u64($a, $b)
        };
    }
    macro_rules! rho {
        ($a:expr,$d:expr,$r:literal) => {
            vxarq_u64::<{ (64 - $r) % 64 }>($a, $d)
        };
    }
    macro_rules! chi {
        ($a:expr,$b:expr,$c:expr) => {
            vbcaxq_u64($a, $c, $b)
        };
    }
    macro_rules! iota {
        ($a:expr,$rc:expr) => {
            veorq_u64($a, vdupq_n_u64($rc))
        };
    }
    round_function!("neon,sha3");

    /// In-place SHA3 NEON round with minimal temporary vector pressure so that
    /// simultaneous scalar rounds do not trigger vector register spills.
    #[inline]
    #[target_feature(enable = "neon,sha3")]
    unsafe fn round_inplace(mut a: [V; 25], rc: u64) -> [V; 25] {
        let c = [
            veor3q_u64(a[0], a[5], veor3q_u64(a[10], a[15], a[20])),
            veor3q_u64(a[1], a[6], veor3q_u64(a[11], a[16], a[21])),
            veor3q_u64(a[2], a[7], veor3q_u64(a[12], a[17], a[22])),
            veor3q_u64(a[3], a[8], veor3q_u64(a[13], a[18], a[23])),
            veor3q_u64(a[4], a[9], veor3q_u64(a[14], a[19], a[24])),
        ];
        let d = [
            vrax1q_u64(c[4], c[1]),
            vrax1q_u64(c[0], c[2]),
            vrax1q_u64(c[1], c[3]),
            vrax1q_u64(c[2], c[4]),
            vrax1q_u64(c[3], c[0]),
        ];
        let t = vxarq_u64::<63>(a[1], d[1]);
        a[0] = veorq_u64(a[0], d[0]);
        a[1] = vxarq_u64::<20>(a[6], d[1]);
        a[6] = vxarq_u64::<44>(a[9], d[4]);
        a[9] = vxarq_u64::<3>(a[22], d[2]);
        a[22] = vxarq_u64::<25>(a[14], d[4]);
        a[14] = vxarq_u64::<46>(a[20], d[0]);
        a[20] = vxarq_u64::<2>(a[2], d[2]);
        a[2] = vxarq_u64::<21>(a[12], d[2]);
        a[12] = vxarq_u64::<39>(a[13], d[3]);
        a[13] = vxarq_u64::<56>(a[19], d[4]);
        a[19] = vxarq_u64::<8>(a[23], d[3]);
        a[23] = vxarq_u64::<23>(a[15], d[0]);
        a[15] = vxarq_u64::<37>(a[4], d[4]);
        a[4] = vxarq_u64::<50>(a[24], d[4]);
        a[24] = vxarq_u64::<62>(a[21], d[1]);
        a[21] = vxarq_u64::<9>(a[8], d[3]);
        a[8] = vxarq_u64::<19>(a[16], d[1]);
        a[16] = vxarq_u64::<28>(a[5], d[0]);
        a[5] = vxarq_u64::<36>(a[3], d[3]);
        a[3] = vxarq_u64::<43>(a[18], d[3]);
        a[18] = vxarq_u64::<49>(a[17], d[2]);
        a[17] = vxarq_u64::<54>(a[11], d[1]);
        a[11] = vxarq_u64::<58>(a[7], d[2]);
        a[7] = vxarq_u64::<61>(a[10], d[0]);
        a[10] = t;
        macro_rules! chi_row {
            ($i:literal) => {{
                let i = $i;
                let (b0, b1, b2, b3, b4) = (a[i], a[i + 1], a[i + 2], a[i + 3], a[i + 4]);
                a[i] = vbcaxq_u64(b0, b2, b1);
                a[i + 1] = vbcaxq_u64(b1, b3, b2);
                a[i + 2] = vbcaxq_u64(b2, b4, b3);
                a[i + 3] = vbcaxq_u64(b3, b0, b4);
                a[i + 4] = vbcaxq_u64(b4, b1, b0);
            }};
        }
        chi_row!(0);
        chi_row!(5);
        chi_row!(10);
        chi_row!(15);
        chi_row!(20);
        a[0] = veorq_u64(a[0], vdupq_n_u64(rc));
        a
    }

    /// In-place scalar Keccak round running on integer ALUs concurrently with NEON SHA3.
    #[inline(always)]
    fn round_scalar(a: &mut [u64; 25], rc: u64) {
        let c0 = a[0] ^ a[5] ^ a[10] ^ a[15] ^ a[20];
        let c1 = a[1] ^ a[6] ^ a[11] ^ a[16] ^ a[21];
        let c2 = a[2] ^ a[7] ^ a[12] ^ a[17] ^ a[22];
        let c3 = a[3] ^ a[8] ^ a[13] ^ a[18] ^ a[23];
        let c4 = a[4] ^ a[9] ^ a[14] ^ a[19] ^ a[24];
        let d0 = c4 ^ c1.rotate_left(1);
        let d1 = c0 ^ c2.rotate_left(1);
        let d2 = c1 ^ c3.rotate_left(1);
        let d3 = c2 ^ c4.rotate_left(1);
        let d4 = c3 ^ c0.rotate_left(1);
        let mut i = 0;
        while i < 25 {
            a[i] ^= d0;
            a[i + 1] ^= d1;
            a[i + 2] ^= d2;
            a[i + 3] ^= d3;
            a[i + 4] ^= d4;
            i += 5;
        }
        let t = a[1].rotate_left(1);
        a[1] = a[6].rotate_left(44);
        a[6] = a[9].rotate_left(20);
        a[9] = a[22].rotate_left(61);
        a[22] = a[14].rotate_left(39);
        a[14] = a[20].rotate_left(18);
        a[20] = a[2].rotate_left(62);
        a[2] = a[12].rotate_left(43);
        a[12] = a[13].rotate_left(25);
        a[13] = a[19].rotate_left(8);
        a[19] = a[23].rotate_left(56);
        a[23] = a[15].rotate_left(41);
        a[15] = a[4].rotate_left(27);
        a[4] = a[24].rotate_left(14);
        a[24] = a[21].rotate_left(2);
        a[21] = a[8].rotate_left(55);
        a[8] = a[16].rotate_left(45);
        a[16] = a[5].rotate_left(36);
        a[5] = a[3].rotate_left(28);
        a[3] = a[18].rotate_left(21);
        a[18] = a[17].rotate_left(15);
        a[17] = a[11].rotate_left(10);
        a[11] = a[7].rotate_left(6);
        a[7] = a[10].rotate_left(3);
        a[10] = t;
        let mut i = 0;
        while i < 25 {
            let (b0, b1, b2, b3, b4) = (a[i], a[i + 1], a[i + 2], a[i + 3], a[i + 4]);
            a[i] = b0 ^ (!b1 & b2);
            a[i + 1] = b1 ^ (!b2 & b3);
            a[i + 2] = b2 ^ (!b3 & b4);
            a[i + 3] = b3 ^ (!b4 & b0);
            a[i + 4] = b4 ^ (!b0 & b1);
            i += 5;
        }
        a[0] ^= rc;
    }

    #[inline]
    #[target_feature(enable = "neon,sha3")]
    unsafe fn load_pair(words: &States, off: usize) -> [V; 25] {
        core::array::from_fn(|i| unsafe { vld1q_u64(words[i].as_ptr().add(off)) })
    }

    #[inline]
    #[target_feature(enable = "neon,sha3")]
    unsafe fn store_pair(words: &mut States, off: usize, a: &[V; 25]) {
        for i in 0..25 {
            unsafe { vst1q_u64(words[i].as_mut_ptr().add(off), a[i]) };
        }
    }

    #[target_feature(enable = "neon,sha3")]
    unsafe fn permute_pair(words: &mut States, off: usize) {
        let mut a = unsafe { load_pair(words, off) };
        for &rc in &RC {
            a = unsafe { round(a, rc) };
        }
        unsafe { store_pair(words, off, &a) };
    }

    /// 3-way hybrid: 2 lanes on NEON SHA3 + 1 lane on scalar ALUs.
    #[target_feature(enable = "neon,sha3")]
    unsafe fn permute3(words: &mut States, off: usize) {
        let mut v = unsafe { load_pair(words, off) };
        let mut s: [u64; 25] = core::array::from_fn(|i| words[i][off + 2]);
        for &rc in &RC {
            v = unsafe { round_inplace(v, rc) };
            round_scalar(&mut s, rc);
        }
        unsafe { store_pair(words, off, &v) };
        for i in 0..25 {
            words[i][off + 2] = s[i];
        }
    }

    /// 5-way hybrid: 2x2 lanes on NEON SHA3 + 1 lane on scalar ALUs (2:1 round cadence).
    #[target_feature(enable = "neon,sha3")]
    unsafe fn permute5(words: &mut States, off: usize) {
        let mut a0 = unsafe { load_pair(words, off) };
        let mut s: [u64; 25] = core::array::from_fn(|i| words[i][off + 4]);
        for k in 0..12 {
            a0 = unsafe { round_inplace(a0, RC[2 * k]) };
            a0 = unsafe { round_inplace(a0, RC[2 * k + 1]) };
            round_scalar(&mut s, RC[k]);
        }
        unsafe { store_pair(words, off, &a0) };
        let mut a1 = unsafe { load_pair(words, off + 2) };
        for k in 0..12 {
            a1 = unsafe { round_inplace(a1, RC[2 * k]) };
            a1 = unsafe { round_inplace(a1, RC[2 * k + 1]) };
            round_scalar(&mut s, RC[12 + k]);
        }
        unsafe { store_pair(words, off + 2, &a1) };
        for i in 0..25 {
            words[i][off + 4] = s[i];
        }
    }

    /// 8-way hybrid: 3x2 lanes on NEON SHA3 + 2 lanes on scalar ALUs (3:2 round cadence).
    #[target_feature(enable = "neon,sha3")]
    pub(super) unsafe fn permute(words: &mut States) {
        let mut a0 = unsafe { load_pair(words, 0) };
        let mut s: [u64; 25] = core::array::from_fn(|i| words[i][6]);
        for k in 0..8 {
            a0 = unsafe { round_inplace(a0, RC[3 * k]) };
            a0 = unsafe { round_inplace(a0, RC[3 * k + 1]) };
            round_scalar(&mut s, RC[2 * k]);
            a0 = unsafe { round_inplace(a0, RC[3 * k + 2]) };
            round_scalar(&mut s, RC[2 * k + 1]);
        }
        unsafe { store_pair(words, 0, &a0) };

        let mut a1 = unsafe { load_pair(words, 2) };
        for k in 0..4 {
            a1 = unsafe { round_inplace(a1, RC[3 * k]) };
            a1 = unsafe { round_inplace(a1, RC[3 * k + 1]) };
            round_scalar(&mut s, RC[16 + 2 * k]);
            a1 = unsafe { round_inplace(a1, RC[3 * k + 2]) };
            round_scalar(&mut s, RC[16 + 2 * k + 1]);
        }
        for i in 0..25 {
            words[i][6] = s[i];
        }
        s = core::array::from_fn(|i| words[i][7]);
        for k in 0..4 {
            a1 = unsafe { round_inplace(a1, RC[12 + 3 * k]) };
            a1 = unsafe { round_inplace(a1, RC[12 + 3 * k + 1]) };
            round_scalar(&mut s, RC[2 * k]);
            a1 = unsafe { round_inplace(a1, RC[12 + 3 * k + 2]) };
            round_scalar(&mut s, RC[2 * k + 1]);
        }
        unsafe { store_pair(words, 2, &a1) };

        let mut a2 = unsafe { load_pair(words, 4) };
        for k in 0..8 {
            a2 = unsafe { round_inplace(a2, RC[3 * k]) };
            a2 = unsafe { round_inplace(a2, RC[3 * k + 1]) };
            round_scalar(&mut s, RC[8 + 2 * k]);
            a2 = unsafe { round_inplace(a2, RC[3 * k + 2]) };
            round_scalar(&mut s, RC[8 + 2 * k + 1]);
        }
        unsafe { store_pair(words, 4, &a2) };
        for i in 0..25 {
            words[i][7] = s[i];
        }
    }

    #[target_feature(enable = "neon,sha3")]
    pub(super) unsafe fn permute_active(words: &mut States, active: usize) {
        match active {
            0 => {}
            1 | 2 => unsafe { permute_pair(words, 0) },
            3 => unsafe { permute3(words, 0) },
            4 => unsafe {
                permute_pair(words, 0);
                permute_pair(words, 2);
            },
            5 => unsafe { permute5(words, 0) },
            6 => unsafe {
                permute3(words, 0);
                permute3(words, 3);
            },
            7 => unsafe {
                permute5(words, 0);
                permute_pair(words, 5);
            },
            _ => unsafe { permute(words) },
        }
    }

    #[target_feature(enable = "neon,sha3")]
    pub(super) unsafe fn single(state: &mut [u64; 25]) {
        let mut a = state.map(|word| vdupq_n_u64(word));
        for &rc in &RC {
            a = unsafe { round(a, rc) };
        }
        for i in 0..25 {
            state[i] = vgetq_lane_u64::<0>(a[i]);
        }
    }

    // Keep all 25 words in SHA3 vector registers across consecutive rate blocks.
    // The two vector lanes carry duplicates of this one sequential sponge.
    #[target_feature(enable = "neon,sha3")]
    pub(super) unsafe fn blocks(state: &mut [u64; 25], input: &[u8]) {
        let mut a = state.map(|word| vdupq_n_u64(word));
        for block in input.chunks_exact(super::super::RATE) {
            macro_rules! absorb_word {
                ($i:literal) => {{
                    let word = u64::from_le_bytes(block[8 * $i..8 * ($i + 1)].try_into().unwrap());
                    a[$i] = veorq_u64(a[$i], vdupq_n_u64(word));
                }};
            }
            absorb_word!(0);
            absorb_word!(1);
            absorb_word!(2);
            absorb_word!(3);
            absorb_word!(4);
            absorb_word!(5);
            absorb_word!(6);
            absorb_word!(7);
            absorb_word!(8);
            absorb_word!(9);
            absorb_word!(10);
            absorb_word!(11);
            absorb_word!(12);
            absorb_word!(13);
            absorb_word!(14);
            absorb_word!(15);
            absorb_word!(16);
            for &rc in &RC {
                a = unsafe { round(a, rc) };
            }
        }
        for i in 0..25 {
            state[i] = vgetq_lane_u64::<0>(a[i]);
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
mod neon {
    use super::*;
    use core::arch::aarch64::*;
    type V = uint64x2_t;
    macro_rules! xor3 {
        ($a:expr,$b:expr,$c:expr) => {
            veorq_u64($a, veorq_u64($b, $c))
        };
    }
    macro_rules! theta {
        ($a:expr,$b:expr) => {
            veorq_u64($a, vsriq_n_u64::<63>(vshlq_n_u64::<1>($b), $b))
        };
    }
    macro_rules! rho {
        ($a:expr,$d:expr,$r:literal) => {{
            let x = veorq_u64($a, $d);
            vsriq_n_u64::<{ 64 - $r }>(vshlq_n_u64::<$r>(x), x)
        }};
    }
    macro_rules! chi {
        ($a:expr,$b:expr,$c:expr) => {
            veorq_u64($a, vbicq_u64($c, $b))
        };
    }
    macro_rules! iota {
        ($a:expr,$rc:expr) => {
            veorq_u64($a, vdupq_n_u64($rc))
        };
    }
    round_function!("neon");

    #[target_feature(enable = "neon")]
    pub(super) unsafe fn permute_active(words: &mut States, active: usize) {
        let pairs = active.min(WIDTH).div_ceil(2);
        for p in 0..pairs {
            let off = 2 * p;
            let mut a: [V; 25] =
                core::array::from_fn(|i| unsafe { vld1q_u64(words[i].as_ptr().add(off)) });
            for &rc in &RC {
                a = unsafe { round(a, rc) };
            }
            for i in 0..25 {
                unsafe { vst1q_u64(words[i].as_mut_ptr().add(off), a[i]) };
            }
        }
    }

    #[target_feature(enable = "neon")]
    pub(super) unsafe fn permute(words: &mut States) {
        unsafe { permute_active(words, WIDTH) }
    }
}

#[cfg(all(target_arch = "aarch64", not(target_vendor = "apple")))]
mod mixed {
    use super::*;
    use core::arch::aarch64::*;
    #[derive(Clone, Copy)]
    struct V {
        pair: uint64x2_t,
        scalar: u64,
    }
    #[inline]
    #[target_feature(enable = "neon")]
    unsafe fn xor3(a: V, b: V, c: V) -> V {
        V {
            pair: veorq_u64(a.pair, veorq_u64(b.pair, c.pair)),
            scalar: a.scalar ^ b.scalar ^ c.scalar,
        }
    }
    macro_rules! xor3 {
        ($a:expr, $b:expr, $c:expr) => {
            unsafe { xor3($a, $b, $c) }
        };
    }
    #[inline]
    #[target_feature(enable = "neon")]
    unsafe fn theta(a: V, b: V) -> V {
        V {
            pair: veorq_u64(a.pair, vsriq_n_u64::<63>(vshlq_n_u64::<1>(b.pair), b.pair)),
            scalar: a.scalar ^ b.scalar.rotate_left(1),
        }
    }
    macro_rules! theta {
        ($a:expr, $b:expr) => {
            unsafe { theta($a, $b) }
        };
    }
    #[inline]
    #[target_feature(enable = "neon")]
    unsafe fn rho<const R: i32, const S: i32>(a: V, d: V) -> V {
        {
            let x = veorq_u64(a.pair, d.pair);
            V {
                pair: vsriq_n_u64::<S>(vshlq_n_u64::<R>(x), x),
                scalar: (a.scalar ^ d.scalar).rotate_left(R as u32),
            }
        }
    }
    macro_rules! rho {
        ($a:expr, $d:expr, $r:literal) => {
            unsafe { rho::<$r, { 64 - $r }>($a, $d) }
        };
    }
    #[inline]
    #[target_feature(enable = "neon")]
    unsafe fn chi(a: V, b: V, c: V) -> V {
        V {
            pair: veorq_u64(a.pair, vbicq_u64(c.pair, b.pair)),
            scalar: a.scalar ^ (!b.scalar & c.scalar),
        }
    }
    macro_rules! chi {
        ($a:expr, $b:expr, $c:expr) => {
            unsafe { chi($a, $b, $c) }
        };
    }
    #[inline]
    #[target_feature(enable = "neon")]
    unsafe fn iota(a: V, rc: u64) -> V {
        V {
            pair: veorq_u64(a.pair, vdupq_n_u64(rc)),
            scalar: a.scalar ^ rc,
        }
    }
    macro_rules! iota {
        ($a:expr, $rc:expr) => {
            unsafe { iota($a, $rc) }
        };
    }
    round_function!("neon");

    #[target_feature(enable = "neon")]
    pub(super) unsafe fn permute(words: &mut States) {
        // Run the third independent state on integer ALUs alongside two NEON lanes.
        let mut a = core::array::from_fn(|i| V {
            pair: vcombine_u64(vcreate_u64(words[i][0]), vcreate_u64(words[i][1])),
            scalar: words[i][2],
        });
        for &rc in &RC {
            a = unsafe { round(a, rc) };
        }
        for i in 0..25 {
            words[i] = [
                vgetq_lane_u64::<0>(a[i].pair),
                vgetq_lane_u64::<1>(a[i].pair),
                a[i].scalar,
            ];
        }
    }
}

#[inline]
pub(crate) fn available() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        crate::sha256::x86::avx512_available()
    }
    #[cfg(target_arch = "aarch64")]
    {
        cfg!(target_feature = "neon")
    }
}

#[inline]
pub(crate) fn permute(words: &mut States) {
    assert!(available());
    // SAFETY: available() checks the target feature before entering a SIMD kernel.
    #[cfg(target_arch = "x86_64")]
    unsafe {
        avx512::permute(words)
    }
    #[cfg(all(target_arch = "aarch64", not(target_vendor = "apple")))]
    unsafe {
        mixed::permute(words)
    }
    #[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
    if crate::sha512::hw::arm::available() {
        unsafe { sha3::permute(words) }
    } else {
        unsafe { neon::permute(words) }
    }
}

/// Permute at least the first `active` lanes of `words`, skipping idle lane groups on
/// architectures where narrower kernels have lower latency.
#[inline]
pub(crate) fn permute_active(words: &mut States, active: usize) {
    if active == 0 {
        return;
    }
    assert!(available());
    #[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
    {
        if crate::sha512::hw::arm::available() {
            // SAFETY: available() checks FEAT_SHA3 before entering the kernel.
            unsafe { sha3::permute_active(words, active) }
        } else {
            // SAFETY: available() checks NEON before entering the kernel.
            unsafe { neon::permute_active(words, active) }
        }
    }
    #[cfg(not(all(target_arch = "aarch64", target_vendor = "apple")))]
    {
        let _ = active;
        permute(words);
    }
}

#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
pub(super) fn single(state: &mut [u64; 25]) {
    // SAFETY: the hardware check is made here before calling the SHA3 kernel.
    assert!(crate::sha512::hw::arm::available());
    unsafe { sha3::single(state) }
}

#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
pub(super) fn blocks(state: &mut [u64; 25], input: &[u8]) {
    assert!(crate::sha512::hw::arm::available());
    // SAFETY: available() checks FEAT_SHA3 before entering the kernel.
    unsafe { sha3::blocks(state, input) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reference_permute(state: &mut [u64; 25]) {
        for &rc in &RC {
            *state = super::super::round(state, rc);
        }
    }

    #[test]
    fn permute_and_active_lanes_match_reference() {
        if !available() {
            return;
        }
        let mut init: States = [[0; WIDTH]; 25];
        for lane in 0..WIDTH {
            for word in 0..25 {
                init[word][lane] = ((lane as u64 + 1) * 0x9e37_79b9_7f4a_7c15)
                    ^ ((word as u64 + 1) * 0xbf58_476d_1ce4_e5b9);
            }
        }
        let mut expected = [[0u64; WIDTH]; 25];
        for lane in 0..WIDTH {
            let mut s: [u64; 25] = core::array::from_fn(|w| init[w][lane]);
            reference_permute(&mut s);
            for w in 0..25 {
                expected[w][lane] = s[w];
            }
        }
        let mut full = init;
        permute(&mut full);
        assert_eq!(full, expected);

        for active in 1..=WIDTH {
            let mut partial = init;
            permute_active(&mut partial, active);
            for w in 0..25 {
                for lane in 0..active {
                    assert_eq!(
                        partial[w][lane], expected[w][lane],
                        "active={active} word={w} lane={lane}"
                    );
                }
            }
        }
    }
}
