//! Keccak-f[1600] on independent sponge states in SIMD lanes.
use super::RC;

#[cfg(target_arch = "x86_64")]
pub(crate) const WIDTH: usize = 8;
#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
pub(crate) const WIDTH: usize = 2;
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
    permutation!("neon,sha3");
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
    permutation!("neon");
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
    macro_rules! xor3 {
        ($a:expr,$b:expr,$c:expr) => {{
            let c = $c;
            V {
                pair: veorq_u64($a.pair, veorq_u64($b.pair, c.pair)),
                scalar: $a.scalar ^ $b.scalar ^ c.scalar,
            }
        }};
    }
    macro_rules! theta {
        ($a:expr,$b:expr) => {
            V {
                pair: veorq_u64(
                    $a.pair,
                    vsriq_n_u64::<63>(vshlq_n_u64::<1>($b.pair), $b.pair),
                ),
                scalar: $a.scalar ^ $b.scalar.rotate_left(1),
            }
        };
    }
    macro_rules! rho {
        ($a:expr,$d:expr,$r:literal) => {{
            let x = veorq_u64($a.pair, $d.pair);
            V {
                pair: vsriq_n_u64::<{ 64 - $r }>(vshlq_n_u64::<$r>(x), x),
                scalar: ($a.scalar ^ $d.scalar).rotate_left($r),
            }
        }};
    }
    macro_rules! chi {
        ($a:expr,$b:expr,$c:expr) => {
            V {
                pair: veorq_u64($a.pair, vbicq_u64($c.pair, $b.pair)),
                scalar: $a.scalar ^ (!$b.scalar & $c.scalar),
            }
        };
    }
    macro_rules! iota {
        ($a:expr,$rc:expr) => {
            V {
                pair: veorq_u64($a.pair, vdupq_n_u64($rc)),
                scalar: $a.scalar ^ $rc,
            }
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

#[cfg(all(target_arch = "aarch64", target_vendor = "apple"))]
pub(super) fn single(state: &mut [u64; 25]) {
    let mut words = core::array::from_fn(|i| [state[i]; WIDTH]);
    // SAFETY: the hardware check is made here before calling the SHA3 kernel.
    assert!(crate::sha512::hw::arm::available());
    unsafe { sha3::permute(&mut words) }
    for i in 0..25 {
        state[i] = words[i][0];
    }
}
