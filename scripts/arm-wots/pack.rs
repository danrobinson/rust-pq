// A bit is a known zero/one or an input (big-endian byte number, bit number).
// OR is representable only for disjoint masks or identical inputs.
#![allow(non_camel_case_types, unused_unsafe)]
use std::ops::{BitAnd, BitOr, Shl, Shr};
type Bit = u16; // 0=zero, 1=one, 2+8*byte+bit=input
type V = [Bit; 128];
type uint16x8_t = V;
#[derive(Clone, Copy)]
struct S([Bit; 64]);
impl From<u64> for S {
    fn from(x: u64) -> Self {
        S(std::array::from_fn(|i| ((x >> i) & 1) as Bit))
    }
}
impl BitAnd<u64> for S {
    type Output = Self;
    fn bitand(self, x: u64) -> Self {
        S(std::array::from_fn(|i| {
            if (x >> i) & 1 == 1 {
                self.0[i]
            } else {
                0
            }
        }))
    }
}
impl BitOr for S {
    type Output = Self;
    fn bitor(self, r: Self) -> Self {
        S(std::array::from_fn(|i| match (self.0[i], r.0[i]) {
            (0, v) | (v, 0) => v,
            (1, _) | (_, 1) => 1,
            (a, b) if a == b => a,
            _ => panic!("nonlinear source mask"),
        }))
    }
}
impl Shl<usize> for S {
    type Output = Self;
    fn shl(self, n: usize) -> Self {
        S(std::array::from_fn(
            |i| if i >= n { self.0[i - n] } else { 0 },
        ))
    }
}
impl Shr<usize> for S {
    type Output = Self;
    fn shr(self, n: usize) -> Self {
        S(std::array::from_fn(|i| {
            if i + n < 64 {
                self.0[i + n]
            } else {
                0
            }
        }))
    }
}
fn vdup_n_u64(x: impl Into<S>) -> S {
    x.into()
}
fn vcombine_u64(lo: S, hi: S) -> V {
    std::array::from_fn(|i| if i < 64 { lo.0[i] } else { hi.0[i - 64] })
}
fn vreinterpretq_u16_u64(v: V) -> V {
    v
}
fn vreinterpretq_u16_u32(v: V) -> V {
    v
}
fn vreinterpretq_u32_u16(v: V) -> V {
    v
}
fn vrev32q_u16(v: V) -> V {
    std::array::from_fn(|i| v[i ^ 16])
}
fn vextq_u16<const K: usize>(a: V, b: V) -> V {
    std::array::from_fn(|i| [a, b][(i + 16 * K) / 128][(i + 16 * K) % 128])
}
fn vsetq_lane_u16<const K: usize>(v: u16, mut a: V) -> V {
    for i in 0..16 {
        a[16 * K + i] = ((v >> i) & 1) as Bit;
    }
    a
}
fn vsetq_lane_u32<const K: usize>(v: u32, mut a: V) -> V {
    for i in 0..32 {
        a[32 * K + i] = ((v >> i) & 1) as Bit;
    }
    a
}
fn vdupq_n_u32(v: u32) -> V {
    std::array::from_fn(|i| ((v >> (i % 32)) & 1) as Bit)
}

// PRODUCTION

fn input(i: usize, base: usize) -> Bit {
    2 + (8 * (base + (i / 32) * 4 + 3 - (i % 32) / 8) + i % 8) as Bit
}
fn run<const N: usize>() {
    let word = |base| {
        S(std::array::from_fn(
            |i| if i < 32 { input(i, base) } else { 0 },
        ))
    };
    let x = std::array::from_fn(|i| input(i, 8));
    let xb = std::array::from_fn(|i| input(i, 24));
    let (a, b, d) = unsafe { pack_short::<N>(make_hdr(word(0), word(4)), x, xb) };
    for v in [a, b, d] {
        for j in 0..16 {
            let pos = 8 * (j ^ 3);
            let first = v[pos];
            let byte = if first < 2 {
                let mut x = 0;
                for k in 0..8 {
                    assert!(v[pos + k] < 2);
                    x |= v[pos + k] << k;
                }
                x
            } else {
                let byte = (first - 2) / 8;
                for k in 0..8 {
                    assert_eq!(v[pos + k], 2 + 8 * byte + k as Bit);
                }
                256 + byte
            };
            print!("{byte} ");
        }
    }
    println!();
}
fn main() {
    run::<16>();
    run::<24>();
    run::<32>();
}
