#![allow(unused_unsafe)]
// Symbolic state identities force a feed-forward with the same lane and old accumulator.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum V {
    Acc(usize, usize),
    Work(usize, usize),
    Input(usize),
}
const K: [u32; 64] = [0; 64];
use std::cell::RefCell;
thread_local! {static BLOCKS:RefCell<Vec<[usize;4]>>=const{RefCell::new(Vec::new())};}
mod arm {
    use super::*;
    pub fn load_words(st: &[u32; 8], i: usize) -> V {
        assert_eq!(st, &[97; 8]);
        assert!(i == 0 || i == 4);
        V::Acc(0, i / 4)
    }
    pub fn load_be(buf: &[usize], i: usize) -> V {
        assert!(i + 16 <= buf.len());
        V::Input(buf[i])
    }
}
fn compress_block_lanes<const L: usize, const HIGH: bool>(
    a: &mut [V; L],
    e: &mut [V; L],
    m: &mut [[V; 4]; L],
    k: *const u32,
) {
    assert_eq!(L, 1);
    assert!(HIGH);
    assert_eq!(k, K.as_ptr());
    BLOCKS.with_borrow_mut(|b| {
        let s = b.len();
        assert_eq!((a[0], e[0]), (V::Acc(s, 0), V::Acc(s, 1)));
        b.push(m[0].map(|v| if let V::Input(i) = v { i } else { panic!() }));
        a[0] = V::Work(s, 0);
        e[0] = V::Work(s, 1);
    });
}
fn vaddq_u32(a: V, b: V) -> V {
    let V::Acc(s, i) = a else { panic!() };
    assert_eq!(b, V::Work(s, i));
    V::Acc(s + 1, i)
}
struct Bytes(V);
fn vreinterpretq_u8_u32(v: V) -> V {
    v
}
fn vrev32q_u8(v: V) -> Bytes {
    Bytes(v)
}
fn vst1q_u8(out: &mut [u8; 16], v: Bytes) {
    BLOCKS.with_borrow(|b| assert_eq!(v.0, V::Acc(b.len(), 0)));
    *out = [97; 16];
}
// PRODUCTION
fn main() {
    let msg = (0..640).collect::<Vec<_>>();
    assert_eq!(compress_multi_1_active(&[97; 8], &msg), [97; 16]);
    BLOCKS.with_borrow(|b| {
        for v in b {
            println!("{},{},{},{}", v[0], v[1], v[2], v[3]);
        }
    });
}
