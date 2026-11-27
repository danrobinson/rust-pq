#![allow(unused_unsafe)]
use std::cell::RefCell;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum V {
    Zero,
    Acc(u32, usize),
    Work(u32, u32, usize),
    Bytes(usize),
    Rev(u32),
}
const K: [u32; 64] = [17; 64];
const STATE: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
thread_local! {static LOG:RefCell<Vec<(u32,[usize;4])>>=const{RefCell::new(Vec::new())};}
mod arm {
    use super::*;
    pub fn load_words(st: &[u32; 8], off: usize) -> V {
        unsafe { vld1q_u32(st[off..].as_ptr()) }
    }
    pub fn load_be(bytes: &[usize], off: usize) -> V {
        let first = bytes[off];
        for j in 0..16 {
            assert_eq!(bytes[off + j], first + j);
        }
        V::Bytes(first)
    }
}
unsafe fn vld1q_u32(ptr: *const u32) -> V {
    let a = unsafe { std::slice::from_raw_parts(ptr, 4) };
    let off = a[0] % 8;
    assert!(off == 0 || off == 4);
    for j in 0..4 {
        assert_eq!(a[j], a[0] + j as u32);
    }
    V::Acc(a[0] / 8, off as usize)
}
unsafe fn vst1q_u32(ptr: *mut u32, v: V) {
    let V::Acc(s, off) = v else {
        panic!("bad feed-forward store")
    };
    for j in 0..4 {
        unsafe {
            *ptr.add(j) = s * 8 + (off + j) as u32;
        }
    }
}
fn vdupq_n_u32(v: u32) -> V {
    assert_eq!(v, 0);
    V::Zero
}
fn vaddq_u32(a: V, b: V) -> V {
    let V::Acc(s, j) = a else {
        panic!("bad accumulator")
    };
    let V::Work(old, next, i) = b else {
        panic!("bad round state")
    };
    assert_eq!((s, j), (old, i));
    V::Acc(next, i)
}
fn vreinterpretq_u8_u32(v: V) -> V {
    v
}
fn vrev32q_u8(v: V) -> V {
    let V::Acc(s, 0) = v else {
        panic!("bad truncation")
    };
    V::Rev(s)
}
unsafe fn vst1q_u8(ptr: *mut u32, v: V) {
    let V::Rev(s) = v else {
        panic!("bad digest store")
    };
    for j in 0..16 {
        unsafe {
            *ptr.add(j) = s * 16 + j as u32;
        }
    }
}
fn compress_block_lanes<const G: usize, const HIGH: bool>(
    a: &mut [V; G],
    e: &mut [V; G],
    m: &mut [[V; 4]; G],
    ptr: *const u32,
) {
    assert!(HIGH);
    assert_eq!(ptr, K.as_ptr());
    for j in 0..G {
        let V::Acc(old, 0) = a[j] else {
            panic!("bad input state")
        };
        assert_eq!(e[j], V::Acc(old, 4));
        let next = LOG.with_borrow_mut(|log| {
            log.push((
                old,
                m[j].map(|r| {
                    if let V::Bytes(b) = r {
                        b
                    } else {
                        panic!("missing message block")
                    }
                }),
            ));
            log.len() as u32
        });
        a[j] = V::Work(old, next, 0);
        e[j] = V::Work(old, next, 4);
    }
}
// PRODUCTION
fn run<const G: usize>() {
    LOG.with_borrow_mut(Vec::clear);
    let msgs = std::array::from_fn(|k| std::array::from_fn(|j| 640 * k + j));
    let mut out = [[u32::MAX; 16]; G];
    compress_multi_lanes::<G, 640>(&STATE, &msgs, &mut out);
    for (k, d) in out.into_iter().enumerate() {
        let mut node = d[0] / 16;
        for j in 0..16 {
            assert_eq!(d[j], node * 16 + j as u32);
        }
        let mut blocks = Vec::new();
        LOG.with_borrow(|log| {
            while node > 0 {
                let (prev, words) = log[node as usize - 1];
                blocks.push(words);
                node = prev;
            }
        });
        blocks.reverse();
        print!("{G} {k}|");
        for block in blocks {
            for i in block {
                print!("{i},");
            }
            print!(";");
        }
        println!();
    }
}
fn main() {
    run::<2>();
    run::<4>();
}
