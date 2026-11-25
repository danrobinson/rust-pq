// Every annotated digest records the source lane, full block range and byte offset.
#[derive(Copy, Clone, Debug, PartialEq)]
enum Byte {
    Input(usize, usize),
    Digest(usize, usize, usize),
    Empty,
}
const STATE: [u64; 8] = [51; 8];
use std::cell::Cell;
thread_local! {static HARD:Cell<bool>=const{Cell::new(false)};}
mod sha512 {
    use super::*;
    pub mod paired {
        use super::*;
        fn multi<const G: usize, const N: usize, const L: usize>(
            st: &[u64; 8],
            m: &[[Byte; L]; G],
            out: &mut [[Byte; N]],
        ) -> bool {
            assert_eq!(st, &STATE);
            if !HARD.get() {
                return false;
            }
            for (k, row) in m.iter().enumerate() {
                for j in 0..L {
                    assert_eq!(row[j], Byte::Input(k, j));
                }
                out[k] = std::array::from_fn(|b| Byte::Digest(k, L, b));
            }
            true
        }
        pub fn compress_multi_2<const N: usize, const L: usize>(
            s: &[u64; 8],
            m: &[[Byte; L]; 2],
            o: &mut [[Byte; N]],
        ) -> bool {
            multi(s, m, o)
        }
        pub fn compress_multi_4<const N: usize, const L: usize>(
            s: &[u64; 8],
            m: &[[Byte; L]; 4],
            o: &mut [[Byte; N]],
        ) -> bool {
            multi(s, m, o)
        }
    }
    pub fn compress(state: &[u64; 8], buf: &[Byte], off: usize) -> [u64; 8] {
        let Byte::Input(k, pos) = buf[off] else {
            panic!("missing input")
        };
        assert_eq!(pos, off);
        for j in 0..128 {
            assert_eq!(buf[off + j], Byte::Input(k, off + j));
        }
        if pos == 0 {
            assert_eq!(state, &STATE);
        } else {
            assert_eq!(state, &[(k * 4096 + off) as u64; 8]);
        }
        [(k * 4096 + off + 128) as u64; 8]
    }
}
mod hash {
    use super::*;
    pub fn trunc512<const N: usize>(st: &[u64; 8]) -> [Byte; N] {
        assert_eq!(st, &[st[0]; 8]);
        let x = st[0] as usize;
        std::array::from_fn(|b| Byte::Digest(x / 4096, x % 4096, b))
    }
}
// PRODUCTION
fn run<const N: usize, const L: usize>(hard: bool) {
    HARD.set(hard);
    for g in [2, 4] {
        let mut out = vec![[Byte::Empty; N]; g];
        if g == 2 {
            let m = std::array::from_fn(|k| std::array::from_fn(|j| Byte::Input(k, j)));
            compress_tlen_pair::<N, L>(&STATE, &m, &mut out);
        } else {
            let m = std::array::from_fn(|k| std::array::from_fn(|j| Byte::Input(k, j)));
            compress_tlen_quad::<N, L>(&STATE, &m, &mut out);
        }
        for k in 0..g {
            for b in 0..N {
                assert_eq!(out[k][b], Byte::Digest(k, L, b));
            }
        }
    }
}
fn main() {
    for hard in [false, true] {
        run::<24, 1280>(hard);
        run::<32, 2304>(hard);
    }
}
