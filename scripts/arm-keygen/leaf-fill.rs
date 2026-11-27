#[derive(Clone, Copy, Debug)]
struct Base;
#[derive(Clone, Copy, Debug)]
struct Key(u32, u32); // subtree index shifted by the first field, plus offset
impl std::ops::Shl<u32> for Base {
    type Output = Key;
    fn shl(self, bits: u32) -> Key {
        Key(bits, 0)
    }
}
impl std::ops::Add<u32> for Key {
    type Output = Key;
    fn add(self, delta: u32) -> Key {
        Key(self.0, self.1.checked_add(delta).unwrap())
    }
}
#[derive(Clone, Copy)]
struct Adrs;
#[derive(Clone, Copy)]
struct Seed<const N: usize> {
    state: [u32; 8],
    state512: [u64; 8],
}
const LEN2: usize = 3;
const STATE: [u32; 8] = [54; 8];
const WIDE: [u64; 8] = [83; 8];
#[derive(Clone, Copy, Debug)]
enum Byte {
    Zero,
    Header(Key),
    Value(Key, Key, usize, usize, usize),
}
fn prepare_tlen<const L: usize>(m: &mut [Byte; L], _: Adrs, key: Key, size: usize, block: usize) {
    let (n, b) = match L {
        640 => (16, 64),
        1280 => (24, 128),
        2304 => (32, 128),
        _ => panic!("unknown buffer"),
    };
    assert_eq!((size, block), (22 + n * (2 * n + 3), b));
    assert!(m.iter().all(|v| matches!(v, Byte::Zero)));
    m.fill(Byte::Header(key));
}
fn endpoints<const G: usize, const N: usize, const L: usize>(
    state: &[u32; 8],
    sk: &[u8; N],
    _: Adrs,
    first: Key,
    msgs: &mut [[Byte; L]; G],
) {
    assert_eq!(state, &STATE);
    assert_eq!(sk, &[23; N]);
    for (k, m) in msgs.iter_mut().enumerate() {
        for b in m {
            let Byte::Header(header) = *b else {
                panic!("unprepared row")
            };
            *b = Byte::Value(header, first, G, k, N);
        }
    }
}
mod arm_wide {
    use super::*;
    pub fn wots_endpoints_2<const N: usize, const L: usize>(
        s: &[u32; 8],
        k: &[u8; N],
        a: Adrs,
        b: Key,
        m: &mut [[Byte; L]; 2],
    ) {
        endpoints(s, k, a, b, m)
    }
    pub fn wots_endpoints_4<const N: usize, const L: usize>(
        s: &[u32; 8],
        k: &[u8; N],
        a: Adrs,
        b: Key,
        m: &mut [[Byte; L]; 4],
    ) {
        endpoints(s, k, a, b, m)
    }
    pub fn compress_multi_2<const L: usize>(
        state: &[u32; 8],
        m: &[[Byte; L]; 2],
        o: &mut [[Byte; 16]],
    ) {
        assert_eq!(state, &STATE);
        compress(m, o)
    }
    pub fn compress_multi_4<const L: usize>(
        state: &[u32; 8],
        m: &[[Byte; L]; 4],
        o: &mut [[Byte; 16]],
    ) {
        assert_eq!(state, &STATE);
        compress(m, o)
    }
}
fn compress<const G: usize, const N: usize, const L: usize>(
    m: &[[Byte; L]; G],
    out: &mut [[Byte; N]],
) {
    assert_eq!(out.len(), G);
    for (k, r) in out.iter_mut().enumerate() {
        let Byte::Value(h, b, g, l, n) = m[k][0] else {
            panic!("missing endpoints")
        };
        assert_eq!((g, l, n), (G, k, N));
        r.fill(Byte::Value(h, b, g, l, n));
    }
}
fn compress_tlen_pair<const N: usize, const L: usize>(
    s: &[u64; 8],
    m: &[[Byte; L]; 2],
    o: &mut [[Byte; N]],
) {
    assert_eq!(s, &WIDE);
    compress(m, o)
}
fn compress_tlen_quad<const N: usize, const L: usize>(
    s: &[u64; 8],
    m: &[[Byte; L]; 4],
    o: &mut [[Byte; N]],
) {
    assert_eq!(s, &WIDE);
    compress(m, o)
}
// PRODUCTION
fn output<const N: usize>(rows: [[Byte; N]; 16], height: u32) {
    print!("{N} {height}|");
    for r in rows {
        match r[0] {
            Byte::Zero => print!("-;"),
            Byte::Value(h, b, g, k, n) => {
                assert_eq!(n, N);
                print!("{},{},{},{},{},{};", h.0, h.1, b.0, b.1, g, k);
            }
            Byte::Header(_) => panic!("unexpected prepared message in root buffer"),
        }
    }
    println!();
}
fn main() {
    for h in 1..=4 {
        output(batch_root_16(&[23; 16], Base, h, &STATE, Adrs), h);
    }
    for h in 1..=4 {
        output(
            batch_root_512::<24, 1280>(
                &[23; 24],
                Base,
                h,
                &Seed {
                    state: STATE,
                    state512: WIDE,
                },
                Adrs,
            ),
            h,
        );
    }
    for h in 1..=4 {
        output(
            batch_root_512::<32, 2304>(
                &[23; 32],
                Base,
                h,
                &Seed {
                    state: STATE,
                    state512: WIDE,
                },
                Adrs,
            ),
            h,
        );
    }
}
