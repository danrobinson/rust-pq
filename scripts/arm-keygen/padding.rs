// Distinguish every buffer, header, digest and constant byte, including equal-valued inputs.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Byte {
    Buffer(usize),
    Adrs(usize),
    Literal(u8),
    Output(usize),
}
#[derive(Clone, Copy)]
struct Adrs {
    typ: u32,
    keypair: u32,
}
impl Adrs {
    fn with_type(self, typ: u32) -> Self {
        Self { typ, keypair: 0 }
    }
    fn with_keypair(self, keypair: u32) -> Self {
        Self { keypair, ..self }
    }
    fn compress(self) -> [Byte; 22] {
        assert_eq!((self.typ, self.keypair), (1, 77));
        std::array::from_fn(Byte::Adrs)
    }
}
const WOTS_PK: u32 = 1;
struct Seed<const N: usize> {
    state: [u32; 8],
    state512: [u64; 8],
}
use std::cell::RefCell;
thread_local! {
  static HARD:RefCell<bool>=const{RefCell::new(false)};
  static CALLS:RefCell<Vec<(usize,Vec<Byte>)>>=const{RefCell::new(Vec::new())};
}
mod arm_wide {
    use super::*;
    pub fn compress_multi_1(st: &[u32; 8], msg: &[Byte]) -> [Byte; 16] {
        assert_eq!(st, &[51; 8]);
        CALLS.with_borrow_mut(|c| c.push((256, msg.to_vec())));
        std::array::from_fn(Byte::Output)
    }
}
mod sha512 {
    use super::*;
    pub mod paired {
        use super::*;
        pub fn compress_multi_1<const N: usize>(st: &[u64; 8], msg: &[Byte]) -> Option<[Byte; N]> {
            assert_eq!(st, &[512; 8]);
            HARD.with_borrow(|h| {
                h.then(|| {
                    CALLS.with_borrow_mut(|c| c.push((512, msg.to_vec())));
                    std::array::from_fn(Byte::Output)
                })
            })
        }
    }
    pub fn compress(st: &[u64; 8], buf: &[Byte], off: usize) -> [u64; 8] {
        CALLS.with_borrow_mut(|c| {
            assert_eq!(*st, [512 + c.len() as u64; 8]);
            c.push((1, buf[off..off + 128].to_vec()));
            [512 + c.len() as u64; 8]
        })
    }
}
mod hash {
    use super::*;
    pub fn trunc512<const N: usize>(st: &[u64; 8]) -> [Byte; N] {
        CALLS.with_borrow(|c| assert_eq!(*st, [512 + c.len() as u64; 8]));
        std::array::from_fn(Byte::Output)
    }
}
// PRODUCTION
fn run<const N: usize>(total: usize, hard: bool) {
    HARD.with_borrow_mut(|h| *h = hard);
    CALLS.with_borrow_mut(Vec::clear);
    let mut buf = (0..total).map(Byte::Buffer).collect::<Vec<_>>();
    let d = compress_tlen_1::<N>(
        &Seed {
            state: [51; 8],
            state512: [512; 8],
        },
        Adrs {
            typ: 19,
            keypair: 77,
        },
        &mut buf,
        2 * N + 3,
    );
    assert_eq!(d, std::array::from_fn(Byte::Output));
    CALLS.with_borrow(|c| {
        print!("{N} {}|", usize::from(hard));
        for (op, b) in c {
            print!("{op},{};", b.len());
        }
        print!("|");
        for x in c.iter().flat_map(|(_, b)| b) {
            let v = match x {
                Byte::Literal(b) => u32::from(*b),
                Byte::Adrs(i) => 256 + *i as u32,
                Byte::Buffer(i) => 512 + *i as u32,
                Byte::Output(_) => panic!(),
            };
            print!("{v},");
        }
        println!();
    });
}
fn main() {
    for hard in [false, true] {
        run::<16>(640, hard);
        run::<24>(1280, hard);
        run::<32>(2304, hard);
    }
}
