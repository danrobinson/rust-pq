// Trace the production FORS buffers with opaque digest IDs. The subtree index
// is an indeterminate, so one trace covers every representable starting index.
use std::cell::RefCell;
use std::ops::{Add, Shl};
const WIDTH: usize = 8;
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Idx {
    factor: u32,
    offset: u32,
}
thread_local! {static LIMIT:std::cell::Cell<u32>=const{std::cell::Cell::new(0)};}
impl Idx {
    fn checked(factor: u32, offset: u32) -> Self {
        LIMIT.with(|n| assert!(factor <= n.get() && offset <= n.get()));
        Self { factor, offset }
    }
    const ZERO: Self = Self {
        factor: 0,
        offset: 0,
    };
}
impl Add<u32> for Idx {
    type Output = Self;
    fn add(self, n: u32) -> Self {
        Self::checked(self.factor, self.offset + n)
    }
}
impl Shl<usize> for Idx {
    type Output = Self;
    fn shl(self, n: usize) -> Self {
        Self::checked(self.factor << n, self.offset << n)
    }
}
impl Shl<u32> for Idx {
    type Output = Self;
    fn shl(self, n: u32) -> Self {
        self << (n as usize)
    }
}

const FORS_TREE: u32 = 3;
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Adrs {
    typ: u32,
    keypair: u32,
    height: u32,
    index: Idx,
}
impl Adrs {
    fn with_type(self, typ: u32) -> Self {
        Self {
            typ,
            keypair: 0,
            height: 0,
            index: Idx::ZERO,
        }
    }
    fn with_keypair(self, keypair: u32) -> Self {
        Self { keypair, ..self }
    }
    fn with_word2(self, height: u32) -> Self {
        Self { height, ..self }
    }
    fn with_word3(self, index: Idx) -> Self {
        Self { index, ..self }
    }
}
const BASE: Adrs = Adrs {
    typ: FORS_TREE,
    keypair: 1729,
    height: 0,
    index: Idx::ZERO,
};
#[derive(Clone, Copy, PartialEq, Debug)]
struct Digest(usize);
const EMPTY: Digest = Digest(usize::MAX);
const SECRET: Digest = Digest(usize::MAX - 1);
const SEED: Digest = Digest(usize::MAX - 2);
enum Op {
    Leaf(Idx),
    Parent(bool, u32, Idx, Digest, Digest),
}
thread_local! {static OPS:RefCell<Vec<Op>>=const{RefCell::new(Vec::new())};}
fn emit(op: Op) -> Digest {
    OPS.with_borrow_mut(|ops| {
        ops.push(op);
        Digest(ops.len() - 1)
    })
}
fn fors_leaves_fused(
    sk: &Digest,
    seed: &Digest,
    a: Adrs,
    ids: &[Idx; WIDTH],
    active: usize,
) -> [Digest; WIDTH] {
    assert_eq!((*sk, *seed, a, active), (SECRET, SEED, BASE, 8));
    ids.map(|i| emit(Op::Leaf(i)))
}
fn parent(packed: bool, seed: &Digest, a: &Adrs, l: Digest, r: Digest) -> Digest {
    assert_eq!(*seed, SEED);
    assert_eq!((a.typ, a.keypair), (FORS_TREE, BASE.keypair));
    assert_ne!(l, EMPTY);
    assert_ne!(r, EMPTY);
    emit(Op::Parent(packed, a.height, a.index, l, r))
}
fn thash_pair(seed: &Digest, a: &Adrs, l: &Digest, r: &Digest) -> Digest {
    parent(false, seed, a, *l, *r)
}
fn pair_active(
    seed: &Digest,
    a: &[Adrs; WIDTH],
    l: &[Digest; WIDTH],
    r: &[Digest; WIDTH],
    active: usize,
) -> [Digest; WIDTH] {
    assert!((1..=WIDTH).contains(&active));
    core::array::from_fn(|j| {
        if j < active {
            parent(true, seed, &a[j], l[j], r[j])
        } else {
            EMPTY
        }
    })
}
// PRODUCTION
fn show(ops: &[Op], d: Digest, z: u32, expected: Idx, trace: &mut String) {
    use std::fmt::Write;
    match ops[d.0] {
        Op::Leaf(actual) => {
            assert_eq!(actual.factor, expected.factor);
            write!(
                trace,
                "L 8 {} ",
                i64::from(actual.offset) - i64::from(expected.offset)
            )
            .unwrap()
        }
        Op::Parent(pack, h, actual, l, r) => {
            assert!(z > 0);
            assert_eq!(actual.factor, expected.factor);
            write!(
                trace,
                "B {} {} {} ",
                pack as u8,
                i64::from(h) - i64::from(z),
                i64::from(actual.offset) - i64::from(expected.offset)
            )
            .unwrap();
            let left = expected << 1u32;
            show(ops, l, z - 1, left, trace);
            show(ops, r, z - 1, left + 1, trace)
        }
    }
}
fn main() {
    for z in 3..=14 {
        LIMIT.with(|n| n.set(1 << z));
        OPS.with_borrow_mut(|ops| ops.clear());
        let root = Idx::checked(1, 0);
        let value = fors_subtree_horiz(&SECRET, &SEED, BASE, root, z);
        let mut trace = String::new();
        OPS.with_borrow(|ops| show(ops, value, z, root, &mut trace));
        println!("{z} {trace}")
    }
}
