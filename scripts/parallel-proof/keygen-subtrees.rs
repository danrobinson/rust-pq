// Digest IDs are opaque throughout the production traversal. Only a primitive
// invocation can produce an initialized ID. Indices into the arena recover the
// exact returned dependency tree, including swapped children and stale stores.
#[path = "ADDRESS_PATH"]
mod source_address;
use source_address::{TREE, WOTS_HASH};
const WIDTH: usize = PROOF_WIDTH;

// Each untouched source field is represented by a distinct token. Restrict the
// production traversal to the address operations used by Rust; it can neither
// inspect the base tokens nor branch on their values.
mod addresses {
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub(super) enum Field {
        Base(usize),
        Word(u32),
    }
    #[derive(Clone, Copy)]
    pub(super) struct Adrs([Field; 6]);
    pub(super) const BASE: Adrs = Adrs([
        Field::Base(0),
        Field::Base(1),
        Field::Base(2),
        Field::Base(3),
        Field::Base(4),
        Field::Base(5),
    ]);
    impl Adrs {
        pub(super) fn with_type(mut self, v: u32) -> Self {
            self.0[2] = Field::Word(v);
            self.0[3..].fill(Field::Word(0));
            self
        }
        pub(super) fn with_keypair(mut self, v: u32) -> Self {
            self.0[3] = Field::Word(v);
            self
        }
        pub(super) fn with_word2(mut self, v: u32) -> Self {
            self.0[4] = Field::Word(v);
            self
        }
        pub(super) fn with_word3(mut self, v: u32) -> Self {
            self.0[5] = Field::Word(v);
            self
        }
    }
    pub(super) fn fields(a: Adrs) -> [Field; 6] {
        a.0
    }
    pub(super) fn value(a: Adrs, i: usize) -> u32 {
        match a.0[i] {
            Field::Word(x) => x,
            Field::Base(_) => panic!("unwritten address field"),
        }
    }
}
use addresses::{fields, value, Adrs, BASE};
#[derive(Clone, Copy)]
struct Digest(usize);
const EMPTY: Digest = Digest(usize::MAX);
const SECRET: Digest = Digest(usize::MAX - 1);
const SEED: Digest = Digest(usize::MAX - 2);
#[derive(Clone, Copy)]
enum Op {
    Leaf(u32, u32),
    Parent(bool, u32, u32, Digest, Digest),
}
use std::cell::RefCell;
thread_local! {static OPS:RefCell<Vec<Op>>=const{RefCell::new(Vec::new())};}
fn emit(x: Op) -> Digest {
    OPS.with_borrow_mut(|ops| {
        let id = ops.len();
        ops.push(x);
        Digest(id)
    })
}
fn keygen<const N: usize>(sk: &Digest, seed: &Digest, a: Adrs) -> Digest {
    assert_eq!((sk.0, seed.0), (SECRET.0, SEED.0));
    assert_eq!(
        fields(a),
        fields(BASE.with_type(WOTS_HASH).with_keypair(value(a, 3)))
    );
    emit(Op::Leaf(1, value(a, 3)))
}
fn wots_leaves_small<const N: usize, const K: usize>(
    sk: &Digest,
    seed: &Digest,
    first: u32,
    a: Adrs,
) -> [Digest; K] {
    assert_eq!((sk.0, seed.0), (SECRET.0, SEED.0));
    assert_eq!(fields(a), fields(BASE));
    std::array::from_fn(|i| emit(Op::Leaf(K as u32, first + i as u32)))
}
fn wots_leaves_batch<const N: usize>(
    sk: &Digest,
    seed: &Digest,
    first: u32,
    a: Adrs,
) -> [Digest; WIDTH] {
    wots_leaves_small::<N, WIDTH>(sk, seed, first, a)
}
fn pair(packed: bool, seed: &Digest, a: &Adrs, l: &Digest, r: &Digest) -> Digest {
    assert_eq!(seed.0, SEED.0);
    assert_eq!(
        fields(*a),
        fields(
            BASE.with_type(TREE)
                .with_word2(value(*a, 4))
                .with_word3(value(*a, 5))
        )
    );
    emit(Op::Parent(packed, value(*a, 4), value(*a, 5), *l, *r))
}
fn thash_pair<const N: usize>(seed: &Digest, a: &Adrs, l: &Digest, r: &Digest) -> Digest {
    pair(false, seed, a, l, r)
}
fn pair_active<const N: usize>(
    seed: &Digest,
    a: &[Adrs; WIDTH],
    l: &[Digest; WIDTH],
    r: &[Digest; WIDTH],
    active: usize,
) -> [Digest; WIDTH] {
    assert!((1..=WIDTH).contains(&active));
    std::array::from_fn(|i| {
        if i < active {
            pair(true, seed, &a[i], &l[i], &r[i])
        } else {
            EMPTY
        }
    })
}
// PRODUCTION
fn show(ops: &[Op], d: Digest, z: u32, i: u32, out: &mut String) {
    use std::fmt::Write;
    match ops[d.0] {
        Op::Leaf(k, idx) => {
            write!(out, "L {k} {} ", i64::from(idx) - i64::from(i)).unwrap();
        }
        Op::Parent(pack, h, idx, l, r) => {
            write!(
                out,
                "B {} {} {} ",
                pack as u8,
                i64::from(h) - i64::from(z),
                i64::from(idx) - i64::from(i)
            )
            .unwrap();
            assert!(z > 0);
            show(ops, l, z - 1, i * 2, out);
            show(ops, r, z - 1, i * 2 + 1, out);
        }
    }
}
fn check<const N: usize>() {
    for z in 1..=9 {
        let mut common = None;
        for i in 0..(1 << (9 - z)) {
            OPS.with_borrow_mut(|o| o.clear());
            let d = xmss_subtree::<N>(&SECRET, &SEED, i, z, BASE);
            let mut trace = String::new();
            OPS.with_borrow(|o| show(o, d, z, i, &mut trace));
            if let Some(previous) = &common {
                assert_eq!(previous, &trace);
            } else {
                common = Some(trace);
            }
        }
        println!("{N} {z} {}", common.unwrap());
    }
}
fn main() {
    check::<16>();
    check::<24>();
    check::<32>();
}
