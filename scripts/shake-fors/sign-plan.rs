// The production signer writes symbols into its actual slices. All index expressions
// are retained as syntax, including the independent selection variable for each tree.
#![allow(dead_code)]
extern crate alloc;
use std::cell::RefCell;
use std::ops::{Add, BitXor, Mul, Shr};
#[path = "PARAMS_PATH"]
mod params;
use params::{Params, K_MAX};
const WIDTH: usize = PROOF_WIDTH;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Expr(usize);
thread_local! {
    static TERMS: RefCell<Vec<String>> = RefCell::new(vec!["(.lit 0)".into()]);
    static BLOCKS: RefCell<Vec<(String,Expr)>> = const { RefCell::new(Vec::new()) };
}
fn term(body: String) -> Expr {
    TERMS.with_borrow_mut(|terms| {
        terms.push(body);
        Expr(terms.len() - 1)
    })
}
impl Expr {
    fn show(self) -> String {
        TERMS.with_borrow(|terms| terms[self.0].clone())
    }
}
impl Add<Expr> for u32 {
    type Output = Expr;
    fn add(self, x: Expr) -> Expr {
        term(format!("(.add (.lit {self}) {})", x.show()))
    }
}
impl Add<u32> for Expr {
    type Output = Expr;
    fn add(self, x: u32) -> Expr {
        term(format!("(.add {} (.lit {x}))", self.show()))
    }
}
impl Shr<u32> for Expr {
    type Output = Expr;
    fn shr(self, x: u32) -> Expr {
        term(format!("(.shr {} {x})", self.show()))
    }
}
impl BitXor<u32> for Expr {
    type Output = Expr;
    fn bitxor(self, x: u32) -> Expr {
        term(format!("(.xor {} {x})", self.show()))
    }
}
impl Mul<Expr> for u32 {
    type Output = Expr;
    fn mul(self, x: Expr) -> Expr {
        term(format!("(.mul {self} {})", x.show()))
    }
}
const FORS_PRF: u32 = 6;
const FORS_TREE: u32 = 3;
#[derive(Clone, Copy)]
struct Adrs {
    typ: u32,
    keypair: u32,
    height: u32,
    word3: Expr,
}
impl Adrs {
    fn with_type(self, typ: u32) -> Self {
        Self {
            typ,
            keypair: 0,
            height: 0,
            word3: Expr(0),
        }
    }
    fn with_keypair(self, keypair: u32) -> Self {
        Self { keypair, ..self }
    }
    fn with_word2(self, height: u32) -> Self {
        Self { height, ..self }
    }
    fn with_word3(self, word3: Expr) -> Self {
        Self { word3, ..self }
    }
    fn check(self, typ: u32) {
        assert_eq!((self.typ, self.keypair), (typ, 123))
    }
}
// Every byte carries a (producer,offset) label. Padding, unwritten or swapped bytes
// cannot masquerade as a correctly copied hash result.
fn block<const N: usize>(op: String, index: Expr) -> [usize; N] {
    let id = BLOCKS.with_borrow_mut(|b| {
        b.push((op, index));
        b.len()
    });
    core::array::from_fn(|j| id * 64 + j)
}
fn inspect<const N: usize>(b: &[usize; N]) -> (String, Expr) {
    let id = b[0] / 64;
    assert!(id > 0);
    for (j, v) in b.iter().enumerate() {
        assert_eq!(*v, id * 64 + j)
    }
    BLOCKS.with_borrow(|blocks| blocks[id - 1].clone())
}
fn keys<const N: usize>(sk: &[usize; N], seed: &[usize; N]) {
    assert_eq!(sk, &[1; N]);
    assert_eq!(seed, &[2; N]);
}
fn short_active<const N: usize>(
    seed: &[usize; N],
    addresses: &[Adrs; WIDTH],
    keys_in: &[[usize; N]; WIDTH],
    active: usize,
) -> [[usize; N]; WIDTH] {
    assert!((1..=WIDTH).contains(&active));
    core::array::from_fn(|j| {
        if j < active {
            keys(&keys_in[j], seed);
            addresses[j].check(FORS_PRF);
            assert_eq!(addresses[j].height, 0);
            block("secret".into(), addresses[j].word3)
        } else {
            [0; N]
        }
    })
}
fn node<const N: usize>(
    sk: &[usize; N],
    seed: &[usize; N],
    a: Adrs,
    i: Expr,
    h: u32,
) -> [usize; N] {
    keys(sk, seed);
    a.check(FORS_TREE);
    block(format!("node {h}"), i)
}
fn fors_subtree_horiz<const N: usize>(
    sk: &[usize; N],
    seed: &[usize; N],
    a: Adrs,
    i: Expr,
    h: u32,
) -> [usize; N] {
    assert!(h >= 3 && WIDTH == 8);
    node(sk, seed, a, i, h)
}
fn nodes_fallback<const N: usize>(
    sk: &[usize; N],
    seed: &[usize; N],
    a: Adrs,
    indices: [Expr; WIDTH],
    h: u32,
    active: usize,
) -> [[usize; N]; WIDTH] {
    assert!((1..=WIDTH).contains(&active));
    core::array::from_fn(|j| {
        if j < active {
            node(sk, seed, a, indices[j], h)
        } else {
            [0; N]
        }
    })
}
fn fors_leaves_fused<const N: usize>(
    sk: &[usize; N],
    seed: &[usize; N],
    a: Adrs,
    indices: &[Expr; WIDTH],
    active: usize,
) -> [[usize; N]; WIDTH] {
    assert!((1..=WIDTH).contains(&active));
    core::array::from_fn(|j| {
        if j < active {
            node(sk, seed, a, indices[j], 0)
        } else {
            [0; N]
        }
    })
}
fn pair_active<const N: usize>(
    seed: &[usize; N],
    addrs: &[Adrs; WIDTH],
    left: &[[usize; N]; WIDTH],
    right: &[[usize; N]; WIDTH],
    active: usize,
) -> [[usize; N]; WIDTH] {
    assert_eq!(seed, &[2; N]);
    assert!((1..=WIDTH).contains(&active));
    core::array::from_fn(|j| {
        if j >= active {
            return [0; N];
        }
        let a = addrs[j];
        a.check(FORS_TREE);
        for (side, child) in [&left[j], &right[j]].iter().enumerate() {
            let (op, idx) = inspect(child);
            assert_eq!(op, format!("node {}", a.height - 1));
            println!("child {} {} {}", idx.show(), a.word3.show(), side);
        }
        block(format!("node {}", a.height), a.word3)
    })
}
// PRODUCTION_SIGN
fn probe<const N: usize>(name: &str, p: &Params) {
    println!("set {name}");
    let choices: Vec<_> = (0..p.k).map(|j| term(format!("(.sel {j})"))).collect();
    let a = Adrs {
        typ: FORS_TREE,
        keypair: 123,
        height: 0,
        word3: Expr(0),
    };
    let sig = sign(p, &choices, &[1; N], &[2; N], a);
    assert_eq!(sig.len(), p.k as usize * (1 + p.a as usize) * N);
    for row in sig.chunks_exact(N) {
        let (op, index) = inspect::<N>(row.try_into().unwrap());
        println!("block ({op}) {}", index.show())
    }
}
fn main() {
    probe::<16>("128s", &params::SHA2_128S);
    probe::<16>("128f", &params::SHA2_128F);
    probe::<24>("192s", &params::SHA2_192S);
    probe::<24>("192f", &params::SHA2_192F);
    probe::<32>("256s", &params::SHA2_256S);
    probe::<32>("256f", &params::SHA2_256F);
}
