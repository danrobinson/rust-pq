// A symbolic word is a handle to a Lean expression. Rust executes the production
// array updates, loop bounds and macro expansion; no input word is concrete.
use std::{
    cell::RefCell,
    ops::{BitAnd, BitXor, BitXorAssign, Not},
};
thread_local! { static TERMS: RefCell<Vec<String>> = RefCell::default(); }

#[derive(Clone, Copy)]
struct Word(usize);
impl Word {
    fn term(s: String) -> Self {
        TERMS.with(|ts| {
            let mut ts = ts.borrow_mut();
            ts.push(s);
            Word(ts.len() - 1)
        })
    }
    fn expr(self) -> String {
        TERMS.with(|ts| ts.borrow()[self.0].clone())
    }
    fn rotate_left(self, n: u32) -> Self {
        Word::term(format!("(BitVec.rotateLeft {} {n})", self.expr()))
    }
}
impl BitXor for Word {
    type Output = Self;
    fn bitxor(self, b: Self) -> Self {
        Word::term(format!("({} ^^^ {})", self.expr(), b.expr()))
    }
}
impl BitXorAssign for Word {
    fn bitxor_assign(&mut self, b: Self) {
        *self = *self ^ b;
    }
}
impl Not for Word {
    type Output = Self;
    fn not(self) -> Self {
        Word::term(format!("(~~~{})", self.expr()))
    }
}
impl BitAnd for Word {
    type Output = Self;
    fn bitand(self, b: Self) -> Self {
        Word::term(format!("({} &&& {})", self.expr(), b.expr()))
    }
}

// ARM intrinsic semantics projected onto either 64-bit vector element.
type V = Word;
fn veor3q_u64(a: V, b: V, c: V) -> V {
    a ^ b ^ c
}
fn veorq_u64(a: V, b: V) -> V {
    a ^ b
}
fn vrax1q_u64(a: V, b: V) -> V {
    a ^ b.rotate_left(1)
}
fn vxarq_u64<const N: u32>(a: V, b: V) -> V {
    (a ^ b).rotate_left((64 - N) % 64)
}
fn vbcaxq_u64(a: V, b: V, c: V) -> V {
    a ^ (b & !c)
}
fn vdupq_n_u64(a: Word) -> V {
    a
}

fn vbicq_u64(a: V, b: V) -> V {
    a & !b
}
fn vshlq_n_u64<const N: u32>(a: V) -> V {
    Word::term(format!("({} <<< ({N} : Nat))", a.expr()))
}
fn vsriq_n_u64<const N: u32>(a: V, b: V) -> V {
    Word::term(format!(
        "(({} &&& ((-1 : BitVec 64) <<< ({} : Nat))) ||| ({} >>> ({N} : Nat)))",
        a.expr(),
        64 - N,
        b.expr()
    ))
}

// PRODUCTION

fn main() {
    let a = std::array::from_fn(|i| Word::term(format!("a[{i}]!")));
    let c = Word::term("c".into());
    let mut scalar = a;
    round_scalar(&mut scalar, c);
    for state in [
        scalar,
        unsafe { round_inplace(a, c) },
        unsafe { round(a, c) },
        unsafe { neon::round(a, c) },
    ] {
        for w in state {
            println!("{}", w.expr());
        }
    }
}
