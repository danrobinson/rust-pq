// Symbolic evaluator for the production signer's byte copies and tree addresses.
// A bit is either a constant (0/1), a distinct input bit, or its complement.
use std::collections::HashMap;
use std::ops::{BitAnd, BitXor, Shr, ShrAssign};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Mutex, OnceLock,
};

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
struct Word([u16; 64]);
impl Word {
    fn input(first: u16, bits: usize) -> Self {
        Self(std::array::from_fn(|i| {
            if i < bits {
                2 * (first + i as u16 + 1)
            } else {
                0
            }
        }))
    }
    fn low32(self) -> Self {
        self & u64::from(u32::MAX)
    }
}
impl BitAnd<u64> for Word {
    type Output = Self;
    fn bitand(self, mask: u64) -> Self {
        Self(std::array::from_fn(|i| {
            if mask >> i & 1 == 1 {
                self.0[i]
            } else {
                0
            }
        }))
    }
}
impl BitXor<u64> for Word {
    type Output = Self;
    fn bitxor(self, mask: u64) -> Self {
        Self(std::array::from_fn(|i| {
            self.0[i] ^ ((mask >> i) & 1) as u16
        }))
    }
}
impl Shr<u32> for Word {
    type Output = Self;
    fn shr(self, n: u32) -> Self {
        assert!(n < 64);
        Self(std::array::from_fn(|i| {
            *self.0.get(i + n as usize).unwrap_or(&0)
        }))
    }
}
impl ShrAssign<u32> for Word {
    fn shr_assign(&mut self, n: u32) {
        *self = *self >> n;
    }
}

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
struct Adrs {
    layer: u32,
    tree: Word,
    typ: u32,
    keypair: Word,
}
impl Adrs {
    fn new() -> Self {
        Self {
            layer: 0,
            tree: Word([0; 64]),
            typ: 0,
            keypair: Word([0; 64]),
        }
    }
    fn with_layer(self, layer: u32) -> Self {
        Self { layer, ..self }
    }
    fn with_tree(self, tree: Word) -> Self {
        Self { tree, ..self }
    }
    fn with_type(self, typ: u32) -> Self {
        Self {
            typ,
            keypair: Word([0; 64]),
            ..self
        }
    }
    fn with_keypair(self, keypair: Word) -> Self {
        Self { keypair, ..self }
    }
}

// A token is one byte of an uninterpreted primitive result. HashMap uses
// structural equality on the complete call including every input byte.
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
struct Token(usize, usize);
type Seed<const N: usize> = [Token; N];
#[derive(Hash, Eq, PartialEq)]
struct Call(&'static str, Adrs, Word, u32, Vec<Vec<Token>>);
fn result(call: Call, n: usize) -> Vec<Token> {
    static TERMS: OnceLock<Mutex<HashMap<Call, usize>>> = OnceLock::new();
    let mut terms = TERMS.get_or_init(Default::default).lock().unwrap();
    let fresh = terms.len() + 1;
    let id = *terms.entry(call).or_insert(fresh);
    (0..n).map(|i| Token(id, i)).collect()
}
#[path = "PARAMS_PATH"]
mod params;
use params::Params;
#[path = "ADDRESS_PATH"]
mod rust_address;
use rust_address::WOTS_HASH;
fn fors_sign<const N: usize>(
    p: &Params,
    m: &[Token],
    sk: &[Token; N],
    pk: &Seed<N>,
    a: Adrs,
) -> Vec<Token> {
    result(
        Call(
            "fors",
            a,
            Word([0; 64]),
            0,
            vec![m.to_vec(), sk.to_vec(), pk.to_vec()],
        ),
        (p.a + 1) as usize * p.k as usize * N,
    )
}
fn fors_pk_from_sig<const N: usize>(
    _: &Params,
    s: &[Token],
    m: &[Token],
    pk: &Seed<N>,
    a: Adrs,
) -> [Token; N] {
    result(
        Call(
            "fors root",
            a,
            Word([0; 64]),
            0,
            vec![s.to_vec(), m.to_vec(), pk.to_vec()],
        ),
        N,
    )
    .try_into()
    .unwrap()
}
fn xmss_node<const N: usize>(
    sk: &[Token; N],
    i: Word,
    h: u32,
    pk: &Seed<N>,
    a: Adrs,
) -> [Token; N] {
    result(Call("node", a, i, h, vec![sk.to_vec(), pk.to_vec()]), N)
        .try_into()
        .unwrap()
}
fn wots_sign<const N: usize>(
    root: &[Token; N],
    sk: &[Token; N],
    pk: &Seed<N>,
    a: Adrs,
) -> Vec<Token> {
    result(
        Call(
            "wots",
            a,
            Word([0; 64]),
            0,
            vec![root.to_vec(), sk.to_vec(), pk.to_vec()],
        ),
        (2 * N + 3) * N,
    )
}
fn xmss_pk_from_sig<const N: usize>(
    _: &Params,
    i: Word,
    s: &[Token],
    root: &[Token; N],
    pk: &Seed<N>,
    a: Adrs,
) -> [Token; N] {
    result(
        Call(
            "xmss root",
            a,
            i,
            0,
            vec![s.to_vec(), root.to_vec(), pk.to_vec()],
        ),
        N,
    )
    .try_into()
    .unwrap()
}

// Boundaries of the host runtime. Real scoped threads still join before the
// result is assembled. The controls exercise absent CPUs and failed spawns.
static CPUS: AtomicUsize = AtomicUsize::new(2);
static SPAWNS: AtomicUsize = AtomicUsize::new(0);
mod runtime {
    use super::{Ordering, CPUS, SPAWNS};
    pub use std::thread::scope;
    use std::{io, num::NonZeroUsize, thread};
    pub fn available_parallelism() -> io::Result<NonZeroUsize> {
        NonZeroUsize::new(CPUS.load(Ordering::Relaxed)).ok_or_else(|| io::Error::other("no count"))
    }
    pub struct Builder;
    impl Builder {
        pub fn new() -> Self {
            Self
        }
        pub fn spawn_scoped<'s, 'e, F>(
            self,
            scope: &'s thread::Scope<'s, 'e>,
            f: F,
        ) -> io::Result<thread::ScopedJoinHandle<'s, ()>>
        where
            F: FnOnce() + Send + 's,
        {
            SPAWNS
                .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_sub(1))
                .map_err(|_| io::Error::other("spawn unavailable"))?;
            thread::Builder::new().spawn_scoped(scope, f)
        }
    }
}
mod production {
    use super::runtime as thread;
    use super::*;
    // PRODUCTION_SIGNER
}

// Independently assemble in FIPS layer order, obtaining address bits directly
// from the initial indices. Earlier layers are never read from the worker table.
fn check<const N: usize>(p: &Params, row: (u32, u32, u32, u32, u32, usize)) {
    assert_eq!(p.n, N);
    assert_eq!((p.h, p.d, p.hp, p.a, p.k, p.m), row);
    fn input<const N: usize>(k: usize) -> [Token; N] {
        std::array::from_fn(|i| Token(0, k + i))
    }
    let sk = input::<N>(0);
    let pk = input::<N>(32);
    let r = input::<N>(64);
    let md: Vec<_> = (0..p.md_bytes()).map(|i| Token(0, 96 + i)).collect();
    let t = Word::input(0, 64);
    let l = Word::input(64, 32);
    let fors_addr = Adrs::new().with_tree(t).with_type(3).with_keypair(l);
    let fors = fors_sign(p, &md, &sk, &pk, fors_addr);
    let mut root = fors_pk_from_sig(p, &fors, &md, &pk, fors_addr);
    let mut expected = r.to_vec();
    expected.extend(fors);
    for j in 0..p.d {
        let hp = p.hp as usize;
        let tree = Word(std::array::from_fn(|i| {
            *t.0.get(i + j as usize * hp).unwrap_or(&0)
        }));
        let leaf = if j == 0 {
            l
        } else {
            Word(std::array::from_fn(|i| {
                if i < hp {
                    t.0[(j as usize - 1) * hp + i]
                } else {
                    0
                }
            }))
        };
        let a = Adrs::new().with_layer(j).with_tree(tree);
        let mut part = wots_sign(&root, &sk, &pk, a.with_type(0).with_keypair(leaf));
        for h in 0..hp {
            let idx = Word(std::array::from_fn(|i| {
                *leaf.0.get(i + h).unwrap_or(&0) ^ u16::from(i == 0)
            }));
            part.extend(xmss_node(&sk, idx, h as u32, &pk, a));
        }
        root = xmss_pk_from_sig(p, leaf, &part, &root, &pk, a);
        expected.extend(part);
    }
    for (cpus, spawn_limit) in [(0, 0), (1, 0), (2, 0), (2, 1), (16, 1), (64, 64)] {
        CPUS.store(cpus, Ordering::Relaxed);
        SPAWNS.store(spawn_limit, Ordering::Relaxed);
        let got = production::sign(p, &md, &sk, &pk, fors_addr, &r, t, l);
        if cpus < 2 {
            assert!(got.is_none());
            continue;
        }
        assert!(
            got.as_deref() == Some(&expected[..]),
            "symbolic signature differs"
        );
    }
    println!(
        "n={N}, d={}: all {} symbolic output bytes agree",
        p.d,
        expected.len()
    );
}
fn main() {
    check::<16>(&params::SHA2_128S, (63, 7, 9, 12, 14, 30));
    check::<16>(&params::SHA2_128F, (66, 22, 3, 6, 33, 34));
    check::<24>(&params::SHA2_192S, (63, 7, 9, 14, 17, 39));
    check::<24>(&params::SHA2_192F, (66, 22, 3, 8, 33, 42));
    check::<32>(&params::SHA2_256S, (64, 8, 8, 14, 22, 47));
    check::<32>(&params::SHA2_256F, (68, 17, 4, 9, 35, 49));
}
