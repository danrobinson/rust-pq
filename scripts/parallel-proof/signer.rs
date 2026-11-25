// Symbolic evaluator for the production signer's byte copies and tree addresses.
// A bit is either a constant (0/1), a distinct input bit, or its complement.
use std::collections::HashMap;
use std::ops::{BitAnd, BitXor, Shr, ShrAssign};
use std::sync::{
    atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering},
    Condvar, Mutex, OnceLock,
};

#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
struct Word([u16; 64]);
impl Word {
    fn constant(value: u32) -> Self {
        Self(std::array::from_fn(|i| {
            if i < 32 {
                ((value >> i) & 1) as u16
            } else {
                0
            }
        }))
    }
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

impl std::ops::Shl<u32> for Word {
    type Output = Self;
    fn shl(self, shift: u32) -> Self {
        assert!(shift < 32);
        assert!(self.0[(32 - shift) as usize..].iter().all(|&b| b == 0));
        Self(std::array::from_fn(|i| {
            if i < shift as usize {
                0
            } else {
                self.0[i - shift as usize]
            }
        }))
    }
}
impl std::ops::Add<Word> for Word {
    type Output = Self;
    fn add(self, rhs: Word) -> Self {
        Self(std::array::from_fn(|i| {
            // All additions in these address expressions concatenate disjoint fields.
            assert!(self.0[i] == 0 || rhs.0[i] == 0);
            self.0[i] | rhs.0[i]
        }))
    }
}
impl std::ops::Add<u32> for Word {
    type Output = Self;
    fn add(self, rhs: u32) -> Self {
        self + Word::constant(rhs)
    }
}
impl std::ops::Add<Word> for u32 {
    type Output = Word;
    fn add(self, rhs: Word) -> Word {
        Word::constant(self) + rhs
    }
}
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
struct Adrs {
    layer: u32,
    tree: Word,
    typ: u32,
    keypair: Word,
    height: u32,
    index: Word,
}
impl Adrs {
    fn new() -> Self {
        Self {
            layer: 0,
            tree: Word([0; 64]),
            typ: 0,
            height: 0,
            index: Word::constant(0),
            keypair: Word([0; 64]),
        }
    }
    fn with_word2(self, height: u32) -> Self {
        Self { height, ..self }
    }
    fn with_word3(self, index: Word) -> Self {
        Self { index, ..self }
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
            height: 0,
            index: Word::constant(0),
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
use rust_address::{TREE, WOTS_HASH};
fn fors_sign<const N: usize>(
    p: &Params,
    m: &[Token],
    sk: &[Token; N],
    pk: &Seed<N>,
    a: Adrs,
) -> Vec<Token> {
    let mut sig = Vec::new();
    for t in 0..p.k {
        let digit = digit(p.a, t as usize);
        let prefix = t << p.a;
        sig.extend(fors_sk_gen(sk, pk, a, prefix + digit));
        for h in 0..p.a {
            // Reference extracts sibling bits directly from the original digit.
            let idx = Word(std::array::from_fn(|b| {
                if b >= (p.a - h) as usize {
                    Word::constant(t << (p.a - h)).0[b]
                } else {
                    digit.0[b + h as usize] ^ u16::from(b == 0)
                }
            }));
            sig.extend(fors_node(sk, idx, h, pk, a));
        }
    }
    assert_eq!(m.len(), p.md_bytes());
    sig
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
    node("xmss", sk, i, h, pk, a)
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

fn digit(bits: u32, t: usize) -> Word {
    Word::input((128 + t * bits as usize).try_into().unwrap(), bits as usize)
}
fn base_2b(m: &[Token], a: u32, k: usize) -> Vec<Word> {
    let expected: Vec<_> = (0..(a as usize * k).div_ceil(8))
        .map(|i| Token(0, 96 + i))
        .collect();
    assert_eq!(m, expected);
    (0..k).map(|t| digit(a, t)).collect()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Node {
    kind: &'static str,
    idx: Word,
    height: u32,
    a: Adrs,
    sk: Vec<Token>,
    pk: Vec<Token>,
}
static NODES: OnceLock<Mutex<HashMap<usize, Node>>> = OnceLock::new();
fn node<const N: usize>(
    kind: &'static str,
    sk: &[Token; N],
    idx: Word,
    h: u32,
    pk: &Seed<N>,
    a: Adrs,
) -> [Token; N] {
    let args = vec![sk.to_vec(), pk.to_vec()];
    let bytes = result(Call(kind, a, idx, h, args), N);
    let descriptor = Node {
        kind,
        idx,
        height: h,
        a,
        sk: sk.to_vec(),
        pk: pk.to_vec(),
    };
    NODES
        .get_or_init(Default::default)
        .lock()
        .unwrap()
        .insert(bytes[0].0, descriptor);
    bytes.try_into().unwrap()
}
fn decode(bytes: &[Token]) -> Node {
    let id = bytes[0].0;
    assert!(bytes.iter().enumerate().all(|(i, t)| *t == Token(id, i)));
    NODES.get().unwrap().lock().unwrap()[&id].clone()
}
fn fors_node<const N: usize>(
    sk: &[Token; N],
    i: Word,
    h: u32,
    pk: &Seed<N>,
    a: Adrs,
) -> [Token; N] {
    node("fors", sk, i, h, pk, a)
}
fn fors_sk_gen<const N: usize>(sk: &[Token; N], pk: &Seed<N>, a: Adrs, i: Word) -> [Token; N] {
    result(
        Call("fors secret", a, i, 0, vec![sk.to_vec(), pk.to_vec()]),
        N,
    )
    .try_into()
    .unwrap()
}
fn parent<const N: usize>(pk: &Seed<N>, a: &Adrs, l: Node, r: Node) -> [Token; N] {
    let idx = a.index;
    assert_eq!(l.idx, idx << 1);
    assert_eq!(
        r,
        Node {
            idx: (idx << 1) + 1,
            ..l.clone()
        }
    );
    assert_eq!(pk.as_slice(), l.pk);
    let base = if l.kind == "xmss" {
        l.a.with_type(TREE)
    } else {
        l.a
    };
    assert_eq!(*a, base.with_word2(l.height + 1).with_word3(idx));
    node(
        l.kind,
        l.sk.as_slice().try_into().unwrap(),
        idx,
        l.height + 1,
        pk,
        l.a,
    )
}
fn hash2<const N: usize>(pk: &Seed<N>, a: &Adrs, l: &[Token; N], r: &[Token; N]) -> [Token; N] {
    parent(pk, a, decode(l), decode(r))
}
// Split on the actual low bit. In the left branch the signing leaf is
// even; in the right branch its sibling is even. Both calls have the same parent.
fn climb_step<const N: usize>(
    index: Word,
    pk: &Seed<N>,
    a: &Adrs,
    value: &[Token; N],
    sibling: &[Token; N],
) -> [Token; N] {
    let mut me = decode(value);
    let mut other = decode(sibling);
    assert_eq!(me.idx, index);
    assert_eq!(other.idx, index ^ 1);
    let mut answer = None;
    for odd in [false, true] {
        if index.0[0] <= 1 && index.0[0] != u16::from(odd) {
            continue;
        }
        me.idx.0[0] = u16::from(odd);
        other.idx.0[0] = u16::from(!odd);
        let (l, r) = if odd { (&other, &me) } else { (&me, &other) };
        let out = parent(pk, a, l.clone(), r.clone());
        if let Some(old) = answer {
            assert_eq!(old, out);
        }
        answer = Some(out);
    }
    answer.unwrap()
}
type Journal = std::collections::BTreeMap<(usize, &'static str, usize), Vec<Token>>;
static JOURNAL: Mutex<Journal> = Mutex::new(Journal::new());
static REFERENCE: Mutex<Option<Journal>> = Mutex::new(None);

fn record_write(ticket: usize, table: &'static str, slot: usize, value: &[Token]) -> usize {
    let replaced = JOURNAL.lock().unwrap().insert((ticket, table, slot), value.to_vec());
    assert!(replaced.is_none(), "ticket published its cell twice");
    slot
}

fn check_ledger(
    tickets: usize, xmss: usize, leaves: usize, direct: usize, split: usize,
    reserved: impl Iterator<Item = usize>,
) {
    let journal = std::mem::take(&mut *JOURNAL.lock().unwrap());
    let mut cells = std::collections::BTreeSet::new();
    let mut issued = std::collections::BTreeSet::new();
    for &(ticket, table, slot) in journal.keys() {
        assert!(cells.insert((table, slot)), "two tickets own the same cell");
        issued.insert(ticket);
    }
    assert!(issued.into_iter().eq(0..tickets));
    let reserved: Vec<_> = reserved.collect();
    for &slot in &reserved {
        assert!(cells.insert(("fors_direct", slot)), "reducer overlaps a publication");
    }
    let mut expected = std::collections::BTreeSet::new();
    for (table, len) in [("xmss_slots", xmss), ("leaf_pks", leaves),
                         ("fors_direct", direct), ("fors_split", split)] {
        expected.extend((0..len).map(|slot| (table, slot)));
    }
    assert_eq!(cells, expected);
    if std::env::var_os("RUST_PQ_SIGNING_CERTIFICATE").is_some()
        && WORKERS.load(Ordering::Relaxed) == 1 {
        let mut rows = vec![Vec::new(); tickets];
        for &(ticket, table, slot) in journal.keys() {
            let offset = match table {
                "xmss_slots" => 0,
                "leaf_pks" => xmss,
                "fors_direct" => xmss + leaves,
                "fors_split" => xmss + leaves + direct,
                _ => unreachable!(),
            };
            rows[ticket].push(offset + slot);
        }
        let reducer: Vec<_> = reserved.iter().map(|s| xmss + leaves + s).collect();
        println!("LEAF_RANGE {} {}", xmss, leaves);
        println!("LEDGER {} {} {:?}|{:?}", PROOF_WIDTH, expected.len(), rows, reducer);
    }
    let mut reference = REFERENCE.lock().unwrap();
    if let Some(previous) = reference.as_ref() {
        assert_eq!(previous, &journal, "ticket writes depended on the worker schedule");
    } else {
        *reference = Some(journal);
    }
}

static CPUS: AtomicUsize = AtomicUsize::new(2);
mod pool {
    pub fn available_threads() -> usize {
        super::CPUS.load(super::Ordering::Relaxed)
    }
    pub fn execute<F: Fn() + Sync>(max: usize, scrub: bool, f: &F) {
        assert!(scrub);
        std::thread::scope(|scope| {
            for _ in 1..max.min(super::WORKERS.load(super::Ordering::Relaxed)) {
                scope.spawn(f);
            }
            f();
        })
    }
}

mod shake256 {
    pub mod parallel {
        pub const WIDTH: usize = PROOF_WIDTH;
    }
}
mod batch {
    pub fn available<const N: usize>() -> bool {
        super::SIMD.load(super::Ordering::Relaxed)
    }
}
static WORKERS: AtomicUsize = AtomicUsize::new(1);
static SIMD_CALLS: AtomicUsize = AtomicUsize::new(0);
static SIMD: AtomicBool = AtomicBool::new(false);
mod shake_fors_simd {
    use super::*;
    use shake256::parallel::WIDTH;
    pub fn secrets<const N: usize>(
        sk: &[Token; N],
        seed: &Seed<N>,
        a: Adrs,
        idx: [Word; WIDTH],
        active: usize,
    ) -> [[Token; N]; WIDTH] {
        SIMD_CALLS.fetch_add(1, Ordering::Relaxed);
        std::array::from_fn(|i| {
            if i < active {
                fors_sk_gen(sk, seed, a, idx[i])
            } else {
                [Token(0, usize::MAX); N]
            }
        })
    }
    pub fn nodes_active<const N: usize>(
        sk: &[Token; N],
        seed: &Seed<N>,
        a: Adrs,
        idx: [Word; WIDTH],
        active: usize,
        h: u32,
    ) -> [[Token; N]; WIDTH] {
        std::array::from_fn(|i| {
            if i < active {
                fors_node(sk, idx[i], h, seed, a)
            } else {
                [Token(0, usize::MAX); N]
            }
        })
    }
}
macro_rules! shake_only { ($($item:tt)*)=> {$($item)*}; }
mod algorithm {
    pub mod production {
        use super::super::*;
        // PRODUCTION_SIGNER
    }
}

mod cached {
    // CACHED_HARNESS
}

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
    let l = Word::input(64, p.hp as usize);
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
        root = xmss_node(&sk, Word::constant(0), p.hp, &pk, a);
        expected.extend(part);
    }
    cached::check(p, &md, &sk, &pk, fors_addr, &r, t, l, &expected);
    for (cpus, workers, simd) in [
        (1, 1, false),
        (2, 1, false),
        (4, 4, false),
        (2, 1, true),
        (4, 4, true),
    ] {
        if workers == 1 { *REFERENCE.lock().unwrap() = None; }
        WORKERS.store(workers, Ordering::Relaxed);
        SIMD_CALLS.store(0, Ordering::Relaxed);
        CPUS.store(cpus, Ordering::Relaxed);
        SIMD.store(simd, Ordering::Relaxed);
        let got = algorithm::production::sign(p, &md, &sk, &pk, fors_addr, &r, t, l);
        assert_eq!(SIMD_CALLS.load(Ordering::Relaxed) > 0, simd);
        if cpus < 2 {
            assert!(got.is_none());
        } else {
            assert!(
                got.as_deref() == Some(expected.as_slice()),
                "symbolic signature differs"
            );
        }
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
