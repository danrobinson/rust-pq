// Cached trees carry their canonical (address, height, seeds) descriptor.
// Cachepath checks the concrete level-contiguous array read separately.
use super::*;
use crate::shake256::parallel::WIDTH;

fn append_auth_path<const N: usize>(
    tree: &[[Token; N]],
    hp: u32,
    index: Word,
    sig: &mut Vec<Token>,
) {
    let cached = decode(tree.last().unwrap());
    assert_eq!(
        (cached.kind, cached.height, cached.idx),
        ("xmss", hp, Word::constant(0))
    );
    let sk: [Token; N] = cached.sk.try_into().unwrap();
    let pk = cached.pk.try_into().unwrap();
    for h in 0..hp {
        sig.extend(xmss_node(&sk, (index >> h) ^ 1, h, &pk, cached.a));
    }
}
// PRODUCTION_ROOT

fn xmss_pk_from_sig<const N: usize>(
    p: &Params,
    leaf: Word,
    sig: &[Token],
    root: &[Token; N],
    pk: &Seed<N>,
    addr: Adrs,
) -> [Token; N] {
    assert_eq!(sig.len(), (p.len() + p.hp as usize) * N);
    let witness = decode(&sig[p.len() * N..(p.len() + 1) * N]);
    let sk: [Token; N] = witness.sk.try_into().unwrap();
    let mut required = wots_sign(root, &sk, pk, addr.with_type(WOTS_HASH).with_keypair(leaf));
    for h in 0..p.hp {
        required.extend(xmss_node(&sk, (leaf >> h) ^ 1, h, pk, addr));
    }
    assert_eq!(sig, required, "invalid XMSS reconstruction input");
    xmss_node(&sk, Word::constant(0), p.hp, pk, addr)
}

fn fors_secrets<const N: usize>(
    sk: &[Token; N],
    seed: &Seed<N>,
    adrs: Adrs,
    indices: [Word; WIDTH],
) -> [[Token; N]; WIDTH] {
    SIMD_CALLS.fetch_add(1, Ordering::Relaxed);
    indices.map(|i| fors_sk_gen(sk, seed, adrs, i))
}
fn fors_nodes<const N: usize>(
    sk: &[Token; N],
    seed: &Seed<N>,
    adrs: Adrs,
    indices: [Word; WIDTH],
    h: u32,
) -> [[Token; N]; WIDTH] {
    indices.map(|i| fors_node(sk, i, h, seed, adrs))
}

mod sha2 {
    use super::*;
    // PRODUCTION_SHA2
}
mod shake {
    use super::fors_node as fors_node_portable;
    use super::*;
    // PRODUCTION_SHAKE
}

pub(super) fn check<const N: usize>(
    p: &Params,
    md: &[Token],
    sk: &[Token; N],
    pk: &Seed<N>,
    adrs: Adrs,
    r: &[Token; N],
    tree: Word,
    leaf: Word,
    expected: &[Token],
) {
    check_layout::<N>(p.hp);
    steps::check(p, sk, pk, adrs);
    packing::check::<N>();
    let cache = |j: u32| {
        // Two distinguishable entries make selecting the first instead of the last observable.
        let addr = Adrs::new()
            .with_layer(j)
            .with_tree((0..j).fold(tree, |index, _| index >> p.hp));
        [*r, xmss_node(sk, Word::constant(0), p.hp, pk, addr)]
    };
    let top = cache(p.d - 1);
    let d2 = cache(p.d - 2);
    for hit in [None, Some(&d2[..])] {
        for (cpus, workers) in [(1, 1), (4, 1), (4, 4)] {
            CPUS.store(cpus, Ordering::Relaxed);
            WORKERS.store(workers, Ordering::Relaxed);
            for (grouped, signer) in [
                (false, sha2::sign_parallel::<N> as Signer<N>),
                (false, shake::sign_parallel::<N>),
                (true, shake::sign_parallel::<N>),
            ] {
                SIMD.store(grouped, Ordering::Relaxed);
                SIMD_CALLS.store(0, Ordering::Relaxed);
                let got = signer(p, md, sk, pk, adrs, r, tree, leaf, &top, hit);
                assert_eq!(
                    SIMD_CALLS.load(Ordering::Relaxed) > 0,
                    cfg!(proof_simd) && grouped && cpus > 1
                );
                assert!(
                    got.as_deref() == (cpus > 1).then_some(expected),
                    "cached symbolic signature differs"
                );
            }
        }
    }
}

type Signer<const N: usize> = fn(
    &Params,
    &[Token],
    &[Token; N],
    &Seed<N>,
    Adrs,
    &[Token; N],
    Word,
    Word,
    &[[Token; N]],
    Option<&[[Token; N]]>,
) -> Option<Vec<Token>>;

mod layout {
    use super::*;
    // PRODUCTION_LAYOUT
    pub(super) fn read<const N: usize>(tree: &[[Token; N]], hp: u32, leaf: u32) -> Vec<Token> {
        let mut sig = Vec::new();
        append_auth_path(tree, hp, leaf, &mut sig);
        sig
    }
}

fn check_layout<const N: usize>(hp: u32) {
    let leaves = 1usize << hp;
    let tree: Vec<[Token; N]> = (0..2 * leaves - 1)
        .map(|i| std::array::from_fn(|j| Token(i, j)))
        .collect();
    for leaf in 0..leaves {
        let mut offset = 0;
        let mut expected = Vec::new();
        for height in 0..hp {
            expected.extend(tree[offset + ((leaf >> height) ^ 1)]);
            offset += leaves >> height;
        }
        assert_eq!(
            layout::read(&tree, hp, leaf as u32),
            expected,
            "cached auth-path byte offset"
        );
    }
    assert_eq!(tree_root(&tree), tree[tree.len() - 1]);
}

// Compare the production SIMD FORS base case and induction step with the
// production portable step. Recursive calls on smaller subtrees denote fresh
// terms keyed by every argument. short/pair use the lane-wise hash contract.
mod steps {
    use super::*;
    use crate::fors_node as fors_node_portable;
    use crate::rust_address::FORS_PRF;

    impl std::ops::Mul<u32> for Word {
        type Output = Word;
        fn mul(self, n: u32) -> Word {
            assert_eq!(n, 2);
            self << 1
        }
    }
    impl std::ops::Mul<Word> for u32 {
        type Output = Word;
        fn mul(self, i: Word) -> Word {
            i * self
        }
    }
    fn thash<const N: usize>(pk: &Seed<N>, a: &Adrs, v: &[Token; N]) -> [Token; N] {
        result(
            Call(
                "short",
                *a,
                Word::constant(0),
                0,
                vec![pk.to_vec(), v.to_vec()],
            ),
            N,
        )
        .try_into()
        .unwrap()
    }
    fn thash_pair<const N: usize>(
        pk: &Seed<N>,
        a: &Adrs,
        l: &[Token; N],
        r: &[Token; N],
    ) -> [Token; N] {
        result(
            Call(
                "pair",
                *a,
                Word::constant(0),
                0,
                vec![pk.to_vec(), l.to_vec(), r.to_vec()],
            ),
            N,
        )
        .try_into()
        .unwrap()
    }
    fn short<const N: usize>(
        pk: &Seed<N>,
        a: &[Adrs; WIDTH],
        v: &[[Token; N]; WIDTH],
    ) -> [[Token; N]; WIDTH] {
        std::array::from_fn(|i| thash(pk, &a[i], &v[i]))
    }
    fn pair<const N: usize>(
        pk: &Seed<N>,
        a: &[Adrs; WIDTH],
        l: &[[Token; N]; WIDTH],
        r: &[[Token; N]; WIDTH],
    ) -> [[Token; N]; WIDTH] {
        std::array::from_fn(|i| thash_pair(pk, &a[i], &l[i], &r[i]))
    }
    // PRODUCTION_STEPS

    pub(super) fn check<const N: usize>(p: &Params, sk: &[Token; N], pk: &Seed<N>, a: Adrs) {
        for h in 0..p.a {
            // 31 independent bits per lane include every possible valid parent index.
            let idx = std::array::from_fn(|i| Word::input(128 + 31 * i as u16, 31));
            let got = group_step(sk, pk, a, idx, h);
            assert_eq!(
                got,
                idx.map(|i| scalar_step(sk, i, h, pk, a)),
                "grouped FORS recurrence"
            );
        }
    }
}

mod packing {
    use super::{result, Call, Token, Word, WIDTH};

    impl Token {
        fn constant(byte: u8) -> Self {
            Self(usize::MAX, byte as usize)
        }
    }
    #[derive(Clone, Copy)]
    struct LaneWord([Token; 8]);
    impl LaneWord {
        fn zero() -> Self {
            Self([Token::constant(0); 8])
        }
        fn domain() -> Self {
            let mut w = Self::zero();
            w.0[0] = Token::constant(0x1f);
            w
        }
        fn from_le_bytes(b: [Token; 8]) -> Self {
            Self(b)
        }
        fn to_le_bytes(self) -> [Token; 8] {
            self.0
        }
    }
    impl std::ops::BitOrAssign<u64> for LaneWord {
        fn bitor_assign(&mut self, rhs: u64) {
            assert_eq!(rhs, 1 << 63);
            assert_eq!(self.0[7], Token::constant(0));
            self.0[7] = Token::constant(0x80);
        }
    }
    struct Adrs([Token; 32]);
    impl Adrs {
        fn full(&self) -> [Token; 32] {
            self.0
        }
    }
    type States = [[LaneWord; WIDTH]; 25];

    fn permutation(bytes: Vec<Token>) -> Vec<Token> {
        assert_eq!(bytes.len(), 200);
        result(
            Call(
                "Keccak-f",
                super::Adrs::new(),
                Word::constant(0),
                0,
                vec![bytes],
            ),
            200,
        )
    }
    mod parallel {
        use super::*;
        pub(super) fn permute(s: &mut States) {
            for lane in 0..WIDTH {
                let output = permutation(s.iter().flat_map(|row| row[lane].0).collect());
                for (row, word) in s.iter_mut().zip(output.chunks_exact(8)) {
                    row[lane] = LaneWord(word.try_into().unwrap());
                }
            }
        }
    }
    // PRODUCTION_PACKING

    pub(super) fn check<const N: usize>() {
        // Each input byte has independent identity, including the 32 serialized address bytes.
        let seed = std::array::from_fn(|i| Token(0, i));
        let addresses =
            std::array::from_fn(|i| Adrs(std::array::from_fn(|j| Token(0, N + i * 32 + j))));
        let left =
            std::array::from_fn(|i| std::array::from_fn(|j| Token(0, N + 32 * WIDTH + i * N + j)));
        let right = std::array::from_fn(|i| {
            std::array::from_fn(|j| Token(0, N + (32 + N) * WIDTH + i * N + j))
        });
        let single = short::<N>(&seed, &addresses, &left);
        let double = pair::<N>(&seed, &addresses, &left, &right);
        for (i, a) in addresses.iter().enumerate() {
            for (extra, got) in [(&[][..], single[i]), (&right[i][..], double[i])] {
                let mut state = Vec::from(seed);
                state.extend(a.full());
                state.extend(left[i]);
                state.extend_from_slice(extra);
                state.push(Token::constant(0x1f));
                state.resize(135, Token::constant(0));
                state.push(Token::constant(0x80));
                state.resize(200, Token::constant(0));
                assert_eq!(
                    got.as_slice(),
                    &permutation(state)[..N],
                    "SHAKE cached lane preimage or output bytes"
                );
            }
        }
    }
}
