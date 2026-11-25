// Compiled with the production builder bodies by check-cache-build.py.
// The layer, tree index and seed bytes are opaque to the lifted builder.
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
static THREADS: AtomicUsize = AtomicUsize::new(1);
static SIMD: AtomicBool = AtomicBool::new(false);
const WIDTH: usize = PROOF_WIDTH;
const WOTS_HASH: u32 = 0;
const TREE: u32 = 2;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Layer {
    Zero,
    Input,
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TreeIndex {
    Zero,
    Input,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Adrs {
    layer: Layer,
    tree: TreeIndex,
    typ: u32,
    keypair: u32,
    word2: u32,
    word3: u32,
}
impl Adrs {
    // ADDRESS_METHODS
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Token {
    Empty,
    Secret(usize),
    Public(usize),
    Node(u32, u32, usize),
}
fn node<const N: usize>(h: u32, i: u32) -> [Token; N] {
    std::array::from_fn(|b| Token::Node(h, i, b))
}
type Seed<const N: usize> = [Token; N];
fn seed_ctx<const N: usize>(seed: &Seed<N>) -> Seed<N> {
    *seed
}
fn base() -> Adrs {
    Adrs::new()
        .with_layer(Layer::Input)
        .with_tree(TreeIndex::Input)
}
fn wots_pk_gen<const N: usize>(sk: &[Token; N], seed: &Seed<N>, a: Adrs) -> [Token; N] {
    assert_eq!(*sk, std::array::from_fn(Token::Secret));
    assert_eq!(*seed, std::array::from_fn(Token::Public));
    assert_eq!(
        a,
        Adrs {
            layer: Layer::Input,
            tree: TreeIndex::Input,
            typ: WOTS_HASH,
            keypair: a.keypair,
            word2: 0,
            word3: 0
        }
    );
    node(0, a.keypair)
}
fn hash2<const N: usize>(seed: &Seed<N>, a: &Adrs, l: &[Token; N], r: &[Token; N]) -> [Token; N] {
    assert_eq!(*seed, std::array::from_fn(Token::Public));
    assert_eq!(
        *a,
        Adrs {
            layer: Layer::Input,
            tree: TreeIndex::Input,
            typ: TREE,
            keypair: 0,
            word2: a.word2,
            word3: a.word3
        }
    );
    assert_eq!(*l, node(a.word2.checked_sub(1).unwrap(), 2 * a.word3));
    assert_eq!(*r, node(a.word2 - 1, 2 * a.word3 + 1));
    node(a.word2, a.word3)
}
mod pool {
    pub fn available_threads() -> usize {
        super::THREADS.load(super::Ordering::Relaxed)
    }
    pub fn execute(workers: usize, scrub: bool, f: &impl Fn()) {
        assert!(workers > 0 && scrub);
        // A worker claims one chunk at a time; this replay drains the queue.
        // The parallel queue theorem handles permutation of claim completions.
        f()
    }
}
// COMMON_FUNCTIONS
mod sha2_ops {
    use super::*;
    // SHA2_FUNCTIONS
}
mod shake_ops {
    use super::*;
    use super::{hash2 as thash_pair, wots_pk_gen as wots_pk_gen_portable};
    mod simd {
        use super::*;
        pub(super) fn available<const N: usize>() -> bool {
            SIMD.load(Ordering::Relaxed)
        }
        fn wots_pk_gen_batch<const N: usize>(
            sk: &[Token; N],
            seed: &Seed<N>,
            a: Adrs,
            keys: [u32; WIDTH],
        ) -> [[Token; N]; WIDTH] {
            assert_eq!(a, base());
            keys.map(|i| wots_pk_gen(sk, seed, a.with_type(WOTS_HASH).with_keypair(i)))
        }
        fn pair<const N: usize>(
            seed: &Seed<N>,
            a: &[Adrs; WIDTH],
            l: &[[Token; N]; WIDTH],
            r: &[[Token; N]; WIDTH],
        ) -> [[Token; N]; WIDTH] {
            std::array::from_fn(|i| hash2(seed, &a[i], &l[i], &r[i]))
        }
        use super::wots_pk_gen as wots_pk_gen_single;
        // SIMD_FUNCTIONS
    }
    pub(super) fn check_nodes<const N: usize>(height: u32, sk: &Seed<N>, pk: &Seed<N>) {
        for z in 0..=height {
            for i in 0..(1 << (height - z)) {
                assert_eq!(simd::xmss_node(sk, i, z, pk, base()), node(z, i));
            }
        }
    }
    // SHAKE_FUNCTIONS
}
fn check<const N: usize>(h: u32) {
    let sk = std::array::from_fn(Token::Secret);
    let pk = std::array::from_fn(Token::Public);
    let expected: Vec<[Token; N]> = (0..=h)
        .flat_map(|z| (0..(1 << (h - z))).map(move |i| node(z, i)))
        .collect();
    shake_ops::check_nodes(h, &sk, &pk);
    // Worker counts above leaves/4 are clamped by the production builder.
    for workers in 1..=(1usize << h) / 4 + 1 {
        THREADS.store(workers, Ordering::Relaxed);
        assert_eq!(
            sha2_ops::build_xmss_tree(h, Layer::Input, TreeIndex::Input, &sk, &pk),
            expected
        );
        for active in [false, true] {
            SIMD.store(active, Ordering::Relaxed);
            assert_eq!(
                shake_ops::build_xmss_tree(h, Layer::Input, TreeIndex::Input, &sk, &pk),
                expected
            );
        }
    }
}
fn main() {
    for h in [3, 9] {
        check::<16>(h);
        check::<24>(h);
    }
    for h in [4, 8] {
        check::<32>(h);
    }
}
