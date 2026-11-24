// Model primitive outputs by their FIPS node coordinates. Keep production
// subtree traversal, address operations, buffer sizes, copies and indexing.
#[path = "ADDRESS_PATH"]
mod address;
use address::{Adrs, TREE, WOTS_HASH};
const WIDTH: usize = PROOF_WIDTH;

const BASE: Adrs = Adrs {
    layer: 5,
    tree: 0x172935478192,
    typ: 7,
    keypair: 9,
    word2: 11,
    word3: 13,
};

fn encode<const N: usize>(height: u32, index: u32) -> [u8; N] {
    let mut tag = [0xab; N];
    tag[..4].copy_from_slice(&height.to_be_bytes());
    tag[4..8].copy_from_slice(&index.to_be_bytes());
    tag
}

fn keygen<const N: usize>(sk: &[u8; N], seed: &[u8; N], a: Adrs) -> [u8; N] {
    assert_eq!(*sk, [1; N]);
    assert_eq!(*seed, [2; N]);
    assert_eq!(
        a.full(),
        BASE.with_type(WOTS_HASH).with_keypair(a.keypair).full()
    );
    encode(0, a.keypair)
}

fn wots_leaves_small<const N: usize, const K: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    start: u32,
    a: Adrs,
) -> [[u8; N]; K] {
    assert_eq!(a.full(), BASE.full());
    std::array::from_fn(|i| {
        keygen(
            sk,
            seed,
            a.with_type(WOTS_HASH).with_keypair(start + i as u32),
        )
    })
}

fn wots_leaves_batch<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    start: u32,
    a: Adrs,
) -> [[u8; N]; WIDTH] {
    wots_leaves_small(sk, seed, start, a)
}

fn thash_pair<const N: usize>(seed: &[u8; N], a: &Adrs, l: &[u8; N], r: &[u8; N]) -> [u8; N] {
    assert_eq!(*seed, [2; N]);
    assert_eq!(
        a.full(),
        BASE.with_type(TREE)
            .with_word2(a.word2)
            .with_word3(a.word3)
            .full()
    );
    assert_eq!(*l, encode(a.word2 - 1, 2 * a.word3));
    assert_eq!(*r, encode(a.word2 - 1, 2 * a.word3 + 1));
    encode(a.word2, a.word3)
}

fn pair_active<const N: usize>(
    seed: &[u8; N],
    a: &[Adrs; WIDTH],
    l: &[[u8; N]; WIDTH],
    r: &[[u8; N]; WIDTH],
    active: usize,
) -> [[u8; N]; WIDTH] {
    assert!((1..=WIDTH).contains(&active));
    std::array::from_fn(|i| {
        if i < active {
            thash_pair(seed, &a[i], &l[i], &r[i])
        } else {
            [0; N]
        }
    })
}

// PRODUCTION_TREE

fn check<const N: usize>() {
    for height in 1..=9 {
        for index in 0..1 << (9 - height) {
            assert_eq!(
                xmss_subtree(&[1; N], &[2; N], index, height, BASE),
                encode(height, index)
            );
        }
    }
}

fn main() {
    check::<16>();
    check::<24>();
    check::<32>();
}
