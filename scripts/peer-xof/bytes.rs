// Included inside the published peer's address module so every private field is visible.
use super::*;
use crate::{PkSeed, SkPrf, SkSeed};

fn encoding<T: Address>(a: T, words: [u32; 8]) {
    let bytes = a.as_ref();
    assert!(bytes.len() == 32);
    for i in 0..32 {
        assert!(bytes[i] == (words[i / 4] >> (24 - 8 * (i % 4))) as u8);
    }
}
#[kani::proof]
#[kani::unwind(35)]
fn check_all_address_encodings() {
    let [layer, high, tree_high, tree_low, key, height, index] = kani::any::<[u32; 7]>();
    let tree = ((tree_high as u64) << 32) | tree_low as u64;
    let mut w = WotsHash::default();
    w.layer_adrs.set(layer);
    w.tree_adrs_high.set(high);
    w.tree_adrs_low.set(tree);
    w.key_pair_adrs.set(key);
    w.chain_adrs.set(height);
    w.hash_adrs.set(index);
    encoding(
        w.clone(),
        [layer, high, tree_high, tree_low, 0, key, height, index],
    );
    encoding(
        w.pk_adrs(),
        [layer, high, tree_high, tree_low, 1, key, 0, 0],
    );
    let mut h = w.tree_adrs();
    h.tree_height.set(height);
    h.tree_index.set(index);
    encoding(h, [layer, high, tree_high, tree_low, 2, 0, height, index]);
    let mut p = w.prf_adrs();
    p.chain_adrs.set(height);
    encoding(p, [layer, high, tree_high, tree_low, 5, key, height, 0]);

    let mut f = ForsTree::new(tree, key);
    f.tree_adrs_high.set(high);
    f.tree_height.set(height);
    f.tree_index.set(index);
    encoding(
        f.clone(),
        [0, high, tree_high, tree_low, 3, key, height, index],
    );
    encoding(f.fors_roots(), [0, high, tree_high, tree_low, 4, key, 0, 0]);
    encoding(
        f.prf_adrs(),
        [0, high, tree_high, tree_low, 6, key, 0, index],
    );
}

macro_rules! bytes {
    ($n:literal) => {{
        type Size = typenum::U<$n>;
        let raw: [u8; $n] = kani::any();
        let a = hybrid_array::Array::<u8, Size>(raw);
        assert_eq!(a.as_slice(), &raw);
        let p = PkSeed(a);
        let s = SkSeed(a);
        let k = SkPrf(a);
        assert_eq!(p.as_ref(), &raw);
        assert_eq!(s.as_ref(), &raw);
        assert_eq!(k.as_ref(), &raw);
        let mut output = hybrid_array::Array::<u8, Size>::default();
        output.as_mut_slice().copy_from_slice(&raw);
        assert_eq!(output.0, raw);
    }};
}
#[kani::proof]
#[kani::unwind(68)]
fn check_byte_views() {
    bytes!(16);
    bytes!(24);
    bytes!(32);
    bytes!(30);
    bytes!(34);
    bytes!(39);
    bytes!(42);
    bytes!(47);
    bytes!(49);
}
