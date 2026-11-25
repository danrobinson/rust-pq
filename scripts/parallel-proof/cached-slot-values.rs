// Reference the initial tree and leaf directly. The production loop mutates its
// copies while constructing the layer table. Every Word bit is symbolic.
fn check_cached_slots<const N: usize>(
    p: &Params, md: &[Token], sk: &[Token; N], pk: &Seed<N>, fors_address: Adrs,
    tree: Word, leaf: Word, cached_layers: usize,
    xmss: &[std::sync::OnceLock<[Token; N]>], fors: &[std::sync::OnceLock<[Token; N]>],
) {
    let hp = p.hp as usize;
    let layers = p.d as usize - cached_layers;
    assert_eq!(xmss.len(), layers * hp);
    for (slot, cell) in xmss.iter().enumerate() {
        let layer = slot / hp;
        let h = slot % hp;
        let tree_at = Word(std::array::from_fn(|b| *tree.0.get(layer * hp + b).unwrap_or(&0)));
        let leaf_at = if layer == 0 { leaf } else {
            Word(std::array::from_fn(|b| if b < hp { tree.0[(layer - 1) * hp + b] } else { 0 }))
        };
        let sibling = Word(std::array::from_fn(|b| *leaf_at.0.get(h + b).unwrap_or(&0) ^ u16::from(b == 0)));
        let address = Adrs::new().with_layer(layer as u32).with_tree(tree_at);
        assert_eq!(cell.get().unwrap(), &xmss_node(sk, sibling, h as u32, pk, address));
    }
    let expected = fors_sign(p, md, sk, pk, fors_address);
    assert_eq!(expected.len(), fors.len() * N);
    for (cell, row) in fors.iter().zip(expected.chunks_exact(N)) {
        assert_eq!(&cell.get().unwrap()[..], row);
    }
}
