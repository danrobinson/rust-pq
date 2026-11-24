#[kani::proof]
#[kani::unwind(40)]
#[kani::stub(crate::xmss::XmssParams::xmss_sign, Observe::checked_sign)]
#[kani::stub(crate::xmss::XmssParams::xmss_pk_from_sig, Observe::checked_recover)]
fn sign_step() {
    let seed = PkSeed(Array(kani::any::<[u8; N]>()));
    let secret = SkSeed(Array(kani::any::<[u8; N]>()));
    let hash = P::new_from_pk_seed(&seed);
    let message = kani::any::<[u8; N]>();
    let tree: u64 = kani::any();
    let leaf: u32 = kani::any();
    let j: usize = kani::any();
    let offset: usize = kani::any();
    kani::assume(j < D && offset < XmssSig::<P>::SIZE);
    unsafe {
        SAMPLE = offset;
        PREVIOUS = message;
        TREE = tree;
        LEAF = leaf;
        SECRET = core::ptr::from_ref(&secret).cast();
        HASH = core::ptr::from_ref(&hash).cast();
        LAYER = j;
        RECOVERED = j;
    }
    let (sigs, root) = if j == 0 {
        hash.proof_first(&Array(message), &secret, tree, leaf)
    } else {
        let prior_tree = (u128::from(tree) >> (HP * (j - 1))) as u64;
        let mut adrs = WotsHash::default();
        adrs.layer_adrs.set((j - 1) as u32);
        adrs.tree_adrs_low.set(prior_tree);
        let mut sigs = Array::default();
        let (root, new_tree, new_leaf) = hash.proof_later(
            Array(message),
            &secret,
            prior_tree,
            j as u32,
            adrs,
            &mut sigs,
        );
        assert_eq!(new_tree, (u128::from(tree) >> (HP * j)) as u64);
        assert_eq!(new_leaf, (prior_tree & ((1u64 << HP) - 1)) as u32);
        (sigs, root)
    };
    unsafe {
        let signed = LAYER;
        let recovered = RECOVERED;
        assert_eq!(signed, j + 1);
        assert_eq!(recovered, if j + 1 == D { j } else { j + 1 });
        let expected_root = PREVIOUS;
        assert_eq!(root.as_slice(), &expected_root);
        let sig = sigs[j].as_ref().unwrap();
        let byte = core::ptr::from_ref(sig).cast::<u8>().add(offset).read();
        assert_eq!(byte, BYTES[j]);
        let other: usize = kani::any();
        kani::assume(other < D && other != j);
        assert!(sigs[other].is_none());
    }
}
