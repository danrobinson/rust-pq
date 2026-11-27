// Compiled inside the production cache::shake_ops module.
pub(super) fn compare<const N: usize>(p: &Params) {
    let sk: [u8; N] = core::array::from_fn(|i| (i as u8).wrapping_mul(17));
    let pk = core::array::from_fn(|i| 101u8.wrapping_sub(i as u8));
    let base = Adrs::new().with_layer(p.d - 2).with_tree(0x9876_5432);
    let idx = (0x155 & ((1 << p.hp) - 1)) as u32;
    let wa = base.with_type(WOTS_HASH).with_keypair(idx);
    let fa = base.with_type(FORS_TREE).with_keypair(idx);
    let msg = core::array::from_fn(|i| (i as u8).wrapping_mul(0x1f));
    let md: Vec<u8> = (0..p.md_bytes())
        .map(|i| (i as u8).wrapping_mul(59))
        .collect();
    let wots = crate::wots::wots_sign(&msg, &sk, &pk, wa);
    let xmss = crate::xmss::xmss_sign(p, &msg, &sk, idx, &pk, base);
    let fors = crate::fors::fors_sign(p, &md, &sk, &pk, fa);

    for accelerated in [false, true] {
        crate::shake256::parallel::ENABLED.store(accelerated, std::sync::atomic::Ordering::Relaxed);
        assert_eq!(wots_sign(&msg, &sk, &pk, wa), wots);
        assert_eq!(xmss_sign(p, &msg, &sk, idx, &pk, base), xmss);
        assert_eq!(fors_sign(p, &md, &sk, &pk, fa), fors);
        for different in [false, true] {
            let perturb = |s: &[u8]| -> Vec<u8> {
                s.iter()
                    .enumerate()
                    .map(|(i, b)| {
                        if different {
                            b ^ (i as u8).wrapping_add(1)
                        } else {
                            *b
                        }
                    })
                    .collect()
            };
            let xs = perturb(&xmss);
            let fs = perturb(&fors);
            assert_eq!(
                xmss_pk_from_sig(p, idx, &xs, &msg, &pk, base),
                crate::xmss::xmss_pk_from_sig(p, idx, &xs, &msg, &pk, base)
            );
            assert_eq!(
                fors_pk_from_sig(p, &fs, &md, &pk, fa),
                crate::fors::fors_pk_from_sig(p, &fs, &md, &pk, fa)
            );
        }
    }
}
