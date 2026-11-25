// Execute the source signature writes using tagged bytes. A copied byte carries
// its primitive's ID and its original byte position, including inside partial stores.
mod signing {
    use super::*;
    fn pack<const N: usize>(d: Digest) -> [usize; N] {
        core::array::from_fn(|i| (d.0 + 1) * 64 + i)
    }
    fn unpack(row: &[usize]) -> Digest {
        assert!(!row.is_empty() && row[0] >= 64);
        let id = row[0] / 64;
        for (j, v) in row.iter().enumerate() {
            assert_eq!(*v, id * 64 + j)
        }
        Digest(id - 1)
    }
    fn pair_active<const N: usize>(
        seed: &Digest,
        a: &[Adrs; WIDTH],
        l: &[[usize; N]; WIDTH],
        r: &[[usize; N]; WIDTH],
        active: usize,
    ) -> [[usize; N]; WIDTH] {
        assert!((1..=WIDTH).contains(&active));
        std::array::from_fn(|j| {
            if j < active {
                pack(pair(true, seed, &a[j], &unpack(&l[j]), &unpack(&r[j])))
            } else {
                [0; N]
            }
        })
    }
    fn thash_pair<const N: usize>(
        seed: &Digest,
        a: &Adrs,
        l: &[usize; N],
        r: &[usize; N],
    ) -> [usize; N] {
        pack(pair(false, seed, a, &unpack(l), &unpack(r)))
    }
    fn xmss_subtree<const N: usize>(
        sk: &Digest,
        seed: &Digest,
        i: u32,
        h: u32,
        a: Adrs,
    ) -> [usize; N] {
        pack(super::xmss_subtree::<N>(sk, seed, i, h, a))
    }
    struct Params {
        hp: u32,
    }
    fn auth<const N: usize>(
        p: &Params,
        idx: u32,
        seed: &Digest,
        sk: &Digest,
        addr: Adrs,
    ) -> Vec<usize> {
        let sig_lane = (idx & 7) as usize;
        let base_leaf = idx & !7;
        let len = 2 * N + 3;
        let mut sig: Vec<_> = (0..(len + p.hp as usize) * N)
            .map(|i| usize::MAX - i)
            .collect();
        let nodes = wots_leaves_batch::<N>(sk, seed, base_leaf, addr).map(pack::<N>);
        // PRODUCTION_AUTH
    }
    pub(super) fn check<const N: usize>() {
        let mut shapes = vec![None; 9];
        for hp in [3, 4, 8, 9] {
            for idx in 0..1 << hp {
                OPS.with_borrow_mut(|ops| ops.clear());
                let sig = auth::<N>(&Params { hp }, idx, &SEED, &SECRET, BASE);
                let prefix = (2 * N + 3) * N;
                assert_eq!(sig.len(), prefix + hp as usize * N);
                for (i, v) in sig[..prefix].iter().enumerate() {
                    assert_eq!(*v, usize::MAX - i)
                }
                for (h, row) in sig[prefix..].chunks_exact(N).enumerate() {
                    let mut trace = String::new();
                    OPS.with_borrow(|ops| {
                        show(ops, unpack(row), h as u32, (idx >> h) ^ 1, &mut trace)
                    });
                    match &shapes[h] {
                        Some(old) => assert_eq!(old, &trace),
                        None => shapes[h] = Some(trace),
                    }
                }
            }
        }
        for (h, s) in shapes.into_iter().enumerate() {
            println!("{N} {h} {}", s.unwrap())
        }
    }
}
fn main() {
    signing::check::<16>();
    signing::check::<24>();
    signing::check::<32>()
}
