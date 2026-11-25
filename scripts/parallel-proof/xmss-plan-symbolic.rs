fn main() {
    let args: Vec<usize> = std::env::args()
        .skip(1)
        .map(|s| s.parse().unwrap())
        .collect();
    for pair in args.chunks_exact(2) {
        let (d, w) = (pair[0], pair[1]);
        let layers: Vec<_> = (0..d).map(|j| ((), symbolic::Word::choice(j))).collect();
        let (jobs, metas, count) = build(&Params { hp: w as u32 }, d, &layers);
        assert_eq!(metas.len(), d * w);
        let mut jobs = jobs.into_iter();
        let mut used = 0;
        for (q, meta) in metas.into_iter().enumerate() {
            let (j, h) = (q / w, (q % w) as u32);
            let subtree_height = h.min(if w >= 6 { 3 } else { 2 });
            let split = h - subtree_height;
            let root = (layers[j].1 >> h) ^ 1;
            assert_eq!(meta.root_idx, root);
            assert_eq!((meta.height, meta.split, meta.slot_start), (h, split, used));
            for chunk in 0..1usize << split {
                let job = jobs.next().expect("missing subtree");
                let WorkKind::XmssSubtree {
                    layer,
                    idx,
                    height,
                    slot,
                } = job.kind
                else {
                    panic!("wrong task")
                };
                assert_eq!(job.weight, 256u32 << subtree_height);
                assert_eq!(
                    (layer as usize, idx, height, slot),
                    (j, (root << split) + chunk as u32, subtree_height, used)
                );
                println!("{q} {chunk}");
                used += 1;
            }
        }
        assert_eq!(count, used);
        for j in 0..d - 1 {
            let job = jobs.next().unwrap();
            let WorkKind::XmssLeafPk { layer } = job.kind else {
                panic!("missing leaf key")
            };
            assert_eq!((layer as usize, job.weight), (j, 256));
        }
        assert!(jobs.next().is_none());
    }
}
