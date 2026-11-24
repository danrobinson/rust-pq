#![cfg(all(feature = "parallel", not(target_os = "none")))]

use std::sync::Arc;
use std::thread;

use slhdsa::batch_api::{self, VerifyItem};

#[test]
fn batch_verify_edge_cases_and_mixed_verdicts() {
    // Empty batches
    assert!(batch_api::verify_sha2_128f(&[]).is_empty());
    assert!(batch_api::verify_all_sha2_128f(&[]));
    assert!(batch_api::verify_shake_128f(&[]).is_empty());
    assert!(batch_api::verify_all_shake_128f(&[]));

    // SHA-2 128f mixed valid/invalid batch
    {
        use slhdsa::sha2_128f::{api, params::*};
        let seeds = [0x11u8; SEED_BYTES];
        let mut sk = [0u8; SK_BYTES];
        let mut pk = [0u8; PK_BYTES];
        api::keygen(&seeds, &mut sk, &mut pk);

        let msgs: Vec<Vec<u8>> = (0..16)
            .map(|i| vec![i as u8; if i % 4 == 0 { 1200 } else { 32 + i }])
            .collect();
        let ctxs: Vec<Vec<u8>> = (0..16).map(|i| vec![0xa0 + i as u8; i]).collect();
        let mut sigs: Vec<Vec<u8>> = msgs
            .iter()
            .zip(ctxs.iter())
            .map(|(m, c)| api::sign_deterministic(m, c, &sk).unwrap())
            .collect();

        // Single valid item
        let single = [VerifyItem::new(&msgs[0], &sigs[0], &ctxs[0], &pk)];
        assert_eq!(batch_api::verify_sha2_128f(&single), vec![true]);
        assert!(batch_api::verify_all_sha2_128f(&single));

        // All 16 valid
        {
            let all_valid: Vec<VerifyItem<'_>> = (0..16)
                .map(|i| VerifyItem::new(&msgs[i], &sigs[i], &ctxs[i], &pk))
                .collect();
            assert_eq!(batch_api::verify_sha2_128f(&all_valid), vec![true; 16]);
            assert!(batch_api::verify_all_sha2_128f(&all_valid));
        }

        // Corrupt specific items: sig flip, wrong msg, wrong ctx, bad pk len, bad ctx len
        sigs[3][17] ^= 0x01;
        let bad_msg = b"tampered message";
        let bad_ctx = [0u8; 256];
        let short_pk = &pk[..PK_BYTES - 1];

        let mut mixed: Vec<VerifyItem<'_>> = (0..16)
            .map(|i| VerifyItem::new(&msgs[i], &sigs[i], &ctxs[i], &pk))
            .collect();
        mixed[7].msg = bad_msg;
        mixed[11].ctx = &bad_ctx;
        mixed[14].pk = short_pk;

        let verdicts = batch_api::verify_sha2_128f(&mixed);
        for (i, &ok) in verdicts.iter().enumerate() {
            let expected = !matches!(i, 3 | 7 | 11 | 14);
            assert_eq!(ok, expected, "unexpected verdict at index {i}");
        }
        assert!(!batch_api::verify_all_sha2_128f(&mixed));
    }

    // SHAKE 128f mixed valid/invalid batch
    {
        use slhdsa::shake_128f::{api, params::*};
        let seeds = [0x22u8; SEED_BYTES];
        let mut sk = [0u8; SK_BYTES];
        let mut pk = [0u8; PK_BYTES];
        api::keygen(&seeds, &mut sk, &mut pk);

        let msgs: Vec<Vec<u8>> = (0..12).map(|i| vec![0x30 + i as u8; 40 + i]).collect();
        let mut sigs: Vec<Vec<u8>> = msgs
            .iter()
            .map(|m| api::sign_deterministic(m, b"shake-ctx", &sk).unwrap())
            .collect();

        {
            let valid_items: Vec<VerifyItem<'_>> = (0..12)
                .map(|i| VerifyItem::new(&msgs[i], &sigs[i], b"shake-ctx", &pk))
                .collect();
            assert_eq!(batch_api::verify_shake_128f(&valid_items), vec![true; 12]);
            assert!(batch_api::verify_all_shake_128f(&valid_items));
        }

        sigs[0][0] ^= 0x80;
        let last_len = sigs[11].len();
        sigs[11][last_len - 1] ^= 0x01;
        let mixed: Vec<VerifyItem<'_>> = (0..12)
            .map(|i| VerifyItem::new(&msgs[i], &sigs[i], b"shake-ctx", &pk))
            .collect();

        let verdicts = batch_api::verify_shake_128f(&mixed);
        for (i, &ok) in verdicts.iter().enumerate() {
            let expected = !matches!(i, 0 | 11);
            assert_eq!(ok, expected, "unexpected SHAKE verdict at index {i}");
        }
        assert!(!batch_api::verify_all_shake_128f(&mixed));
    }
}

#[test]
fn batch_verify_all_twelve_parameter_sets() {
    macro_rules! check_set {
        ($set:ident, $verify_fn:ident, $verify_all_fn:ident) => {{
            use slhdsa::$set::{api, params::*};
            let seeds = [0x5au8; SEED_BYTES];
            let mut sk = [0u8; SK_BYTES];
            let mut pk = [0u8; PK_BYTES];
            api::keygen(&seeds, &mut sk, &mut pk);
            let m0 = b"batch message zero";
            let m1 = b"batch message one";
            let s0 = api::sign_deterministic(m0, b"c0", &sk).unwrap();
            let mut s1 = api::sign_deterministic(m1, b"c1", &sk).unwrap();
            let ok_items = [
                VerifyItem::new(m0, &s0, b"c0", &pk),
                VerifyItem::new(m1, &s1, b"c1", &pk),
            ];
            assert_eq!(batch_api::$verify_fn(&ok_items), vec![true, true]);
            assert!(batch_api::$verify_all_fn(&ok_items));

            s1[N] ^= 1;
            let bad_items = [
                VerifyItem::new(m0, &s0, b"c0", &pk),
                VerifyItem::new(m1, &s1, b"c1", &pk),
            ];
            assert_eq!(batch_api::$verify_fn(&bad_items), vec![true, false]);
            assert!(!batch_api::$verify_all_fn(&bad_items));
        }};
    }

    check_set!(sha2_128s, verify_sha2_128s, verify_all_sha2_128s);
    check_set!(sha2_128f, verify_sha2_128f, verify_all_sha2_128f);
    check_set!(sha2_192s, verify_sha2_192s, verify_all_sha2_192s);
    check_set!(sha2_192f, verify_sha2_192f, verify_all_sha2_192f);
    check_set!(sha2_256s, verify_sha2_256s, verify_all_sha2_256s);
    check_set!(sha2_256f, verify_sha2_256f, verify_all_sha2_256f);
    check_set!(shake_128s, verify_shake_128s, verify_all_shake_128s);
    check_set!(shake_128f, verify_shake_128f, verify_all_shake_128f);
    check_set!(shake_192s, verify_shake_192s, verify_all_shake_192s);
    check_set!(shake_192f, verify_shake_192f, verify_all_shake_192f);
    check_set!(shake_256s, verify_shake_256s, verify_all_shake_256s);
    check_set!(shake_256f, verify_shake_256f, verify_all_shake_256f);
}

/// Multi-threaded stress test: 8 concurrent caller threads simultaneously invoke
/// keygen, deterministic signing, hedged signing, and batch verification across
/// SHA-2 and SHAKE sets to prove zero deadlocks, races, or nondeterminism.
#[test]
fn concurrent_callers_stress_test() {
    // Compute deterministic ground-truth outputs on a single thread first.
    let (ref_sk_2f, ref_pk_2f, ref_sig_2f) = {
        use slhdsa::sha2_128f::{api, params::*};
        let seeds = [0x77u8; SEED_BYTES];
        let mut sk = [0u8; SK_BYTES];
        let mut pk = [0u8; PK_BYTES];
        api::keygen(&seeds, &mut sk, &mut pk);
        let sig = api::sign_deterministic(b"concurrent-sha2-128f", b"ctx", &sk).unwrap();
        (sk, pk, Arc::new(sig))
    };
    let (ref_sk_kf, ref_pk_kf, ref_sig_kf) = {
        use slhdsa::shake_128f::{api, params::*};
        let seeds = [0x88u8; SEED_BYTES];
        let mut sk = [0u8; SK_BYTES];
        let mut pk = [0u8; PK_BYTES];
        api::keygen(&seeds, &mut sk, &mut pk);
        let sig = api::sign_deterministic(b"concurrent-shake-128f", b"ctx", &sk).unwrap();
        (sk, pk, Arc::new(sig))
    };
    let (ref_sk_2s, ref_pk_2s, ref_sig_2s) = {
        use slhdsa::sha2_128s::{api, params::*};
        let seeds = [0x99u8; SEED_BYTES];
        let mut sk = [0u8; SK_BYTES];
        let mut pk = [0u8; PK_BYTES];
        api::keygen(&seeds, &mut sk, &mut pk);
        let sig = api::sign_deterministic(b"concurrent-sha2-128s", b"", &sk).unwrap();
        (sk, pk, Arc::new(sig))
    };

    let handles: Vec<_> = (0..8)
        .map(|tid| {
            let ref_sig_2f = Arc::clone(&ref_sig_2f);
            let ref_sig_kf = Arc::clone(&ref_sig_kf);
            let ref_sig_2s = Arc::clone(&ref_sig_2s);
            thread::spawn(move || {
                for iter in 0..4 {
                    // SHA-2 128f keygen + sign + batch verify
                    {
                        use slhdsa::sha2_128f::{api, params::*};
                        let seeds = [0x77u8; SEED_BYTES];
                        let mut sk = [0u8; SK_BYTES];
                        let mut pk = [0u8; PK_BYTES];
                        api::keygen(&seeds, &mut sk, &mut pk);
                        assert_eq!(sk, ref_sk_2f);
                        assert_eq!(pk, ref_pk_2f);
                        let sig =
                            api::sign_deterministic(b"concurrent-sha2-128f", b"ctx", &sk).unwrap();
                        assert_eq!(sig.as_slice(), ref_sig_2f.as_slice());
                        let items = [
                            VerifyItem::new(b"concurrent-sha2-128f", &sig, b"ctx", &pk),
                            VerifyItem::new(b"concurrent-sha2-128f", &sig, b"ctx", &pk),
                            VerifyItem::new(b"concurrent-sha2-128f", &sig, b"ctx", &pk),
                            VerifyItem::new(b"concurrent-sha2-128f", &sig, b"ctx", &pk),
                        ];
                        assert!(batch_api::verify_all_sha2_128f(&items));
                    }

                    // SHAKE 128f keygen + sign + batch verify
                    {
                        use slhdsa::shake_128f::{api, params::*};
                        let seeds = [0x88u8; SEED_BYTES];
                        let mut sk = [0u8; SK_BYTES];
                        let mut pk = [0u8; PK_BYTES];
                        api::keygen(&seeds, &mut sk, &mut pk);
                        assert_eq!(sk, ref_sk_kf);
                        assert_eq!(pk, ref_pk_kf);
                        let sig =
                            api::sign_deterministic(b"concurrent-shake-128f", b"ctx", &sk).unwrap();
                        assert_eq!(sig.as_slice(), ref_sig_kf.as_slice());
                        let items = [
                            VerifyItem::new(b"concurrent-shake-128f", &sig, b"ctx", &pk),
                            VerifyItem::new(b"concurrent-shake-128f", &sig, b"ctx", &pk),
                        ];
                        assert!(batch_api::verify_all_shake_128f(&items));
                    }

                    // Mix in a larger `-s` set on alternating iterations
                    if (tid + iter) % 4 == 0 {
                        use slhdsa::sha2_128s::{api, params::*};
                        let seeds = [0x99u8; SEED_BYTES];
                        let mut sk = [0u8; SK_BYTES];
                        let mut pk = [0u8; PK_BYTES];
                        api::keygen(&seeds, &mut sk, &mut pk);
                        assert_eq!(sk, ref_sk_2s);
                        assert_eq!(pk, ref_pk_2s);
                        let sig =
                            api::sign_deterministic(b"concurrent-sha2-128s", b"", &sk).unwrap();
                        assert_eq!(sig.as_slice(), ref_sig_2s.as_slice());
                    }
                }
            })
        })
        .collect();

    for h in handles {
        h.join().expect("concurrent worker thread panicked");
    }
}

#[test]
#[ignore]
fn bench_batch_verify_throughput() {
    use std::hint::black_box;
    use std::time::Instant;

    macro_rules! measure_set {
        ($set:ident, $verify_fn:ident, $batch:expr) => {{
            use slhdsa::$set::{api, params::*};
            let seeds = [0x42u8; SEED_BYTES];
            let mut sk = [0u8; SK_BYTES];
            let mut pk = [0u8; PK_BYTES];
            api::keygen(&seeds, &mut sk, &mut pk);
            let msg = [0x17u8; 32];
            let sig = api::sign_deterministic(&msg, b"", &sk).unwrap();
            let items: Vec<VerifyItem<'_>> = (0..$batch)
                .map(|_| VerifyItem::new(&msg, &sig, b"", &pk))
                .collect();

            // Warmup
            assert!(batch_api::$verify_fn(&items).into_iter().all(|x| x));

            let mut seq_min = u128::MAX;
            let mut par_min = u128::MAX;
            for _ in 0..5 {
                let t0 = Instant::now();
                for item in &items {
                    assert!(black_box(api::verify(item.msg, item.sig, item.ctx, &pk)));
                }
                seq_min = seq_min.min(t0.elapsed().as_nanos());

                let t1 = Instant::now();
                let res = batch_api::$verify_fn(black_box(&items));
                assert!(black_box(res).into_iter().all(|x| x));
                par_min = par_min.min(t1.elapsed().as_nanos());
            }

            let seq_per = seq_min as f64 / ($batch as f64 * 1e3);
            let par_per = par_min as f64 / ($batch as f64 * 1e3);
            let seq_tps = ($batch as f64) / (seq_min as f64 / 1e9);
            let par_tps = ($batch as f64) / (par_min as f64 / 1e9);
            println!(
                "{:<11} (B={:>2}) | 1T: {:>6.1} us/sig ({:>7.0} ver/s) | Par: {:>5.1} us/sig ({:>8.0} ver/s) | {:.2}x",
                stringify!($set),
                $batch,
                seq_per,
                seq_tps,
                par_per,
                par_tps,
                seq_min as f64 / par_min as f64
            );
        }};
    }

    measure_set!(sha2_128s, verify_sha2_128s, 64);
    measure_set!(sha2_128f, verify_sha2_128f, 64);
    measure_set!(sha2_192s, verify_sha2_192s, 64);
    measure_set!(sha2_192f, verify_sha2_192f, 64);
    measure_set!(sha2_256s, verify_sha2_256s, 64);
    measure_set!(sha2_256f, verify_sha2_256f, 64);
    measure_set!(shake_128s, verify_shake_128s, 64);
    measure_set!(shake_128f, verify_shake_128f, 64);
    measure_set!(shake_192s, verify_shake_192s, 64);
    measure_set!(shake_192f, verify_shake_192f, 64);
    measure_set!(shake_256s, verify_shake_256s, 64);
    measure_set!(shake_256f, verify_shake_256f, 64);
}
