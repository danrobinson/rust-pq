// Included only in the temporary verification crate, inside batch_api.
pub mod worker_replay {
    use super::*;
    use std::sync::Barrier;

    // MUTATED_WORKERS

    #[derive(Clone, Copy)]
    enum Fault {
        None,
        SkipFirst,
        SwapSlot,
        LoseRejection,
        SerialAny,
        EmptyFalse,
    }

    fn exercise(verdicts: &[bool], threads: usize, fault: Fault) {
        let encoded: Vec<_> = (0..verdicts.len()).map(usize::to_le_bytes).collect();
        let items: Vec<_> = encoded
            .iter()
            .map(|id| VerifyItem::new(id, &[], &[], &[]))
            .collect();
        let seen: Vec<_> = items.iter().map(|_| AtomicUsize::new(0)).collect();
        let check = |item: &VerifyItem| {
            let i = usize::from_le_bytes(item.msg.try_into().unwrap());
            assert_eq!(
                seen[i].fetch_add(1, Ordering::Relaxed),
                0,
                "duplicate live ticket"
            );
            if i % 7 == 0 {
                std::thread::yield_now();
            }
            verdicts[i]
        };
        let got = match fault {
            Fault::SkipFirst => skip_first(&items, check),
            Fault::SwapSlot => swap_slot(&items, check),
            _ => verify_batch_with(&items, check),
        };
        assert_eq!(got, verdicts, "wrong ordered verdicts");
        for calls in &seen {
            assert_eq!(calls.swap(0, Ordering::Relaxed), 1, "missing live ticket");
        }
        let result = match fault {
            Fault::LoseRejection => lose_rejection(&items, check),
            Fault::SerialAny => serial_any(&items, check),
            Fault::EmptyFalse => empty_false(&items, check),
            _ => verify_batch_all_with(&items, check),
        };
        let accepted = verdicts.iter().all(|&v| v);
        assert_eq!(result, accepted, "wrong conjunction");
        if accepted {
            assert!(seen.iter().all(|n| n.load(Ordering::Relaxed) == 1));
        } else {
            assert!(seen
                .iter()
                .zip(verdicts)
                .any(|(n, &v)| !v && n.load(Ordering::Relaxed) == 1));
        }
        // Relaxed cancellation can leave more than one verification in flight.
        // Once execute returns, every earlier in-range claimed ticket completed.
        let completed = seen
            .iter()
            .take_while(|calls| calls.load(Ordering::Relaxed) == 1)
            .count();
        assert!(
            seen[completed..]
                .iter()
                .all(|calls| calls.load(Ordering::Relaxed) == 0),
            "gap in completed ticket prefix"
        );
        if threads == 1 {
            let consumed = verdicts
                .iter()
                .position(|&v| !v)
                .map_or(items.len(), |i| i + 1);
            for (i, calls) in seen.iter().enumerate() {
                assert_eq!(
                    calls.load(Ordering::Relaxed),
                    usize::from(i < consumed),
                    "serial short-circuit"
                );
            }
        }
    }

    fn must_overlap() {
        let ids: Vec<_> = (0usize..32).map(usize::to_le_bytes).collect();
        let items: Vec<_> = ids
            .iter()
            .map(|id| VerifyItem::new(id, &[], &[], &[]))
            .collect();
        let mark = Barrier::new(2);
        let published = AtomicUsize::new(0);
        for all in [false, true] {
            let verify = |item: &VerifyItem| {
                let i = usize::from_le_bytes(item.msg.try_into().unwrap());
                if i < 2 {
                    published.fetch_add(1, Ordering::Relaxed);
                    mark.wait();
                }
                i != 1
            };
            if all {
                assert!(!verify_batch_all_with(&items, verify));
            } else {
                assert_eq!(
                    verify_batch_with(&items, verify),
                    (0..32).map(|i| i != 1).collect::<Vec<_>>()
                );
            }
        }
        assert_eq!(published.load(Ordering::Relaxed), 4);
    }

    fn occupied_pool() {
        // The outer job owns the real pool throughout each inner dispatch.
        let claimed = AtomicBool::new(false);
        pool::execute(2, false, &|| {
            if claimed.swap(true, Ordering::Relaxed) {
                return;
            }
            let items = [VerifyItem::new(&[], &[], &[], &[]); 128];
            let calls = AtomicUsize::new(0);
            assert!(!verify_batch_all_with(&items, |_| calls
                .fetch_add(1, Ordering::Relaxed)
                < 2));
            assert_eq!(
                calls.load(Ordering::Relaxed),
                3,
                "busy-pool rejection did not stop"
            );
            assert_eq!(
                verify_batch_with(&items, |_| true),
                alloc::vec![true;items.len()]
            );
        });
        assert!(claimed.load(Ordering::Relaxed));
    }

    pub fn run(threads: usize, mode: &str) {
        pool::configure_worker_replay(threads);
        let fault = match mode {
            "real" => Fault::None,
            "skip-first" => Fault::SkipFirst,
            "swap-slot" => Fault::SwapSlot,
            "lose-rejection" => Fault::LoseRejection,
            "serial-any" => Fault::SerialAny,
            "empty-false" => Fault::EmptyFalse,
            _ => panic!("unknown mode"),
        };
        for len in 0..=8 {
            for mask in 0..1usize << len {
                let verdicts: Vec<_> = (0..len).map(|i| mask & (1 << i) != 0).collect();
                exercise(&verdicts, threads, fault);
            }
        }
        let mut state = 0x93bc_7081_a40f_f6de_u64;
        for len in [9, 15, 16, 17, 31, 32, 33, 64, 127, 128, 257, 521] {
            let mut verdicts = alloc::vec![true;len];
            for i in 0..len {
                verdicts[i] = false;
                exercise(&verdicts, threads, fault);
                verdicts[i] = true;
            }
            for _ in 0..8 {
                for value in &mut verdicts {
                    state ^= state << 13;
                    state ^= state >> 7;
                    state ^= state << 17;
                    *value = state & 1 != 0;
                }
                exercise(&verdicts, threads, fault);
            }
        }
        if threads >= 2 {
            must_overlap();
            occupied_pool();
        }
    }
}
