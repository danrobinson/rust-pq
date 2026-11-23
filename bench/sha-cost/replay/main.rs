//! Replay the real portable scheduling decisions through matched native hash kernels.
#![allow(unexpected_cfgs)]
extern crate alloc;
use native::{address, params, util};
use std::{hint::black_box, time::Instant};
use trace::{capture, Trace};
macro_rules! sha2_only {
    ($($item:tt)*) => {};
}
mod fors;
mod hash;
mod ht;
mod slh;
mod trace;
mod wots;
mod xmss;

fn run<const N: usize>(set: &str, p: &params::Params, size: usize, round: u8) {
    let seed =
        |off: usize| std::array::from_fn::<_, N, _>(|i| (i + off + 42 + round as usize) as u8);
    let (skseed, prf, pkseed) = (seed(0), seed(N), seed(2 * N));
    let msg = vec![17 ^ round; size];
    let mut sk = vec![0; 4 * N];
    let mut pk = vec![0; 2 * N];
    native::slh::slh_keygen_internal(p, &skseed, &prf, &pkseed, &mut sk, &mut pk);
    let sig = native::slh::slh_sign(p, &msg, &[], &sk, &pkseed).unwrap();
    for op in ["keygen", "sign", "verify"] {
        capture(|t| {
            *t = Trace::default();
            t.literal(&pkseed);
            if op != "verify" {
                t.literal(&skseed);
                t.literal(&prf);
            }
            if op != "keygen" {
                t.literal(&pk[N..]);
            }
            if op == "verify" {
                for b in sig.chunks_exact(N) {
                    t.literal(b);
                }
            }
        });
        match op {
            "keygen" => {
                let (mut s, mut k) = (vec![0; 4 * N], vec![0; 2 * N]);
                slh::slh_keygen_internal(p, &skseed, &prf, &pkseed, &mut s, &mut k);
                assert_eq!((&s, &k), (&sk, &pk));
            }
            "sign" => assert_eq!(slh::slh_sign(p, &msg, &[], &sk, &pkseed).unwrap(), sig),
            _ => assert!(slh::slh_verify::<N>(p, &msg, &sig, &[], &pk)),
        }
        let t = capture(std::mem::take);
        let mut times = [0u128; 3];
        let orders = [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ];
        for mode in orders[round.saturating_sub(1) as usize % 6] {
            if mode == 2 {
                let mut s = vec![0; 4 * N];
                let mut k = vec![0; 2 * N];
                let mut signed = None;
                let now = Instant::now();
                match op {
                    "keygen" => {
                        native::slh::slh_keygen_internal(p, &skseed, &prf, &pkseed, &mut s, &mut k)
                    }
                    "sign" => signed = native::slh::slh_sign(p, black_box(&msg), &[], &sk, &pkseed),
                    _ => assert!(black_box(native::slh::slh_verify::<N>(
                        p,
                        &msg,
                        &sig,
                        &[],
                        &pk
                    ))),
                }
                times[mode] = now.elapsed().as_nanos();
                if op == "keygen" {
                    assert_eq!((&s, &k), (&sk, &pk));
                }
                if op == "sign" {
                    assert_eq!(signed.as_ref(), Some(&sig));
                }
            } else {
                let mut v = t.memory::<N>();
                let now = Instant::now();
                let md = if mode == 0 {
                    t.replay::<N, true>(p, black_box(&mut v))
                } else {
                    t.replay::<N, false>(p, black_box(&mut v))
                };
                times[mode] = now.elapsed().as_nanos();
                t.check(&v, &md);
            }
        }
        println!(
            "{set},{size},{op},{round},{},{},{},{}",
            t.ops.len(),
            times[0],
            times[1],
            times[2]
        );
    }
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let rounds: u8 = args.get(1).map(|v| v.parse().unwrap()).unwrap_or(6);
    let suite = args.get(2).map(String::as_str).unwrap_or("all");
    println!("set,bytes,operation,round,hash_batches,full_ns,reuse_ns,api_ns");
    for r in 0..=rounds {
        for bytes in [32, 1 << 20] {
            macro_rules! bench {
                ($n:literal,$set:ident) => {
                    if suite == "all" || suite == stringify!($set) {
                        run::<$n>(stringify!($set), &params::$set, bytes, r);
                    }
                };
            }
            bench!(16, SHA2_128S);
            bench!(16, SHA2_128F);
            bench!(24, SHA2_192S);
            bench!(24, SHA2_192F);
            bench!(32, SHA2_256S);
            bench!(32, SHA2_256F);
        }
    }
}
