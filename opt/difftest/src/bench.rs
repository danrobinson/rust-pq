//! Timing harness, built against each crate like `dump` (see `../bench.sh`).
//! Usage: bench <runs>. Prints one line per operation with every run's time.

use slhdsa::*;
use std::time::Instant;

fn main() {
    let runs: usize = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(5);
    let (sk_seed, sk_prf, pk_seed) = ([1u8; 16], [2u8; 16], [3u8; 16]);
    let msg = [0x5au8; 32];
    let (sk, pk) = slh_keygen_internal(&sk_seed, &sk_prf, &pk_seed);
    let sig = slh_sign_internal(&msg, &sk, &[4u8; 16]);
    let (mut kg, mut sg, mut vf) = (vec![], vec![], vec![]);
    for _ in 0..runs {
        let t = Instant::now();
        std::hint::black_box(slh_keygen_internal(&sk_seed, &sk_prf, std::hint::black_box(&pk_seed)));
        kg.push(t.elapsed().as_secs_f64() * 1e3);
        let t = Instant::now();
        std::hint::black_box(slh_sign_internal(&msg, std::hint::black_box(&sk), &[4u8; 16]));
        sg.push(t.elapsed().as_secs_f64() * 1e3);
        let t = Instant::now();
        for _ in 0..10 {
            assert!(std::hint::black_box(slh_verify_internal(&msg, std::hint::black_box(&sig), &pk)));
        }
        vf.push(t.elapsed().as_secs_f64() * 1e3 / 10.0);
    }
    for (name, v) in [("keygen", kg), ("sign", sg), ("verify", vf)] {
        let s: Vec<String> = v.iter().map(|x| format!("{x:.3}")).collect();
        println!("{name} {}", s.join(" "));
    }
}
