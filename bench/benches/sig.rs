//! keygen / sign / verify for every implementation, SLH-DSA-SHA2-128s.
//!
//! Within each operation all implementations run back to back (interleaved by
//! operation, not one library after another); run.sh runs the whole suite
//! several times, in forward and reversed library order (BENCH_REVERSE=1).
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, SamplingMode};
use slhdsa_bench::*;
use std::hint::black_box;
use std::time::Duration;

const MSG_LENS: [usize; 2] = [32, 1 << 20];

fn label(len: usize) -> String {
    if len >= 1 << 20 { format!("{}MiB", len >> 20) } else { format!("{len}B") }
}

fn benches(c: &mut Criterion) {
    let impls = all();
    let v = verified();
    let (sk, pk) = (v.keygen)(&SK_SEED, &SK_PRF, &PK_SEED);

    {
        let mut g = c.benchmark_group("keygen");
        g.sampling_mode(SamplingMode::Flat).sample_size(10).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(4));
        for imp in &impls {
            g.bench_function(imp.name, |b| b.iter(|| (imp.keygen)(black_box(&SK_SEED), black_box(&SK_PRF), black_box(&PK_SEED))));
        }
        g.finish();
    }
    for &len in &MSG_LENS {
        let m = message(len);
        let mut g = c.benchmark_group(format!("sign_{}", label(len)));
        g.sampling_mode(SamplingMode::Flat).sample_size(10).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(6));
        for imp in &impls {
            let s = (imp.make_signer)(&sk);
            g.bench_with_input(BenchmarkId::from_parameter(imp.name), &m, |b, m| b.iter(|| s(black_box(m))));
        }
        g.finish();
    }
    for &len in &MSG_LENS {
        let m = message(len);
        let mut g = c.benchmark_group(format!("verify_{}", label(len)));
        g.sample_size(30).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(3));
        for imp in &impls {
            // Each library verifies its own signature (PQClean's differs from the FIPS 205 one).
            let sig = (imp.make_signer)(&sk)(&m);
            let ver = (imp.make_verifier)(&pk);
            assert!(ver(&m, &sig), "{} failed to verify", imp.name);
            g.bench_with_input(BenchmarkId::from_parameter(imp.name), &m, |b, m| b.iter(|| assert!(ver(black_box(m), black_box(&sig)))));
        }
        g.finish();
    }
}

criterion_group!(sig, benches);
criterion_main!(sig);
