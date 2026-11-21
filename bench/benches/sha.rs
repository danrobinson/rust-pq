//! SHA-256 micro-benchmark: one-shot hash of 64 B, 102 B (the input size of
//! every SLH-DSA `F`/`PRF` call: PK.seed ‖ 0^48 ‖ ADRSc ‖ 16 B) and 1 KiB.
//!
//! `sha2-0.11` / `sha2-0.10` use the ARMv8 SHA-2 instructions in the default
//! build and the portable code in the `soft` build (see run.sh).
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::hint::black_box;
use std::time::Duration;

fn benches(c: &mut Criterion) {
    for len in [64usize, 102, 1024] {
        let m = slhdsa_bench::message(len);
        let mut g = c.benchmark_group(format!("sha256_{len}B"));
        g.throughput(Throughput::Bytes(len as u64)).sample_size(50).warm_up_time(Duration::from_millis(500)).measurement_time(Duration::from_secs(2));
        g.bench_with_input(BenchmarkId::from_parameter("verified"), &m, |b, m| b.iter(|| slhdsa::sha256::sha256(black_box(m))));
        g.bench_with_input(BenchmarkId::from_parameter("variant-B-soft-streaming"), &m, |b, m| b.iter(|| slhdsa_b::sha256::sha256(black_box(m))));
        g.bench_with_input(BenchmarkId::from_parameter("variant-C-armv8"), &m, |b, m| b.iter(|| slhdsa_c::sha256::sha256(black_box(m))));
        g.bench_with_input(BenchmarkId::from_parameter("sha2-0.11"), &m, |b, m| {
            use sha2::Digest;
            b.iter(|| sha2::Sha256::digest(black_box(m)))
        });
        g.bench_with_input(BenchmarkId::from_parameter("sha2-0.10"), &m, |b, m| {
            use sha2_010::Digest;
            b.iter(|| sha2_010::Sha256::digest(black_box(m)))
        });
        g.bench_with_input(BenchmarkId::from_parameter("openssl"), &m, |b, m| {
            let mut out = [0u8; 32];
            b.iter(|| unsafe { slhdsa_bench::bench_ossl_sha256(black_box(m).as_ptr(), m.len(), out.as_mut_ptr()) })
        });
        g.finish();
    }
}

criterion_group!(sha, benches);
criterion_main!(sha);
