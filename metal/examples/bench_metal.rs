//! Head-to-head benchmark: Apple Silicon Metal GPU vs CPU single-thread (`platform-sha2`)
//! across all six FIPS 205 SLH-DSA-SHA2 parameter sets.
//!
//! Run with:
//!   cargo run --release --example bench_metal

use std::hint::black_box;
use std::time::{Duration, Instant};

use slhdsa::params::{Params, SHA2_128F, SHA2_128S, SHA2_192F, SHA2_192S, SHA2_256F, SHA2_256S};
use slhdsa_metal::MetalSigner;

fn measure_median<F: FnMut()>(mut f: F, warmup: usize, min_iters: usize, min_time: Duration) -> Duration {
    for _ in 0..warmup {
        f();
    }
    let mut samples = Vec::with_capacity(min_iters.max(16));
    let start_all = Instant::now();
    while samples.len() < min_iters || start_all.elapsed() < min_time {
        let t0 = Instant::now();
        f();
        samples.push(t0.elapsed());
        if samples.len() >= 200 {
            break;
        }
    }
    samples.sort();
    samples[samples.len() / 2]
}

fn fmt_us(d: Duration) -> String {
    let us = d.as_secs_f64() * 1e6;
    if us >= 1000.0 {
        format!("{:.2} ms", us / 1000.0)
    } else {
        format!("{:.1} us", us)
    }
}

struct SetSummary {
    name: &'static str,
    cpu_kg: Duration,
    gpu_kg1: Duration,
    gpu_kg64_per: Duration,
    cpu_sign: Duration,
    gpu_sign1: Duration,
    gpu_sign64_per: Duration,
}

fn bench_set<const N: usize>(gpu: &MetalSigner, name: &'static str, p: &Params) -> SetSummary {
    let sk_seed = [0x11u8; N];
    let sk_prf = [0x22u8; N];
    let pk_seed = [0x33u8; N];
    let mut sk = vec![0u8; 4 * N];
    let mut pk = vec![0u8; 2 * N];
    slhdsa::slh::slh_keygen_internal::<N>(p, &sk_seed, &sk_prf, &pk_seed, &mut sk, &mut pk);

    let msg_storage: Vec<Vec<u8>> = (0..64)
        .map(|i| {
            let mut m = vec![0x42u8; 32];
            m[0] = i as u8;
            m[31] = (i * 7 + 3) as u8;
            m
        })
        .collect();
    let rnd_storage: Vec<[u8; N]> = (0..64).map(|i| [i as u8; N]).collect();

    // Sanity check byte-for-byte identity before timing
    let cpu_sig0 = slhdsa::slh::slh_sign::<N>(p, &msg_storage[0], b"", &sk, &rnd_storage[0]).unwrap();
    let gpu_sig0 = gpu
        .sign::<N>(p, &msg_storage[0], b"", &sk, &rnd_storage[0])
        .unwrap()
        .unwrap();
    assert_eq!(cpu_sig0, gpu_sig0, "GPU/CPU mismatch on {name}");

    let min_time = Duration::from_millis(250);

    // 1. CPU single-thread Keygen & Sign
    let cpu_kg = measure_median(
        || {
            let mut s = vec![0u8; 4 * N];
            let mut k = vec![0u8; 2 * N];
            slhdsa::slh::slh_keygen_internal::<N>(
                p,
                black_box(&sk_seed),
                black_box(&sk_prf),
                black_box(&pk_seed),
                &mut s,
                &mut k,
            );
            black_box((s, k));
        },
        1,
        5,
        min_time,
    );

    let cpu_sign = measure_median(
        || {
            let sig = slhdsa::slh::slh_sign::<N>(
                p,
                black_box(&msg_storage[0]),
                b"",
                black_box(&sk),
                black_box(&rnd_storage[0]),
            )
            .unwrap();
            black_box(sig);
        },
        1,
        5,
        min_time,
    );

    // 2. Metal GPU Single-op Keygen & Sign
    let gpu_kg1 = measure_median(
        || {
            let res = gpu
                .keygen_internal::<N>(p, black_box(&sk_seed), black_box(&sk_prf), black_box(&pk_seed))
                .unwrap();
            black_box(res);
        },
        2,
        5,
        min_time,
    );

    let gpu_sign1 = measure_median(
        || {
            let sig = gpu
                .sign::<N>(
                    p,
                    black_box(&msg_storage[0]),
                    b"",
                    black_box(&sk),
                    black_box(&rnd_storage[0]),
                )
                .unwrap()
                .unwrap();
            black_box(sig);
        },
        2,
        5,
        min_time,
    );

    println!("\n=== SLH-DSA-{name} (N={N}, d={}, h'={}, k={}, a={}) ===", p.d, p.hp, p.k, p.a);
    println!(
        "  Single Keygen:  CPU {:>9} | Metal GPU {:>9} | Speedup: {:>6.2}x",
        fmt_us(cpu_kg),
        fmt_us(gpu_kg1),
        cpu_kg.as_secs_f64() / gpu_kg1.as_secs_f64()
    );
    println!(
        "  Single Sign:    CPU {:>9} | Metal GPU {:>9} | Speedup: {:>6.2}x",
        fmt_us(cpu_sign),
        fmt_us(gpu_sign1),
        cpu_sign.as_secs_f64() / gpu_sign1.as_secs_f64()
    );

    // 3. Metal GPU Batch Keygen Throughput (batch = 1, 4, 16, 64)
    println!("  Batch Keygen (Metal GPU):");
    println!(
        "    {:>5} | {:>11} | {:>11} | {:>11} | {:>9}",
        "Batch", "Total", "Per-Key", "Keys/sec", "vs 1T CPU"
    );
    let mut gpu_kg64_per = Duration::ZERO;
    for &b in &[1usize, 4, 16, 64] {
        let seeds: Vec<([u8; N], [u8; N], [u8; N])> = (0..b)
            .map(|i| ([i as u8; N], [(i + 1) as u8; N], [(i + 2) as u8; N]))
            .collect();
        let dt = measure_median(
            || {
                let res = gpu.keygen_internal_batch::<N>(p, black_box(&seeds)).unwrap();
                black_box(res);
            },
            1,
            3,
            Duration::from_millis(200),
        );
        let per = dt.div_f64(b as f64);
        if b == 64 {
            gpu_kg64_per = per;
        }
        let ops_s = (b as f64) / dt.as_secs_f64();
        let speedup = cpu_kg.as_secs_f64() / per.as_secs_f64();
        println!(
            "    {:>5} | {:>11} | {:>11} | {:>9.1}/s | {:>8.2}x",
            b,
            fmt_us(dt),
            fmt_us(per),
            ops_s,
            speedup
        );
    }

    // 4. Metal GPU Batch Sign Throughput (batch = 1, 4, 16, 64)
    println!("  Batch Sign (Metal GPU, 32 B msg):");
    println!(
        "    {:>5} | {:>11} | {:>11} | {:>11} | {:>9}",
        "Batch", "Total", "Per-Sig", "Sigs/sec", "vs 1T CPU"
    );
    let mut gpu_sign64_per = Duration::ZERO;
    for &b in &[1usize, 4, 16, 64] {
        let msgs: Vec<&[u8]> = msg_storage[..b].iter().map(|m| m.as_slice()).collect();
        let rnds: Vec<&[u8; N]> = rnd_storage[..b].iter().collect();
        let dt = measure_median(
            || {
                let sigs = gpu
                    .sign_batch_same_key::<N>(p, black_box(&sk), black_box(&msgs), b"", black_box(&rnds))
                    .unwrap()
                    .unwrap();
                black_box(sigs);
            },
            1,
            3,
            Duration::from_millis(250),
        );
        let per = dt.div_f64(b as f64);
        if b == 64 {
            gpu_sign64_per = per;
        }
        let ops_s = (b as f64) / dt.as_secs_f64();
        let speedup = cpu_sign.as_secs_f64() / per.as_secs_f64();
        println!(
            "    {:>5} | {:>11} | {:>11} | {:>9.1}/s | {:>8.2}x",
            b,
            fmt_us(dt),
            fmt_us(per),
            ops_s,
            speedup
        );
    }

    SetSummary {
        name,
        cpu_kg,
        gpu_kg1,
        gpu_kg64_per,
        cpu_sign,
        gpu_sign1,
        gpu_sign64_per,
    }
}

fn main() {
    let gpu = MetalSigner::new().expect("failed to initialize Metal GPU");
    println!(
        "SLH-DSA Metal GPU Benchmark on {} (Unified Memory: {})",
        gpu.device_name(),
        gpu.has_unified_memory()
    );
    println!("CPU baseline: slhdsa single-threaded with `platform-sha2` (ARMv8 SHA-256/SHA-512)");

    // Warm up Metal GPU clocks once before timing
    let _ = gpu.keygen_internal::<16>(&SHA2_128S, &[1u8; 16], &[2u8; 16], &[3u8; 16]);

    let summaries = [
        bench_set::<16>(&gpu, "SHA2-128s", &SHA2_128S),
        bench_set::<16>(&gpu, "SHA2-128f", &SHA2_128F),
        bench_set::<24>(&gpu, "SHA2-192s", &SHA2_192S),
        bench_set::<24>(&gpu, "SHA2-192f", &SHA2_192F),
        bench_set::<32>(&gpu, "SHA2-256s", &SHA2_256S),
        bench_set::<32>(&gpu, "SHA2-256f", &SHA2_256F),
    ];

    println!("\n=== Summary (Apple M4 Metal GPU vs Single-Thread CPU `platform-sha2`) ===");
    println!(
        "{:<10} | {:>10} | {:>10} | {:>10} | {:>10} | {:>10} | {:>10} | {:>8}",
        "Param Set", "CPU Kg", "GPU Kg(1)", "GPU Kg/64", "CPU Sign", "GPU Sg(1)", "GPU Sg/64", "B64 Spd"
    );
    println!("{}", "-".repeat(98));
    for s in &summaries {
        let spd = s.cpu_sign.as_secs_f64() / s.gpu_sign64_per.as_secs_f64();
        println!(
            "{:<10} | {:>10} | {:>10} | {:>10} | {:>10} | {:>10} | {:>10} | {:>7.2}x",
            s.name,
            fmt_us(s.cpu_kg),
            fmt_us(s.gpu_kg1),
            fmt_us(s.gpu_kg64_per),
            fmt_us(s.cpu_sign),
            fmt_us(s.gpu_sign1),
            fmt_us(s.gpu_sign64_per),
            spd
        );
    }
}
