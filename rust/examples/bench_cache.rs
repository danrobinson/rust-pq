//! Benchmark hypertree top-tree caching vs uncached signing across all 12 FIPS 205 sets.
//!
//! Run with:
//!   cargo run --release --features platform-sha2 --example bench_cache
//!   cargo run --release --features parallel --example bench_cache

#[cfg(not(feature = "platform-sha2"))]
fn main() {
    eprintln!(
        "bench_cache requires the `platform-sha2` or `parallel` feature:\n  \
         cargo run --release --features platform-sha2 --example bench_cache"
    );
}

#[cfg(feature = "platform-sha2")]
fn main() {
    use std::hint::black_box;
    use std::time::Instant;

    let rounds_override: Option<usize> = std::env::args()
        .nth(1)
        .and_then(|a| a.parse().ok());

    fn paired_median_ns(
        iters: usize,
        mut a: impl FnMut(),
        mut b: impl FnMut(),
    ) -> (u128, u128) {
        a();
        b();
        let mut sa = Vec::with_capacity(iters);
        let mut sb = Vec::with_capacity(iters);
        for _ in 0..iters {
            let t0 = Instant::now();
            a();
            sa.push(t0.elapsed().as_nanos());
            let t1 = Instant::now();
            b();
            sb.push(t1.elapsed().as_nanos());
        }
        sa.sort_unstable();
        sb.sort_unstable();
        (sa[sa.len() / 2], sb[sb.len() / 2])
    }

    fn fmt_time(ns: u128) -> String {
        if ns >= 1_000_000 {
            format!("{:>8.2} ms", ns as f64 / 1e6)
        } else {
            format!("{:>8.1} us", ns as f64 / 1e3)
        }
    }

    fn fmt_mem(bytes: usize) -> String {
        if bytes >= 1024 {
            format!("{:>6.1} KiB", bytes as f64 / 1024.0)
        } else {
            format!("{:>6} B  ", bytes)
        }
    }

    let mode = if cfg!(feature = "parallel") {
        "parallel (multicore)"
    } else {
        "platform-sha2 (single-core)"
    };
    println!("SLH-DSA Hypertree Top-Tree Cache Benchmark — {mode}");
    println!("Message: 32 bytes | deterministic pure signing | median latency\n");
    println!(
        "{:<11} {:>10} {:>11} {:>11} {:>9} {:>11} {:>11}",
        "Set", "Cache RAM", "Uncached", "Top-Cached", "Speedup", "Keygen", "KG+Cache"
    );
    println!("{}", "-".repeat(82));

    let msg = [0x5au8; 32];

    macro_rules! bench_one {
        ($set:ident, $default_iters:expr, $bench_d2:expr) => {{
            use slhdsa::$set as base;
            use slhdsa::$set::params::*;
            use slhdsa::cache::$set as c;

            let iters = rounds_override.unwrap_or($default_iters);
            let seeds = [0x33u8; SEED_BYTES];
            let mut sk = [0u8; SK_BYTES];
            let mut pk = [0u8; PK_BYTES];

            let mut sk_tmp = [0u8; SK_BYTES];
            let mut pk_tmp = [0u8; PK_BYTES];
            let mut cache = c::keygen_with_cache(&seeds, &mut sk, &mut pk);
            let (kg_ns, kg_cache_ns) = paired_median_ns(
                iters.min(5),
                || {
                    base::api::keygen(
                        black_box(&seeds),
                        black_box(&mut sk_tmp),
                        black_box(&mut pk_tmp),
                    );
                },
                || {
                    cache = c::keygen_with_cache(
                        black_box(&seeds),
                        black_box(&mut sk),
                        black_box(&mut pk),
                    );
                },
            );

            // Sanity check byte-for-byte identity before timing.
            let ref_sig = base::api::sign_deterministic(&msg, b"", &sk).unwrap();
            let cached_sig = c::sign_deterministic_cached(&msg, b"", &sk, &cache).unwrap();
            assert_eq!(ref_sig, cached_sig, "signature mismatch on {}", stringify!($set));

            let (uncached_ns, cached_ns) = paired_median_ns(
                iters,
                || {
                    let s = base::api::sign_deterministic(black_box(&msg), b"", black_box(&sk))
                        .unwrap();
                    black_box(s);
                },
                || {
                    let s = c::sign_deterministic_cached(
                        black_box(&msg),
                        b"",
                        black_box(&sk),
                        black_box(&cache),
                    )
                    .unwrap();
                    black_box(s);
                },
            );

            let speedup = uncached_ns as f64 / cached_ns as f64;
            println!(
                "{:<11} {:>10} {:>11} {:>11} {:>8.2}x {:>11} {:>11}",
                stringify!($set),
                fmt_mem(cache.memory_bytes()),
                fmt_time(uncached_ns),
                fmt_time(cached_ns),
                speedup,
                fmt_time(kg_ns),
                fmt_time(kg_cache_ns),
            );

            if $bench_d2 {
                let mut d2 = cache.clone();
                c::precompute_layer_d2(&mut d2, &sk);
                let d2_sig = c::sign_deterministic_cached(&msg, b"", &sk, &d2).unwrap();
                assert_eq!(ref_sig, d2_sig);
                let (u2_ns, d2_ns) = paired_median_ns(
                    iters,
                    || {
                        let s = base::api::sign_deterministic(black_box(&msg), b"", black_box(&sk))
                            .unwrap();
                        black_box(s);
                    },
                    || {
                        let s = c::sign_deterministic_cached(
                            black_box(&msg),
                            b"",
                            black_box(&sk),
                            black_box(&d2),
                        )
                        .unwrap();
                        black_box(s);
                    },
                );
                let d2_speedup = u2_ns as f64 / d2_ns as f64;
                println!(
                    "  +layer d-2 {:>9} {:>11} {:>11} {:>8.2}x  ({} d-2 trees)",
                    fmt_mem(d2.memory_bytes()),
                    fmt_time(u2_ns),
                    fmt_time(d2_ns),
                    d2_speedup,
                    d2.layer_d2_cached_trees(),
                );
            }
        }};
    }

    bench_one!(sha2_128s, 5, false);
    bench_one!(sha2_128f, 15, true);
    bench_one!(sha2_192s, 5, false);
    bench_one!(sha2_192f, 15, true);
    bench_one!(sha2_256s, 5, false);
    bench_one!(sha2_256f, 11, true);

    println!("{}", "-".repeat(82));

    bench_one!(shake_128s, 3, false);
    bench_one!(shake_128f, 11, true);
    bench_one!(shake_192s, 3, false);
    bench_one!(shake_192f, 9, true);
    bench_one!(shake_256s, 3, false);
    bench_one!(shake_256f, 7, true);
}
