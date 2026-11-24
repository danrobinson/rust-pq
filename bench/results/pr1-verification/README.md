# Performance of the PR verification fixes

Apple M5 Ultra, release builds. The baseline is the original PR head at `09f7071`. Ratios are throughput after the fixes divided by throughput at baseline. Every parameter set has equal weight.

| Workload | Geometric mean across 12 sets | Range across sets |
|---|---:|---:|
| CPU verification, batch of 64 | 1.002× | 0.95–1.04× |
| Metal key generation, one key | 1.000× | 0.91–1.08× |
| Metal key generation, batch of 64 | 0.998× | 0.98–1.02× |
| Metal signing, one signature | 1.014× | 0.95–1.27× |
| Metal signing, batch of 64 | 0.998× | 0.99–1.01× |

The CPU comparison used eight pairs of separate processes, alternating which binary ran first. For each set, the statistic is the median of the eight paired throughput ratios. The benchmark verifies a repeated valid signature and uses the fastest of five timed iterations in each process. The Metal comparison ran four processes in base/head/head/base order. For each set the ratio uses the geometric mean of its two recorded per-operation latencies per version. These measurements cover this machine and workload. Individual workloads moved in both directions. [CPU measurements](cpu-verify.csv) · [Metal measurements](metal.csv)

To reproduce, build each revision separately, retain both executables and run in the orders above.

```sh
cargo test --manifest-path rust/Cargo.toml --release --locked --features parallel --test parallel_engine --no-run
# Run the emitted test executable with these arguments
# --ignored --exact bench_batch_verify_throughput --nocapture
cargo build --manifest-path metal/Cargo.toml --release --locked --example bench_metal
# Run the emitted bench_metal executable with no arguments
```
