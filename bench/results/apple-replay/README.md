# Apple M5 Ultra benchmark replication

Deterministic signing latency on November 24, 2026. Each workload pairs one parameter set with one message length (32 bytes or 1 MiB). Each row reports the geometric mean and range of the workload medians. A ratio of 2× means rust-pq took half the peer’s time.

| Peer | Workloads | Speedup | Range |
|---|---:|---:|---:|
| RustCrypto | 24 | 2.69× | 1.66–3.99× |
| OpenSSL | 24 | 1.95× | 1.58–2.15× |
| Botan | 24 | 2.67× | 2.21–3.21× |
| Conduition SIMD | 8 | 3.88× | 3.46–4.27× |
| Conduition cached and threaded | 8 | 2.34× | 1.68–3.62× |
| Conduition OpenCL | 4 | 1.09× | 0.36–3.31× |

For a 32-byte message using SHA2-128s, median signing latency was 30.11 ms for rust-pq, 55.41 ms for OpenSSL and 62.20 ms for RustCrypto. For SHAKE-128s the same calls took 133.21 ms, 283.61 ms and 532.28 ms.

The RustCrypto and OpenSSL sweep rebuilt the benchmark at rust-pq commit `e0273b3` with the locked Rust dependencies and Homebrew OpenSSL 4.1.0. The drivers compared complete keys and signatures byte for byte. The output digests for every round and length also match the seven-platform dataset. Key conversions ran separately with the same byte checks for DER. [Signing samples](samples.csv.gz) · [Signature checks](checks.csv) · [Key-conversion samples](encoding-samples.csv.gz) · [Encoding checks](encoding-checks.csv) · [Host and compiler](host.txt) · [Reproduction](../../peers/README.md)

The Botan and Conduition sweeps reused the Apple benchmark binaries from the pinned comparison and checked complete keys and signatures against rust-pq at every supported set, round and length. Each sweep used one warm-up and four measured rounds. [Botan, SIMD and OpenCL samples](optimized.csv.gz) · [Cached and threaded samples](cached.csv.gz) · [Executable hashes](peer-binaries.sha256) · [Builds and timing protocol](../../optimized-peers/README.md)

The replication covers one machine under normal macOS scheduling. The six Linux hosts, including the x86-only Fluhrer comparisons, were checked by regenerating their tables from the recorded samples. The seven-processor summary gives each processor equal weight. Its largest 32-byte signing ratio, 21.3× against RustCrypto, comes from SHA2-128s on the Xeon 8124M, with median latencies of 34.5 ms and 734.2 ms. [Per-workload latencies and paired ratios](../peers-optimized/workloads.csv)
