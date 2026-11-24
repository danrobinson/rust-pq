# Optimized SLH-DSA peers on seven platforms

Measured November 23, 2026. Across deterministic signing workloads, rust-pq had lower paired median latency in **168/168** comparisons with Botan, **56/56** with single-threaded Conduition and **89/96** with single-threaded Fluhrer. Each comparison uses one CPU, one supported parameter set and one message size.

## Deterministic signing

Numbers are peer latency divided by rust-pq latency. **Above 1 favors rust-pq.** Each entry is a geometric mean of per-workload paired median ratios across the peer's supported sets and both message sizes. Botan and Fluhrer cover all twelve sets, Conduition's CPU builds cover four 128-bit sets, and its GPU build covers the two SHA2-128 sets on Apple. Each column compares the peer with rust-pq on the same workload.

| CPU | Botan | Conduition SIMD | Conduition cached + threaded | Fluhrer 1T | Fluhrer 2T | Conduition GPU |
|---|---:|---:|---:|---:|---:|---:|
| Apple M5 Ultra | 2.77× | 4.14× | 2.49× | — | — | 1.15× |
| Xeon 8275CL | 3.19× | 5.95× | 5.55× | 1.42× | 1.34× | — |
| Xeon 8124M | 3.61× | 6.23× | 5.83× | 1.45× | 1.37× | — |
| Xeon 6975P-C | 2.07× | 5.35× | 4.51× | 1.42× | 1.26× | — |
| EPYC 9R45 | 2.43× | 6.61× | 4.10× | 1.57× | 0.87× | — |
| Graviton2 | 4.02× | 3.80× | 2.26× | — | — | — |
| Graviton4 | 4.46× | 3.58× | 2.12× | — | — | — |

- **Apple GPU.** On SHA2-128s signing of 32 bytes, Conduition OpenCL took **12.63 ms** and rust-pq took **32.92 ms**. On SHA2-128f, OpenCL took **4.10 ms** and rust-pq took **1.70 ms**. OpenCL context creation and kernel compilation were outside the timers. The six EC2 CPU instances have no GPU.
- **EPYC multicore signing.** Across the six SHAKE sets and both message lengths, Fluhrer's two-thread implementation was **1.64× faster** than rust-pq. Across the six SHA-2 sets, rust-pq was **1.23× faster**. The EPYC instance has two physical cores. Intel instances expose two hardware threads on one physical core.
- **Single-threaded x86 signing.** All seven workloads in which single-threaded Fluhrer had lower median latency were SHAKE on the Xeon 6975P-C. Its largest lead was about 7%, on SHAKE-192s with a 32-byte message.
- **Repeated signing.** The cached Conduition build computes its root-tree cache during key generation and reuses it when signing. The separate cached sweep includes its construction cost in the key-generation measurement and enables the upstream multithread feature.

## Key generation

| CPU | Botan | Conduition SIMD | Conduition cached + threaded | Fluhrer 1T | Fluhrer 2T | Conduition GPU |
|---|---:|---:|---:|---:|---:|---:|
| Apple M5 Ultra | 2.95× | 4.06× | 4.09× | — | — | 8.83× |
| Xeon 8275CL | 3.42× | 6.61× | 6.56× | 1.61× | 1.61× | — |
| Xeon 8124M | 3.87× | 6.79× | 6.84× | 1.60× | 1.61× | — |
| Xeon 6975P-C | 1.93× | 5.19× | 5.21× | 1.47× | 1.47× | — |
| EPYC 9R45 | 2.04× | 6.78× | 6.79× | 1.66× | 1.66× | — |
| Graviton2 | 5.02× | 3.93× | 3.93× | — | — | — |
| Graviton4 | 5.11× | 3.66× | 3.66× | — | — | — |

## Verification

| CPU | Botan | Conduition SIMD | Conduition cached + threaded | Fluhrer 1T | Fluhrer 2T | Conduition GPU |
|---|---:|---:|---:|---:|---:|---:|
| Apple M5 Ultra | 2.04× | 4.35× | 4.48× | — | — | 6.57× |
| Xeon 8275CL | 2.07× | 5.58× | 5.60× | 1.49× | 1.49× | — |
| Xeon 8124M | 2.33× | 5.62× | 5.64× | 1.54× | 1.54× | — |
| Xeon 6975P-C | 1.60× | 5.85× | 5.90× | 1.54× | 1.55× | — |
| EPYC 9R45 | 1.93× | 6.04× | 6.09× | 1.60× | 1.61× | — |
| Graviton2 | 2.85× | 3.51× | 3.52× | — | — | — |
| Graviton4 | 3.18× | 3.44× | 3.45× | — | — | — |

The operation-level CSV also includes hedged signing and public-key extraction. The workload CSV gives absolute nanosecond timings, round counts, and the minimum and maximum observed paired ratio for each comparison. Small differences are sensitive to scheduler and measurement noise, especially on the shared Apple host. This comparison measures API latency including the setup performed by each driver. It does not measure sustained server throughput.

## Data and reproduction

- [Absolute timings and ratios for every workload](workloads.csv)
- [Operation aggregates and win counts](operations.csv)
- [Raw samples and host/compiler metadata](hosts/)
- [Build commands, upstream revisions, thread placement, timing and validation](../../optimized-peers/README.md)

Every recorded round passed full byte-for-byte comparisons of private keys, public keys, deterministic signatures and hedged signatures against rust-pq. All peers verified their deterministic signatures and rejected a changed message or context. The warm-up rounds are preserved in the raw files and excluded from the summary.
