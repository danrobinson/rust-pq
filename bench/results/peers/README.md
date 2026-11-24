# SLH-DSA benchmarks against OpenSSL and RustCrypto

OpenSSL 4.1.0 and RustCrypto SLH-DSA 0.2.0-rc.5 ran alongside the frozen platform-optimized library on all seven CPUs. The run covers 840 public API workloads and 504 key conversion workloads. Each reports six timed comparisons after warm-up. [Method and reproducible drivers](../../peers/README.md) · [Per-workload times and ranges](workloads.csv) · [Key conversion results](encoding-workloads.csv)

## SHA-2

The values are peer latency divided by this library’s latency. **Above 1× means this library was faster.** Each entry gives the geometric mean of the paired median ratios across the six parameter sets and both message lengths.

| CPU | Keygen vs OpenSSL | Keygen vs RustCrypto | Sign vs OpenSSL | Sign vs RustCrypto | Verify vs OpenSSL | Verify vs RustCrypto |
|---|---:|---:|---:|---:|---:|---:|
| Apple M5 Ultra | 1.87× | 2.07× | 1.83× | 1.90× | 1.46× | 1.44× |
| Xeon Platinum 8275CL | 11.91× | 20.87× | 8.26× | 13.35× | 2.90× | 4.68× |
| Xeon Platinum 8124M | 11.92× | 20.86× | 8.26× | 13.33× | 2.89× | 4.69× |
| EPYC 9R45 | 4.63× | 5.74× | 3.98× | 4.68× | 1.91× | 2.20× |
| Xeon 6975P-C | 4.03× | 5.07× | 3.73× | 4.17× | 1.88× | 2.03× |
| Graviton2 | 2.31× | 3.28× | 2.06× | 2.48× | 1.56× | 1.67× |
| Graviton4 | 2.47× | 3.66× | 2.37× | 3.25× | 1.66× | 2.00× |

OpenSSL had the lower SHA-2 verification latency in one of the 84 workloads. EPYC took 1.090 ms with OpenSSL and 1.118 ms with this library to verify a 1 MiB message with SHA2-192s. [Paired verification measurements](workloads.csv)

## SHAKE

The values are peer latency divided by this library’s latency. **Above 1× means this library was faster.** Each entry gives the geometric mean of the paired median ratios across the six parameter sets and both message lengths.

| CPU | Keygen vs OpenSSL | Keygen vs RustCrypto | Sign vs OpenSSL | Sign vs RustCrypto | Verify vs OpenSSL | Verify vs RustCrypto |
|---|---:|---:|---:|---:|---:|---:|
| Apple M5 Ultra | 0.54× | 0.99× | 0.53× | 0.96× | 0.46× | 0.71× |
| Xeon Platinum 8275CL | 0.60× | 1.46× | 0.59× | 1.44× | 0.57× | 1.18× |
| Xeon Platinum 8124M | 0.60× | 1.46× | 0.59× | 1.44× | 0.57× | 1.18× |
| EPYC 9R45 | 0.69× | 1.57× | 0.69× | 1.56× | 0.68× | 1.30× |
| Xeon 6975P-C | 0.67× | 1.48× | 0.66× | 1.45× | 0.64× | 1.17× |
| Graviton2 | 0.62× | 1.28× | 0.61× | 1.26× | 0.60× | 1.05× |
| Graviton4 | 0.62× | 2.40× | 0.61× | 2.34× | 0.57× | 1.86× |

This library had the lower median paired deterministic signing latency in 84 of 84 SHA-2 workloads and 0 of 84 SHAKE workloads against OpenSSL.

This library had the lower median paired deterministic signing latency in 84 of 84 SHA-2 workloads and 75 of 84 SHAKE workloads against RustCrypto.

## Absolute signing latency

These are the median milliseconds to sign a 32-byte message deterministically with the SHA2-128s parameter set.

| CPU | This library | OpenSSL | RustCrypto |
|---|---:|---:|---:|
| Apple M5 Ultra | 30.55 | 55.99 | 65.16 |
| Xeon Platinum 8275CL | 32.48 | 403.82 | 696.15 |
| Xeon Platinum 8124M | 34.52 | 427.54 | 739.60 |
| EPYC 9R45 | 21.53 | 100.27 | 126.27 |
| Xeon 6975P-C | 28.35 | 116.83 | 147.02 |
| Graviton2 | 64.93 | 154.45 | 223.17 |
| Graviton4 | 49.72 | 119.48 | 176.57 |

## Additional operations

The full data include public-key extraction, hedged signing, raw key import, and PKCS#8 and SPKI processing. Key extraction and conversion compare concrete API representations and their allocation costs. The tiny Rust byte-copy timings can be sensitive to code generation and elapsed-time resolution. [All signing API aggregates](aggregate.csv) · [Conversion aggregates](encoding-aggregate.csv)

## Validation

All three implementations agreed on every private key, public key, deterministic signature, hedged signature, PKCS#8 private key and SPKI public key compared. Each provider accepted the deterministic signature and rejected the wrong context for each signing workload. Each DER decoder recovered the original key bytes. The 98 signature-workload digest records and 49 DER-workload digest records matched across CPUs for identical inputs. [Signature checks](checks.csv) · [Encoding checks](encoding-checks.csv)

The raw sample archives include the warm-up and measured rounds. The summaries discard round zero. Linux ran single-threaded with CPU 0 affinity. The Apple run used normal OS scheduling. The resource audit covers the benchmark EC2 instances and the temporary security groups and key pairs. [Public API samples](samples.csv.gz) · [Conversion samples](encoding-samples.csv.gz) · [Host metadata](hosts/) · [EC2 teardown](cleanup.json)
