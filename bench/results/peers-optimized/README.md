# Optimized SLH-DSA peer benchmarks

All twelve parameter sets ran on seven CPUs against OpenSSL 4.1.0 and RustCrypto SLH-DSA 0.2.0-rc.5. The matrix covers seeded key generation, public-key extraction, deterministic signing, hedged signing and verification at 32 bytes and 1 MiB, plus raw and DER key conversions. Each workload ran once as warm-up and six more times, once per provider order. [Reproduction and timing method](../../peers/README.md)

Linux ran each provider on CPU 0 of a dedicated EC2 instance. Apple used normal scheduling on a shared developer machine with concurrent Lean jobs. The paired sample ranges show the observed variation. Margins of a few percent on that host are sensitive to scheduling and load.

## Results by operation

Each cell is the geometric mean of the paired median speedups, giving each measured processor, parameter set and message size equal weight within that peer and operation. Ratios above 1× favor rust-pq.

| Operation | vs OpenSSL | vs RustCrypto |
|---|---:|---:|
| Key generation | 3.92× | 7.05× |
| Public-key extraction | 13.82× | 1.86× |
| Deterministic signing | 3.52× | 6.01× |
| Hedged signing | 3.51× | 6.00× |
| Verification | 2.09× | 3.22× |
| Raw private-key import | 639.13× | 2.01× |
| Raw public-key import | 744.87× | 1.86× |
| PKCS#8 encode | 1192.33× | 17.59× |
| PKCS#8 decode | 575.18× | 26.28× |
| SPKI encode | 1034.67× | 11.73× |
| SPKI decode | 654.30× | 27.33× |

## SHAKE signing

The ratios are peer latency divided by library latency, aggregated as the geometric mean across the six parameters and both message lengths.

| CPU | vs OpenSSL | vs RustCrypto |
|---|---:|---:|
| Apple M5 Ultra | 2.59× | 3.80× |
| Xeon Platinum 8275CL | 5.30× | 12.85× |
| Xeon Platinum 8124M | 5.99× | 14.51× |
| EPYC 9R45 | 6.38× | 14.37× |
| Xeon 6975P-C | 5.00× | 10.99× |
| Graviton2 | 1.30× | 2.67× |
| Graviton4 | 1.50× | 5.75× |

## SHAKE verification

The ratios are peer latency divided by library latency, aggregated as the geometric mean across the six parameters and both message lengths.

| CPU | vs OpenSSL | vs RustCrypto |
|---|---:|---:|
| Apple M5 Ultra | 1.91× | 2.44× |
| Xeon Platinum 8275CL | 3.01× | 6.20× |
| Xeon Platinum 8124M | 3.40× | 7.02× |
| EPYC 9R45 | 3.02× | 5.80× |
| Xeon 6975P-C | 2.88× | 5.33× |
| Graviton2 | 1.16× | 2.02× |
| Graviton4 | 1.31× | 4.23× |

## SHA-2 signing

The ratios are peer latency divided by library latency, aggregated as the geometric mean across the six parameters and both message lengths.

| CPU | vs OpenSSL | vs RustCrypto |
|---|---:|---:|
| Apple M5 Ultra | 1.91× | 1.85× |
| Xeon Platinum 8275CL | 7.42× | 11.96× |
| Xeon Platinum 8124M | 8.30× | 13.35× |
| EPYC 9R45 | 4.02× | 4.65× |
| Xeon 6975P-C | 3.74× | 4.20× |
| Graviton2 | 2.06× | 2.48× |
| Graviton4 | 2.37× | 3.24× |

## SHA-2 verification

The ratios are peer latency divided by library latency, aggregated as the geometric mean across the six parameters and both message lengths.

| CPU | vs OpenSSL | vs RustCrypto |
|---|---:|---:|
| Apple M5 Ultra | 1.53× | 1.42× |
| Xeon Platinum 8275CL | 2.66× | 4.29× |
| Xeon Platinum 8124M | 2.93× | 4.77× |
| EPYC 9R45 | 1.99× | 2.29× |
| Xeon 6975P-C | 1.89× | 2.12× |
| Graviton2 | 1.56× | 1.67× |
| Graviton4 | 1.66× | 1.99× |

## Change in SHAKE latency

Each number divides the original library latency by the optimized library latency. The geometric mean covers all six parameter sets. Signing and verification are shown separately by input size. Both runs used matching CPU models, and EC2 instances were provisioned separately.

| CPU | Keygen, 32 B row | Sign 32 B | Sign 1 MiB | Verify 32 B | Verify 1 MiB |
|---|---:|---:|---:|---:|---:|
| Apple M5 Ultra | 3.10× | 3.04× | 3.04× | 2.95× | 2.47× |
| Xeon Platinum 8275CL | 9.58× | 9.35× | 8.51× | 7.39× | 3.76× |
| Xeon Platinum 8124M | 10.75× | 10.57× | 9.60× | 8.44× | 4.22× |
| EPYC 9R45 | 10.15× | 9.96× | 8.15× | 8.03× | 2.36× |
| Xeon 6975P-C | 8.02× | 7.94× | 7.19× | 6.75× | 3.06× |
| Graviton2 | 2.14× | 2.12× | 2.10× | 2.05× | 1.81× |
| Graviton4 | 2.47× | 2.47× | 2.45× | 2.37× | 2.20× |

## Higher-resolution raw key measurements

The independent raw-key harness measured 100,000 calls per sample, alternated provider order and discarded one warm-up before collecting 20 pairs. The library had a lower median latency than RustCrypto on 252 of 252 CPU, parameter-set and operation combinations. The primary matrix above retains its original 256-call timing method. [All high-resolution ratios](raw-key-workloads.csv) · [Samples](raw-key-samples.csv.gz) · [Harness](../../peers/raw-keys.rs)


## Workloads at or below parity

The table includes every paired median at or below one. Key-copy measurements operate on fixed-size values and include the overhead of each provider’s public API.

| CPU | Set | Message bytes | Operation | Peer | Peer / library |
|---|---|---:|---|---|---:|
| Xeon Platinum 8275CL | sha2_128f | 1048576 | Public-key extraction | RustCrypto | 0.8679× |
| Xeon Platinum 8275CL | sha2_128s | 1048576 | Public-key extraction | RustCrypto | 0.9665× |
| Xeon Platinum 8275CL | sha2_128f | 32 | Public-key extraction | RustCrypto | 0.8848× |
| Graviton4 | sha2_128s | 1048576 | Public-key extraction | RustCrypto | 0.9236× |
| Graviton4 | sha2_128s | 32 | Public-key extraction | RustCrypto | 0.9626× |

The dedicated 100,000-call extraction runs favored the library in all 20 paired samples for each of the three distinct CPU/set combinations above. The machine-code review found only the required copy in the library’s timed loop. [Timing intervals and assembly](key-extraction.md)

## x86 message schedule trials

On the two older Xeons, we compared the original rolled SHA-256 schedule with fixed-index expansion, several equivalent scalar round expressions, and four-, eight- and sixteen-lane schedules. The selected implementation keeps eight consecutive message blocks in 256-bit vectors, and executes their dependent scalar rounds in block order. Both Xeons use AVX-512VL rotate/ternary instructions and AVX2 gather. A separate SHA-512 trial compared the separated schedule table to the unrolled baseline on all four x86 CPUs using SHA2-192s verification and raw hashing of 1 MiB. Each SHA-512 sample measured 100 calls, with three samples per process and five process pairs. [SHA-256 schedule trials](sha256-schedule-trials.csv) · [SHA-256 lane widths](sha256-width-trials.csv) · [SHA-512 table trials](sha512-table-trials.csv)

The focused probes also measured the standalone library hash over the same 1 MiB buffer. The ratios below divide signature verification time by the time for that single input hash. Verification additionally computes the signature-specific tree hashes. For modeled necessary hash counts across whole operations, see the [raw SHA accounting](../../sha-cost/results.md).

| CPU | Parameter set | Verify, ms | Hash 1 MiB, ms | Verify / hash |
|---|---|---:|---:|---:|
| Xeon Platinum 8275CL | SHA2-192S | 2.009 | 1.875 | 1.076× |
| Xeon Platinum 8275CL | SHA2-128S | 2.719 | 2.489 | 1.092× |
| Xeon Platinum 8124M | SHA2-192S | 1.889 | 1.763 | 1.073× |
| Xeon Platinum 8124M | SHA2-128S | 2.792 | 2.638 | 1.058× |
| EPYC 9R45 | SHA2-192S | 1.015 | 0.947 | 1.065× |
| Xeon 6975P-C | SHA2-192S | 1.526 | 1.426 | 1.069× |

## Source and validation

The x86-64 builds used the combined SHA-256 and SHA-512 sources from `deb57d6`, including the verified forced-software dispatch. Graviton used `4ceac15`, and Apple used `424109e`, which retains the SHA3 sponge in vector registers between blocks and writes it back through fixed indices. Later changes to these Graviton runs’ source are compile-gated to Apple or x86. [SHA-256 schedule](../../../rust/src/sha256/stream.rs) · [SHA-512 schedule](../../../rust/src/sha512/stream.rs) · [Benchmark drivers](../../peers)

Every run checked the complete keys, deterministic and hedged signatures, DER encodings, verification with the intended context and rejection under a different context. The input/output digests matched across all seven CPUs. Both crates passed their release tests on each host. A separate differential test checked every possible rate offset and four message tails against RustCrypto SHAKE256 on each CPU. [Signature checks](checks.csv) · [Encoding checks](encoding-checks.csv) · [Test counts](tests.csv)

[Full API results](workloads.csv) · [Key conversion results](encoding-workloads.csv) · [API samples](samples.csv.gz) · [Conversion samples](encoding-samples.csv.gz) · [Host metadata](hosts/) · [AWS resource teardown](cleanup.json)
