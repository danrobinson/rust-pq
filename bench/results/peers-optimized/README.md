# Optimized SLH-DSA peer benchmarks

The library led in 2,683 of 2,688 workload–peer comparisons by median paired latency. The original baseline led in 2,049. In the new run, 2,635 comparisons favored the library in all six measured pairs.

All twelve parameter sets ran on seven CPUs against OpenSSL 4.1.0 and RustCrypto SLH-DSA 0.2.0-rc.5. The matrix covers seeded key generation, public-key extraction, deterministic signing, hedged signing and verification at 32 bytes and 1 MiB, plus raw and DER key conversions. Each workload ran once as warm-up and six more times, once per provider order. [Reproduction and timing method](../../peers/README.md) · [Original baseline](../peers/README.md)

Linux ran each provider on CPU 0 of a dedicated EC2 instance. Apple used normal scheduling on a shared developer machine with concurrent Lean jobs. The paired sample ranges show the observed variation. Margins of a few percent on that host are sensitive to scheduling and load.

## Results by operation

Each count gives the number of workloads with a median paired latency ratio strictly above one, meaning the library ran faster than the named peer.

| Operation | Workloads | Wins vs OpenSSL | Wins vs RustCrypto |
|---|---:|---:|---:|
| Key generation | 168 | 168 | 168 |
| Public-key extraction | 168 | 168 | 164 |
| Deterministic signing | 168 | 168 | 168 |
| Hedged signing | 168 | 168 | 168 |
| Verification | 168 | 167 | 168 |
| Raw private-key import | 84 | 84 | 84 |
| Raw public-key import | 84 | 84 | 84 |
| PKCS#8 encode | 84 | 84 | 84 |
| PKCS#8 decode | 84 | 84 | 84 |
| SPKI encode | 84 | 84 | 84 |
| SPKI decode | 84 | 84 | 84 |

## SHAKE signing

The ratios are peer latency divided by library latency, aggregated as the geometric mean across the six parameters and both message lengths.

| CPU | vs OpenSSL | vs RustCrypto |
|---|---:|---:|
| Apple M5 Ultra | 2.41× | 3.87× |
| Xeon Platinum 8275CL | 5.32× | 12.99× |
| Xeon Platinum 8124M | 6.02× | 14.64× |
| EPYC 9R45 | 6.39× | 14.50× |
| Xeon 6975P-C | 4.99× | 10.56× |
| Graviton2 | 1.30× | 2.67× |
| Graviton4 | 1.50× | 5.75× |

## SHAKE verification

The ratios are peer latency divided by library latency, aggregated as the geometric mean across the six parameters and both message lengths.

| CPU | vs OpenSSL | vs RustCrypto |
|---|---:|---:|
| Apple M5 Ultra | 1.80× | 2.62× |
| Xeon Platinum 8275CL | 3.03× | 6.30× |
| Xeon Platinum 8124M | 3.42× | 7.11× |
| EPYC 9R45 | 3.01× | 5.79× |
| Xeon 6975P-C | 2.87× | 5.13× |
| Graviton2 | 1.16× | 2.02× |
| Graviton4 | 1.31× | 4.23× |

## SHA-2 signing

The ratios are peer latency divided by library latency, aggregated as the geometric mean across the six parameters and both message lengths.

| CPU | vs OpenSSL | vs RustCrypto |
|---|---:|---:|
| Apple M5 Ultra | 1.85× | 1.87× |
| Xeon Platinum 8275CL | 7.36× | 11.92× |
| Xeon Platinum 8124M | 8.29× | 13.38× |
| EPYC 9R45 | 4.02× | 4.69× |
| Xeon 6975P-C | 3.75× | 4.18× |
| Graviton2 | 2.06× | 2.48× |
| Graviton4 | 2.37× | 3.24× |

## SHA-2 verification

The ratios are peer latency divided by library latency, aggregated as the geometric mean across the six parameters and both message lengths.

| CPU | vs OpenSSL | vs RustCrypto |
|---|---:|---:|
| Apple M5 Ultra | 1.47× | 1.40× |
| Xeon Platinum 8275CL | 2.61× | 4.20× |
| Xeon Platinum 8124M | 2.93× | 4.73× |
| EPYC 9R45 | 1.98× | 2.28× |
| Xeon 6975P-C | 1.90× | 2.05× |
| Graviton2 | 1.56× | 1.67× |
| Graviton4 | 1.66× | 1.99× |

## Change in SHAKE latency

Each number divides the original library latency by the optimized library latency. The geometric mean covers all six parameter sets. Signing and verification are shown separately by input size. Both runs used matching CPU models, and EC2 instances were provisioned separately.

| CPU | Keygen, 32 B row | Sign 32 B | Sign 1 MiB | Verify 32 B | Verify 1 MiB |
|---|---:|---:|---:|---:|---:|
| Apple M5 Ultra | 3.30× | 2.76× | 2.74× | 2.89× | 2.42× |
| Xeon Platinum 8275CL | 9.56× | 9.34× | 8.54× | 7.42× | 3.78× |
| Xeon Platinum 8124M | 10.72× | 10.47× | 9.61× | 8.43× | 4.25× |
| EPYC 9R45 | 10.58× | 10.36× | 8.53× | 8.33× | 2.44× |
| Xeon 6975P-C | 8.09× | 7.93× | 7.13× | 6.71× | 3.05× |
| Graviton2 | 2.14× | 2.12× | 2.10× | 2.05× | 1.81× |
| Graviton4 | 2.47× | 2.47× | 2.45× | 2.37× | 2.20× |

## Higher-resolution raw key measurements

The independent raw-key harness measured 100,000 calls per sample, alternated provider order and discarded one warm-up before collecting 20 pairs. The library had a lower median latency than RustCrypto on 252 of 252 CPU, parameter-set and operation combinations. The primary matrix above retains its original 256-call timing method. [All high-resolution ratios](raw-key-workloads.csv) · [Samples](raw-key-samples.csv.gz) · [Harness](../../peers/raw-keys.rs)


## Workloads at or below parity

The table includes every paired median at or below one. Key-copy measurements operate on fixed-size values and include the overhead of each provider’s public API.

| CPU | Set | Message bytes | Operation | Peer | Peer / library |
|---|---|---:|---|---|---:|
| Xeon Platinum 8275CL | sha2_128s | 1048576 | Verification | OpenSSL | 0.9307× |
| Xeon Platinum 8275CL | shake_128s | 1048576 | Public-key extraction | RustCrypto | 0.9972× |
| Xeon Platinum 8275CL | shake_128s | 32 | Public-key extraction | RustCrypto | 0.9158× |
| Graviton4 | sha2_128s | 1048576 | Public-key extraction | RustCrypto | 0.9236× |
| Graviton4 | sha2_128s | 32 | Public-key extraction | RustCrypto | 0.9626× |

## Source and validation

The x86-64 runs used commit `f9b7697`. The extraction-friendly SHA-512 schedule helper in `dd25d99` emitted the same 3,335 assembly lines for the prescheduled function after normalizing local label numbers. The Graviton runs used `4ceac15`. The intervening change specializes SHA-512 schedule indices inside the x86-64 module. The Graviton sources and build settings are identical between these commits. Apple used `a447738`, which keeps the SHA3 sponge in vector registers between message blocks. [x86 schedule](../../../rust/src/sha512/stream.rs) · [Benchmark drivers](../../peers)

Every run checked the complete keys, deterministic and hedged signatures, DER encodings, verification with the intended context and rejection under a different context. The input/output digests matched across all seven CPUs. Both crates passed their release tests on each host. A separate differential test checked every possible rate offset and four message tails against RustCrypto SHAKE256 on each CPU. [Signature checks](checks.csv) · [Encoding checks](encoding-checks.csv) · [Test counts](tests.csv)

[Full API results](workloads.csv) · [Key conversion results](encoding-workloads.csv) · [API samples](samples.csv.gz) · [Conversion samples](encoding-samples.csv.gz) · [Host metadata](hosts/) · [AWS resource teardown](cleanup.json)
