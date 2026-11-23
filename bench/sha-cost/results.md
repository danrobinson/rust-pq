# SLH-DSA time relative to raw SHA work

The subsequent optimization study measures all six parameter sets on six processors. [Latest measurements](../headroom.md)

The subsequent x86 measurements cover wider SHA-NI and AVX-512 kernels on AMD and Intel. [Updated x86 results](../wide-x86.md)

Each ratio is measured API time divided by the time to do its SHA-256 and SHA-512 compression blocks at the raw kernel rates below. A ratio of 1.25 means 25% extra elapsed time. The primary comparison uses dedicated SHA instructions where exposed. Where the CPU lacks an extension, it uses the fastest complete software kernel measured.

## SHA2-128s, 32-byte messages

| CPU | SHA-256 ns/block | SHA-512 ns/block | Keygen | Sign | Verify | Sign vs round reference |
|---|---:|---:|---:|---:|---:|---:|
| C5 · Xeon 8275CL | 19.81 | 50.47 | 4.065× | 4.031× | 7.312× | 4.031× |
| C8i · Xeon 6975P-C | 28.91 | 45.70 | 1.201× | 1.210× | 1.400× | 1.420× |
| C8a · EPYC 9R45 | 14.58 | 26.39 | 2.012× | 2.009× | 2.319× | 2.069× |
| Graviton2 | 26.72 | 315.00 | 1.058× | 1.097× | 1.381× | 2.509× |
| Graviton4 | 20.75 | 64.50 | 1.054× | 1.080× | 1.334× | 2.157× |
| Apple M5 Ultra | 15.15 | 38.50 | 0.948× | 0.967× | 1.130× | 1.078× |

## Signing across all six parameter sets, 32-byte messages

| CPU | 128s | 128f | 192s | 192f | 256s | 256f |
|---|---:|---:|---:|---:|---:|---:|
| C5 · Xeon 8275CL | 4.031× | 4.493× | 4.210× | 4.393× | 4.359× | 4.190× |
| C8i · Xeon 6975P-C | 1.210× | 1.244× | 1.621× | 1.534× | 1.806× | 1.554× |
| C8a · EPYC 9R45 | 2.009× | 2.059× | 2.484× | 2.395× | 2.677× | 2.410× |
| Graviton2 | 1.097× | 1.151× | 1.493× | 1.449× | 1.576× | 1.444× |
| Graviton4 | 1.080× | 1.122× | 1.461× | 1.378× | 1.604× | 1.368× |
| Apple M5 Ultra | 0.967× | 1.025× | 1.108× | 1.105× | 1.172× | 1.116× |

Results for key generation, signing and verification on 32-byte and 1 MiB messages, including the six-round range and alternative baselines, are in the [full results](overhead.csv). The [operation counts](counts.csv) and [raw nanosecond samples](samples.csv.gz) identify the workload and kernel used for each observation.

## What was measured

- The portable code was instrumented in a temporary copy. Each public operation ran once on the identical seeds, messages and deterministic signatures used in its timing round. Counts include padding blocks, HMAC, and prefix-state setup and reuse. They describe the current algorithm and input. They are not a proof of a minimum across algorithms or key-caching strategies.
- The timed executable was uninstrumented, using the ordinary release build with platform-sha2. On each machine, one warmup and six measured rounds alternated the order of the raw-kernel and API measurements. Each verification sample averaged 32 calls. The EC2 runs used vCPU 0. The local macOS run used the OS scheduler. Both timings were repeated on the same machine, including the replacement C5 host, which exposed a Xeon 8275CL instead of the earlier 8223CL.
- A SHA-256 block is 64 bytes and a SHA-512 block is 128 bytes. Independent-message kernels include message expansion, rounds and feed-forward. The generic SIMD kernels start with transposed, big-endian message words. The native SHA kernels load byte blocks. Each independent kernel was checked lane by lane against OpenSSL on distinct inputs and states. Streaming OpenSSL updates on 16 KiB buffers supplied the single-stream comparison. Rates exclude digest initialization and finalization, which would double-count work for SLH-DSA’s pre-padded blocks.
- For each algorithm and host, the eligible kernel with the lowest six-round median was selected once. Each round then uses its own rates in the weighted cost, `n256 * ns256 + n512 * ns512`. Reported ratios are medians of the six paired ratios. Independent-message saturation assumes enough useful work to fill the lanes. Serial message blocks, authentication paths, partial batches and uneven chains can prevent SLH-DSA from attaining that rate.
- The round reference times streams of independent H/H2 or RNDS2 instructions, omitting message scheduling and feed-forward. For software-only algorithms it retains the measured complete-kernel rate. The Arm SHA-256 count subtracts the two instructions saved per chain step by reusing the first group, charges the two instructions once per distinct consecutive active prefix within each batch, and subtracts the unused final H2 on 128-bit chains. This models empirical instruction throughput, not a proven cycle lower bound. Full-block ratios can fall below 1 when the algorithm skips this work.

## Kernel choices

- C5 · Xeon 8275CL used `vec256_16` for SHA-256 and `vec512_8` for SHA-512.
- C8i · Xeon 6975P-C used `x86256_2` for SHA-256 and `vec512_8` for SHA-512.
- C8a · EPYC 9R45 used `x86256_8` for SHA-256 and `vec512_8` for SHA-512.
- Graviton2 used `arm256_4` for SHA-256 and `bulk512` for SHA-512.
- Graviton4 used `arm256_4` for SHA-256 and `arm512_2` for SHA-512.
- Apple M5 Ultra used `arm256_4` for SHA-256 and `arm512_4` for SHA-512.

The suffix denotes independent lanes. The x86 EC2 hosts exposed no dedicated SHA-512 instructions. C5 also lacked SHA-NI. Graviton2 had SHA-256 instructions only. Graviton4 and Apple exposed both SHA extensions. The AVX-512 comparison in the CSV admits vector software even where SHA-NI exists. The generator uses the project’s round constants. [Kernel generator](generate.py)
