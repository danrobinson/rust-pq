# SLH-DSA platform benchmarks

The subsequent optimization study measures all six parameter sets on six processors. [Latest measurements](headroom.md)

The subsequent x86 measurements cover wider SHA-NI and AVX-512 kernels on AMD and Intel. [Updated x86 results](wide-x86.md)

## Optimization plan and implementation

1. Measure the public key-generation, deterministic-signing and verification APIs for all six SHA-2 parameter sets. Compare the default release build with the existing Arm backend and RustCrypto's `slh-dsa` 0.2.0-rc.5. Separate short-message latency from hashing a 1 MiB message.
2. Use runtime dispatch for distributable binaries. On little-endian Arm, reuse the four-chain kernel and the independent SHA-256 and SHA-512 feature probes. On x86-64, use RustCrypto's SHA-2 compression functions for individual blocks and submit complete runs of message blocks together. This amortizes dispatch and allows the SHA-512 backend to schedule adjacent blocks together.
3. Accelerate the WOTS+ and FORS chain batches on SHA-NI processors. Interleave two independent SHA-256 states through the rounds, then continue any longer chain with the single-block backend. On older AVX2 CPUs, process eight messages in parallel with one chain per vector lane and retire lanes as their step ranges end. Counter values, tail lengths and the handling of uneven pairs follow the public step ranges. Keep this implementation opt-in under `platform-sha2`. [RustCrypto backend selection](https://docs.rs/crate/sha2/0.11.1)
4. Measure each candidate on hardware. Compare native code generation and profile-guided optimization (PGO) with ordinary release builds. Retain a CPU-specific build recommendation only where the corresponding configuration was actually measured.
5. Check bytes as well as timing. Run the NIST ACVP vectors, RustCrypto interoperability, differential compression and chain tests, and adapter tests, including stack wiping. Exercise machines with and without SHA-NI and Arm SHA-512. Re-extract the two existing Lean configurations and compare them with the committed translations.

## Reproduce

Run the matrix and test suites from the repository root with Python 3 and Cargo.

```sh
taskset -c 0 python3 bench/platforms.py --native > samples.csv
cargo test --manifest-path rust/Cargo.toml --release --locked --features platform-sha2
cargo test --manifest-path compat/Cargo.toml --release --locked --features platform-sha2
```

On macOS, omit `taskset -c 0`. The runner builds each configuration once, rotates run order, and uses matching seeds and messages across configurations. Each of six measured rounds uses a different seed and message byte. Round zero warms up each build. Each sample times one key generation, one signing, or the average of 32 successful verifications with the same key and signature. Message allocation, compilation and process startup are outside the timer. The peer uses its native key and signature types. Measurements are single-threaded latency on one machine per row. They do not characterize fleet variance, concurrent throughput or tail latency.

For one sample, run `cargo bench --manifest-path rust/Cargo.toml --bench platforms --features platform-sha2 -- 1 32`. The arguments are the round and message length in bytes. Append `rustcrypto` for the peer. To deploy the measured runtime-dispatched build, enable `platform-sha2` on either `slhdsa` or `slhdsa-compat`. For the proved configuration use `hw-sha2` on Arm or the default on x86-64. The x86 intrinsics and external hash backend have differential and interoperability coverage. The existing Lean proofs cover the portable and Arm builds.

## Measurements

The table gives median latency for SHA2-128s on 32-byte messages. Speedups use the median of six matched round-by-round ratios. The last column spans those six-round signing speedups across all six parameter sets.

| Machine | Portable sign | Platform sign | RustCrypto sign | Platform keygen | Platform verify | Signing speedup, all sets |
|---|---:|---:|---:|---:|---:|---:|
| C5 · Xeon 8223CL | 676.5 ms | 190.2 ms | 735.5 ms | 24.93 ms | 335.5 µs | 3.04–3.56× |
| C8i · Xeon 6975P-C | 475.6 ms | 77.9 ms | 147.4 ms | 10.26 ms | 88.8 µs | 4.30–6.10× |
| C8a · EPYC 9R45 | 371.1 ms | 65.1 ms | 125.5 ms | 8.51 ms | 74.9 µs | 4.20–5.72× |
| C6g · Graviton2 | 797.5 ms | 65.0 ms | 223.9 ms | 8.25 ms | 82.1 µs | 4.06–12.28× |
| C8g · Graviton4 | 557.2 ms | 49.7 ms | 176.8 ms | 6.41 ms | 61.4 µs | 6.37–11.21× |
| Apple M5 Ultra | 306.6 ms | 30.1 ms | 62.3 ms | 3.90 ms | 35.0 µs | 7.65–10.16× |

The full results include key generation, signing and verification for each set and message size. The summary gives median, minimum and maximum across measured rounds. The raw CSV includes warmup. [Summary CSV](results/platforms/summary.csv) · [Raw samples](results/platforms/samples.csv.gz)

## Build decisions

- **Modern Intel and AMD.** Ship the runtime-dispatched build. Holding compression and compiler flags fixed, interleaving two chains reduced signing time by a further factor of 1.18–1.28 on C8i and 1.23–1.34 on C8a across the six sets. For 1 MiB messages, batching complete SHA-256 blocks improved 128s verification by another 11% in throughput on C8i and 16% on C8a in the single-chain experiment. SHA-512 batching had smaller, processor-dependent effects.
- **Older Intel.** The C5 exposed AVX2 and lacked SHA-NI. Single-chain compression alone left short-message signing close to baseline. The eight-lane implementation delivered the 3.04–3.56× gains in the table. On a binary built and deployed exclusively for that CPU, `RUSTFLAGS='-C target-cpu=native'` produced another 1.25–1.36× signing speedup across the six sets. The same flag on C8i slowed 128s signing. Keep ordinary code generation for a binary distributed across CPU models.
- **Arm.** Use `hw-sha2` directly or through `platform-sha2`. The gains in the table are from the existing proved Arm kernel. Graviton2 exercised hardware SHA-256 with portable SHA-512, and Graviton4 exercised both instruction sets. Native compilation gave Graviton4 a further 2–6% in signing in the tuning experiment. On the M5 Ultra the median signing times were within 2% of the ordinary Arm hardware build.
- **Profile-guided optimization.** Train on all six parameter sets with a 32-byte message (round 140) and a 1 MiB message (round 141), merge the LLVM profiles, and evaluate on held-out rounds 1–6. For the portable and pre-interleaving platform builds the median paired signing ratios across sets and rounds ranged from 0.98× to 1.02× on C8i, C8a and C8g. The shipped build uses ordinary release settings. This experiment predates both new x86 chain kernels.

The November 22, 2026 EC2 runs used on-demand `.large` instances in `us-east-1`, Amazon Linux 2023 and Rust 1.100.0 with LLVM 23.1.5. Each timed child process was pinned to vCPU 0. The Apple Silicon run used the local macOS machine without affinity. The pilot used baseline revision `be142b7`. The final matrix compares both Cargo features on the same source tree. On x86-64 the earlier `hw-sha2` build used the portable code.

The experiment CSV records intermediate builds. In the pilot, `base` is portable, `previous` is the previous Arm backend, `platform` adds single-block dispatch on x86 and `native` adds host tuning. In the blocking experiment, `scalar` is portable, `initial` uses single-block dispatch, `bulk` adds multi-block processing, `tuned` adds native code generation and `peer` is RustCrypto. The interleaving experiment compares `bulk` with `paired` SHA-NI. The PGO experiment pairs each ordinary binary with its `-pgo` build. All raw rounds include the warmup at index zero. [Experiment samples](results/platforms/experiments.csv.gz)

## Correctness and portability checks

- The core release suite checks all six NIST ACVP sets, malformed and tampered signatures, independently generated keys and signatures, and key encodings. The compatibility suite exercises the public adapter, including its stack-wiping tests.
- The kernel tests compare 200,000 SHA-256 and 50,000 SHA-512 arbitrary states, blocks and offsets against a reference. They check mixed and reversed chain ranges, counter carries, odd batches and independent neighbours for all three digest lengths. The new continuation test checks every message length from 128 to 1,025 bytes across both padding boundaries.
- Graviton4 replayed all 2,961 recorded Arm instruction-wrapper cases. Graviton2 replayed the 1,745 SHA-256 cases and exercised the SHA-512 software fallback. The explicit full-replay script still requires both instruction sets.
- The portable and Arm Aeneas extractions matched the checked-in Lean translations byte-for-byte. The unchanged theorem packages were not rebuilt in this benchmark run. The new x86 backend is outside those extractions.
- Release builds of the core and compatibility crate with default features disabled were type-checked for `aarch64-unknown-none`, `x86_64-unknown-none` and `wasm32-unknown-unknown`. The bare-metal x86-64 target has a soft-float ABI and selects the portable path. These are compile checks, with no performance claims for those targets.
- On all three x86 machines the compression and chain suite passed under AddressSanitizer. The same release kernel suite passed with QEMU exposing a Nehalem CPU, exercising the x86 fallback without AVX2 or SHA-NI.
- For SHA2-128s, the Linux dudect harness compared fixed and random secrets with identical public ranges in two WOTS+ cases and one FORS case. Across three x86 CPUs and two seeds, the largest absolute Welch t statistic across the harness's crops was 2.91, below its 4.5 detection threshold. The intentionally leaky control crossed 111 in every run. This provides empirical coverage of those kernel shapes and input classes. [Timing output](results/platforms/timing.txt) · [Validation counts](results/platforms/validation.txt)
