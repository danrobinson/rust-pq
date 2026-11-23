# SLH-DSA single-core performance

This study compares the public key-generation, deterministic-signing and verification APIs with the previous best `platform-sha2` build on the same processor. It covers the six SHA-2 parameter sets, 32-byte and 1 MiB messages, five EC2 instance types and a local Apple M5 Ultra. Key generation takes no message. Its second timing is an independent repeat within the long-message sweep.

## Results

The first table gives final latency for SHA2-128s. Messages are 32 bytes except in the last column.

| Processor | 128s keygen, ms | 128s sign, ms | 128s verify, µs | 128s sign / dedicated SHA | 128s sign / fastest SHA | 128s verify, 1 MiB, ms |
|---|---:|---:|---:|---:|---:|---:|
| Xeon Platinum 8124M (C5) | 4.43 | 34.60 | 82.1 | 0.98× | 0.98× | 2.870 |
| EPYC 9R45 (C8a) | 2.79 | 21.67 | 33.6 | 0.67× | 0.92× | 0.507 |
| Xeon 6975P-C (C8i) | 3.67 | 28.40 | 42.7 | 0.44× | 0.93× | 0.597 |
| Graviton2 (C6g) | 8.25 | 64.92 | 81.3 | 1.10× | 1.10× | 0.844 |
| Graviton4 (C8g) | 6.40 | 49.70 | 60.8 | 1.08× | 1.08× | 0.742 |
| Apple M5 Ultra | 4.22 | 32.50 | 37.6 | 0.96× | 0.96× | 0.359 |

The following ranges span all six parameter sets. Each entry is the median paired speedup for the slowest-improving and fastest-improving sets. A value near 1.00× indicates little change.

| Processor | Keygen | Sign, 32 B | Verify, 32 B | Sign, 1 MiB | Verify, 1 MiB |
|---|---:|---:|---:|---:|---:|
| Xeon Platinum 8124M (C5) | 1.61–1.94× | 1.30–1.92× | 1.76–2.17× | 1.39–1.92× | 1.54–1.83× |
| EPYC 9R45 (C8a) | 1.32–1.41× | 1.18–1.39× | 1.66–1.87× | 1.13–1.39× | 1.08–1.18× |
| Xeon 6975P-C (C8i) | 1.27–1.35× | 1.16–1.33× | 1.63–1.75× | 1.09–1.35× | 1.03–1.17× |
| Graviton2 (C6g) | 1.00–1.12× | 1.00–1.42× | 1.01–1.41× | 1.03–1.49× | 1.47–1.79× |
| Graviton4 (C8g) | 1.00–1.03× | 1.00–1.42× | 1.00–1.32× | 1.03–1.42× | 1.32–1.52× |
| Apple M5 Ultra | 0.98–1.01× | 0.99–1.08× | 1.00–1.06× | 1.01–1.07× | 1.05–1.07× |

The full matrix includes elapsed nanoseconds, the range of the six paired speedups, a host-tuned build, and four ways to compare with raw SHA. Round zero is a warmup. Each measured round varies the input and key seed, rotates build order, and averages 32 successful verifications per sample. Key generation and signing run once per set per round. EC2 samples use one pinned vCPU. macOS uses the OS scheduler. These measurements characterize single-operation latency for the core API. The compatibility adapter was tested for correctness. [216 workload results](results/headroom/summary.csv) · [Raw samples](results/headroom/samples.csv.gz)

## What changed

- **Key generation and signing on x86.** A profile on the older Xeon attributed approximately a quarter of SHA2-128s key generation and signing to scalar SHA-256. Batching WOTS chains across consecutive XMSS leaves fills otherwise idle lanes. The selected AVX-512 kernel fuses the PRF with the 15 chain steps, reuses common address rounds, and writes endpoints directly into buffers for parallel WOTS public-key hashes. FORS batches independent leaves and parents, including eight SHA-512 parents on the larger sets.
- **Verification on x86.** Chains from one WOTS signature have different public lengths. Sorting by remaining length, immediately refilling finished lanes, and restoring each endpoint to its original position reduced idle work. Across 996 verification layers, this schedule took 25,268 sixteen-lane steps, compared with 31,975 in input order. The sum of the per-layer lower bounds was 24,249 steps, so perfect assignment could save at most another 4.0% of those steps on this corpus. The bound for a layer is the larger of its longest chain and total steps divided by 16, rounded up. It covers scheduling only. [Layer totals by seed, set and length](results/headroom/occupancy.csv)
- **Long messages.** The original C5 long-message verification profile spent 92% of samples in software SHA-256. The new path schedules consecutive input blocks together and executes their dependent rounds in message order. Short inputs and tails use the individual-block backend. Signing and verification pass message and domain/context segments to the two hash constructions without allocating a contiguous copy of the message. Arm uses a bulk SHA backend for streams.
- **Arm tree hashing.** SHA-256 already spent most of its time in the four-chain hardware kernel on Graviton. The selected build retains that kernel and pairs independent SHA-512 parents where the processor supports the instructions. Graviton2 uses a software SHA-512 fallback.

## Experiments that set the stopping point

Four- and eight-stream SHA-NI lost to 16-way AVX-512 on AMD. On Arm, two-chain SHA-256 interleaving slowed representative workloads by 7–16%. Three chains and alternate public-length ordering failed to give a consistent improvement. Four independent Arm SHA-512 parents cost roughly 2–4% more than pairs on the tested instruction-capable machines. A software NEON pair on Graviton2 slowed signing on the larger sets by roughly 9–14%. On x86, shrinking XMSS tiles to two keys cost up to about 11% on fast sets on C5. Direct endpoint placement, four- and eight-key groups, specialized equal-length chains, alternative message schedules and whole-host code generation were measured against their immediate predecessors. Each trial's timings are exploratory. The complete release-to-release matrix above supplies the selected-build comparison. Exploratory long-message timings on x86 are omitted because an intermediate build encoded the wrong padding length. [Candidate timings](results/headroom/trials.csv.gz) · [Sampled Linux profiles](results/headroom/profiles.txt) · [Earlier SHA-NI comparison](wide-x86.md)

On the final older Xeon profile the fused WOTS kernel accounted for 93% of SHA2-128s key generation. Short verification split roughly evenly between WOTS recovery and scalar SHA-256. Reassociating scalar SHA-256 rounds and pre-scheduling partial groups of 8–15 blocks each changed median verification time by less than 1% on both SHA2-128 sets.

CPU-specific compilation also had workload-specific effects. On C8i, `-C target-cpu=native` sped up SHA2-192s short verification by 1.10×, with a gain in every round. On Graviton4, the distributable release was faster for larger-set signing. For SHA2-256s on a short message, the native build took 20% longer. Apple SHA2-128s short key generation varied from 0.92× to 1.04× compared with its predecessor, with a median of 0.98×. The Apple data supports little change on that operation.

The [paired hash replay](results/hash-replay/README.md) measures the effect of reusing SHA-256 prefix rounds on seven CPUs.

## Reading the SHA references

For each operation and input, the reference time is the counted number of SHA-256 blocks times the measured SHA-256 block time, plus the corresponding SHA-512 product. Thus 1.10× means 10% more elapsed time. A 32-byte SHA2-128s signature uses 2,218,488 equivalent SHA-256 blocks. Its fixed address prefix permits sharing some rounds, and its truncated outputs avoid full digest serialization. An implementation can beat a reference that compresses every independent block in full. [Block counts](sha-cost/counts.csv) · [Measured kernel rates](results/headroom/rates.csv)

- **Dedicated** uses the fastest measured dedicated-instruction or streaming implementation when the CPU exposes the SHA extension. The fastest measured complete software kernel supplies the rate when the extension is absent. C5 lacks SHA-NI, and none of the tested x86 hosts exposed SHA-512 instructions. Graviton2 lacks SHA-512 instructions.
- **Fastest** also admits independent software SIMD on machines with dedicated SHA instructions. It uses per-kernel six-round medians and includes the library's own general 16-lane SHA-256 and eight-lane SHA-512 compressors on x86. The SIMD raw kernels start with transposed message words and include message expansion, all rounds, and feed-forward. Distinct lane states and inputs are checked against a reference before timing. The independent C sweep and second Rust sweep have their own paired-ratio columns. Instruction-issue-only microbenchmarks do not enter these references.
- **Mixed** charges the necessarily sequential full message blocks at OpenSSL single-stream throughput, once for verification and twice for signing. For verification it also charges each WOTS public-key digest, XMSS authentication path and FORS root digest at single-stream rates. Remaining blocks use independent throughput. This is an estimate of the workload's dependency cost. Short-call overhead, partial vector batches, cache behavior and alternative schedules can change the attainable value.

| SHA2-128s verification | 32 B / fastest | 32 B / mixed | 1 MiB / fastest | 1 MiB / mixed |
|---|---:|---:|---:|---:|
| Older Xeon | 2.32× | 1.55× | 9.66× | 1.18× |
| AMD EPYC | 1.43× | 1.29× | 2.57× | 1.02× |
| Newer Xeon | 1.40× | 1.29× | 2.34× | 1.02× |
| Graviton2 | 1.38× | 1.34× | 1.70× | 1.18× |
| Graviton4 | 1.32× | 1.27× | 1.92× | 1.17× |
| Apple M5 Ultra | 1.14× | 1.12× | 1.27× | 1.01× |

Short-message verification has the largest remaining overhead on the older Xeon. On the tested 128s inputs it takes 55% longer than the mixed reference. The model gives independent work full lanes and omits setup and data movement. The observed scheduling bound, the measured alternatives and the validated timings support a stopping point for these single-core implementations. The remaining difference is measurable. Experiments on six processors cannot establish a universal optimum for other CPUs, message distributions, batch APIs or implementations.

## Correctness and scope

The hardware suites exercise NIST ACVP vectors and RustCrypto interoperability for all six sets, context handling, public API errors, compression and chain differentials, and the compatibility adapter including secret wiping. NIST vectors caught an experimental padding bug when pre-scheduled blocks were omitted from the encoded hash length. The selected implementation preserves the total prefix length and has differential tests around the block, padding and multi-batch boundaries. Further tests compare every recovered WOTS endpoint with scalar code and check overlapping in-place FORS parent batches. AddressSanitizer covers the Linux core unit and compression test targets. Two fixed/random timing runs per EC2 host exercise three secret-bearing chain shapes and a deliberately leaky control. These samples cannot establish constant time. The Lean refinement and constant-time proofs cover the default and `hw-sha2` configurations. The additional `platform-sha2` paths have empirical coverage. [Validation](results/headroom/validation.txt)

## Reproduction

The archived predecessor contains the crate source, locked dependencies, manifest and benchmark source for the previous best build. Extract it into an empty scratch directory to build the comparison executable. The final build uses the current checkout. Build each with `cargo bench --locked --features platform-sha2 --bench platforms --no-run`. Pass the resulting binary a round number and message size, for example `platforms-<hash> 1 1048576`. In a separate build set `RUSTFLAGS="-C target-cpu=native"` for the host-tuned comparison. Alternate the three executables on identical inputs, with rounds 0 through 6. [Predecessor source](results/headroom/before-rust.tar.gz) · [Benchmark implementation](../rust/benches/platforms.rs)

Run the following commands from the repository root.

```sh
# Recompute tables from the stored measurements.
python3 bench/sha-cost/summarize-headroom.py

# Run the public API, portable, host-tuned and upstream matrix on Linux.
taskset -c 0 python3 bench/platforms.py --rounds 6 --native > samples.csv

# Measure complete raw compressors and OpenSSL streaming SHA on this CPU.
python3 bench/sha-cost/generate.py > /tmp/slh-raw.c
cc -O3 -march=native /tmp/slh-raw.c -lcrypto -o /tmp/slh-raw
/tmp/slh-raw

cargo test --manifest-path rust/Cargo.toml --release --locked --features platform-sha2
cargo test --manifest-path compat/Cargo.toml --release --locked --features platform-sha2
```

On macOS omit `taskset` and supply the include and library directories for OpenSSL. To measure the general Rust AVX-512 kernels on a capable x86 host, run `python3 bench/sha-cost/rust-kernels.py /path/to/scratch/rust` on a disposable copy of the current crate with its sibling vectors directory. From that crate run `cargo test --locked --release --features platform-sha2 --lib raw_sha -- --ignored --nocapture --test-threads=1`. The archived samples include separate before/after raw-kernel ordering and an independent paired Rust run on each x86 processor.
