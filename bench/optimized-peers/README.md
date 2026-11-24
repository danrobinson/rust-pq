# Optimized SLH-DSA implementation benchmarks

[Measurements and comparisons](../results/optimized-competitors/README.md)

Build inside a disposable copy of formal-sig. The Rust build script installs temporary benchmark programs in both Rust source trees. The comparison uses these revisions.

| Implementation | Revision |
|---|---|
| formal-sig | `6a364bdc31d72bddb20a744cf034c63230204115` |
| Botan | [28a5af9](https://github.com/randombit/botan/tree/28a5af9a3e829480b0fead5e4de51abd00eb11d4) |
| Conduition slh-experiments | [94bc2f5](https://github.com/conduition/slh-experiments/tree/94bc2f5a0ff611b83df32e77a6f14f1d9c81d8be) |
| Fluhrer parallel-sphincsplus | [e1f3b64, AVX-512 branch](https://github.com/sphincs/parallel-sphincsplus/tree/e1f3b647773c7faf15947a12e8f0b21123a9a76e) |

Place checkouts named `botan`, `slh-experiments`, and (x86 only) `parallel-sphincsplus` in the disposable root. Use a Rust toolchain compatible with the pinned dependencies. See the per-host metadata for the measured compiler versions.

```sh
# Amazon Linux 2023. On Apple, use CXX=clang++ and --cc=clang instead.
export CXX=gcc14-g++
(cd botan && bash ../bench/optimized-peers/build-botan.sh --cc=gcc --cc-bin="$CXX")
# x86-64 only
(cd parallel-sphincsplus && make -j2 CPP="$CXX" slh-dsa-fast.a)
bash bench/optimized-peers/build-drivers.sh
bash bench/optimized-peers/link-native.sh
python3 bench/optimized-peers/sweep.py
bash bench/optimized-peers/cached.sh
```

The main sweep writes `samples.csv`. It runs seeded key generation, public key extraction, deterministic and hedged signing, and verification of a valid deterministic signature. All use the same pure FIPS 205 inputs, including empty context and a 32-byte or 1 MiB message. Seed bytes, message, and additional signing randomness vary by round. Verification is averaged over 32 calls and public-key extraction over 256 calls. Each key generation and signing invocation is timed individually. Key generation and extraction are repeated under both message lengths for consistency, though they do not consume the message. Public-key extraction includes differing API allocation/copy costs. DER/key import operations were outside this comparison.

At each size all providers' complete private keys, public keys, deterministic signatures and hedged signatures must be byte-identical to formal-sig's on every common set. Each driver also tests rejection under a changed message or context. The sweep checks the row and vector-file sets before recording timings. The ordinary Conduition build uses its default SIMD and hash-midstate caching, with the root-tree cache disabled. Apple OpenCL selects a GPU device explicitly. API/device initialization is outside the measured GPU operations. SHAKE and larger parameter sets have no measured OpenCL path. Fluhrer runs with a one-thread and a two-thread limit. The Linux single-thread measurements use CPU 0 and two-thread measurements allow CPUs 0 and 1. Those two vCPUs share a core on the Intel instances. Apple uses normal scheduling.

The cached sweep writes `cached.csv`. It remeasures formal-sig alongside Conduition with `multithread` and root-tree caching on its four supported sets. Cache construction is included in key generation and the same generated key is reused for both signatures. Linux permits both vCPUs for this peer. Apple permits normal thread scheduling. The latter sweep uses four measured rounds with alternating provider order. The main sweep rotates provider order for three, four or five measured rounds depending on the host. Both sweeps discard round zero when summarizing. Times use elapsed monotonic clocks within each provider process.

Use the following command in the repository to regenerate the workload and operation summaries from the raw per-host samples. Ratios are peer time divided by formal-sig time, paired within a round. The per-workload estimate is the median paired ratio and the operation aggregates are equal-weight geometric means across supported sets and both message sizes.

```sh
python3 bench/optimized-peers/summarize.py bench/results/optimized-competitors
```
