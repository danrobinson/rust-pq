# Retest of the 122 previous SLH-DSA losses

With the opt-in `parallel` feature, rust-pq achieved a geometric mean speedup of **1.31×** over the peer on the 122 workloads selected for retesting. These comprised 41 deterministic signing, 40 hedged signing, 24 key generation and 17 verification comparisons. Each comparison fixes the CPU, peer configuration, parameter set, message size and operation. The smallest median lead was 1.056×. The two Graviton platforms had no previous losses and were outside this retest. [Original seven-platform results](../optimized-competitors/README.md) · [All 122 before, after and peer measurements](prior-losses.csv)

| CPU | Geometric mean speedup over peer | Peer |
|---|---:|---|
| Apple M5 Ultra | 2.67× | Conduition OpenCL |
| Xeon 8275CL | 1.36× | Fluhrer |
| Xeon 8124M | 1.36× | Fluhrer |
| Xeon 6975P-C | 1.22× | Fluhrer |
| EPYC 9R45 | 1.35× | Fluhrer |

## Where the time went

The signer used to compute each XMSS authentication path when it reached that layer. The message digest already fixes every path's address. Workers now compute the independent subtrees while the caller signs the FORS portion, and the caller assembles the WOTS signatures in their original order. On the M5 Ultra, SHA2-128s deterministic signing of 32 bytes went from 32.85 ms to 4.44 ms using up to eight CPU threads. Conduition took 11.06 ms on the GPU. On the EPYC, SHAKE-192s signing went from 146.58 ms on one core to 58.22 ms on two, against Fluhrer's 77.59 ms on the same two cores.

On AVX-512 x86, the old SHAKE code batched chains within one WOTS public key. Each key has 35, 51 or 67 chains, leaving the last eight-lane batch partly empty. The new subtree code hashes eight leaves together, keeping the lanes occupied through endpoint compression. Short single-state SHAKE hashes also use the existing AVX-512 permutation. A separate one-thread experiment isolated the effects for SHAKE-192s on the Xeon 6975P-C. Times are medians over three measured rounds with 32-byte messages. [Raw experiment](c8i-ablation.csv)

| Single-thread operation | Before | Eight-leaf batching only | Both changes |
|---|---:|---:|---:|
| Key generation | 23.96 ms | 18.00 ms | 16.91 ms |
| Deterministic signing | 221.47 ms | 181.09 ms | 179.86 ms |
| Verification | 258.0 µs | 257.8 µs | 200.7 µs |

Verification never builds a secret-key subtree. Its improvement comes from the single-state permutation. In the main peer retest the same one-thread verification took 198.9 µs against Fluhrer's 222.8 µs.

## Measurement and reproduction

The baseline was revision `6a364bdc31d72bddb20a744cf034c63230204115` with `platform-sha2`. The candidate enabled `parallel`. Both used the same public API driver, native CPU compilation and 32-byte and 1 MiB messages. Each host ran a warmup, then rotated provider order across three measured rounds on Apple and five on Linux. Times in the CSVs are nanoseconds. The summary takes the median of within-round ratios. Each round checked private keys, public keys and both signature modes byte for byte across providers on their common sets. Drivers also checked rejection of altered inputs.

Linux pinned the baseline and the one-thread configurations to CPU 0. Comparisons with two-thread Fluhrer allowed CPUs 0 and 1 for both contenders. These were sibling hardware threads on Intel and separate cores on AMD. Apple used normal scheduling. The GPU comparison excludes OpenCL initialization and kernel compilation. These are individual-operation latency measurements.

1. In disposable checkouts, use the [peer build instructions](../../optimized-peers/README.md) and their pinned revisions to build the baseline and competitors. Place the baseline executable in a benchmark directory as `old`, alongside `fluhrer` on Linux or `opencl` on Apple.
2. In the candidate checkout, copy `bench/peers/public.rs` to `rust/benches/platforms.rs`. Run `RUSTFLAGS='-C target-cpu=native' cargo bench --locked --manifest-path rust/Cargo.toml --features parallel --bench platforms --no-run`. Copy the reported benchmark executable to the benchmark directory as `new`.
3. From that directory run the [timing driver](../../optimized-peers/tuning.py). It writes `tuning.csv`. The recorded runs are [Apple](apple.csv), [Xeon 8275CL](c5c.csv), [Xeon 8124M](c5n.csv), [Xeon 6975P-C](c8i.csv) and [EPYC](c8a.csv).
4. From the repository root run `python3 bench/optimized-peers/tuning_summary.py bench/results/parallel` to regenerate the loss-by-loss comparison.

The optimized configuration passed the Rust release tests on Apple and Xeon, and the compatibility suite on Apple. Lean checks the parallel signing algorithm, eight-leaf construction and both branches of the x86 single-state permutation. The source-bound symbolic checks and their assumptions are documented alongside the proofs. [Proof scope and replay](../../../lean-hw/Parallel/README.md)
