# SHA-2 hash workload replay

The experiment compares a captured hash workload with and without reuse of the first four SHA-256 rounds in chain kernels. It covers the six FIPS 205 SHA-2 parameter sets, key generation, deterministic signing and successful verification, two message sizes and seven CPUs. Key generation takes no message and was timed in both sweeps. The six measured rounds use the peer benchmark’s seeds and messages and visit all six orders of the three timed implementations. Round zero warms up each workload. Linux samples run on CPU 0 of a dedicated benchmark VM. The Apple samples use the normal macOS scheduler.

## SHA2-128s signing of 32 bytes

Across the full matrix, 248 of 252 paired medians favored reuse. In 185 workloads every timed pair favored reuse.

| Processor | Full replay (ms) | Reuse replay (ms) | Production API (ms) | Median paired full / reuse |
|---|---:|---:|---:|---:|
| Apple M5 Ultra | 34.39 | 32.22 | 31.56 | 1.071× |
| Xeon 8275CL | 69.19 | 67.45 | 36.65 | 1.027× |
| Xeon 8124M | 64.69 | 63.19 | 34.48 | 1.027× |
| EPYC 9R45 | 33.75 | 32.66 | 21.84 | 1.031× |
| Xeon 6975P-C | 40.24 | 39.15 | 28.24 | 1.025× |
| Graviton2 | 71.79 | 69.29 | 64.85 | 1.037× |
| Graviton4 | 52.66 | 51.94 | 49.62 | 1.014× |

## Measured times

- **Full replay** executes the captured sequence with native hash kernels. Its Arm SHA and x86 AVX-512 chain kernels recompute the initial four rounds on each step. An opaque register input prevents the compiler from moving them out of the loop. Other kernel choices, truncation and message scheduling are shared with the reuse mode.
- **Reuse replay** executes the same sequence and active lanes using the library’s ordinary cached-prefix kernels. Every step consumes its predecessor’s computed digest, beginning with a cold prefix cache for each chain batch.
- **Library API** measures the public-algorithm implementation with production dispatch on the same host and input. The replays follow the portable operation schedule with native hash kernels. Production can fuse independent tree work across batches, particularly on x86, and skips the trace interpreter’s block reconstruction and intermediate stores. API/reuse is a comparison of two implementations, not an estimate of irreducible overhead.

The paired speedup is full time divided by reuse time within each round, then summarized by its median and range. A ratio above one favors reuse. The separate generic full-block estimate in the benchmark Page comes from the earlier compression study. Its inputs, memory layout and batching differ from the replay.

## Data flow and checks

The recorder executes the library’s portable SLH, FORS, XMSS, WOTS and hypertree scheduling code. It records calls to the hash functions, their addresses, chain ranges, and references to their inputs. A reference resolves to either a supplied key/signature chunk or a previous hash output. It rejects an unbound digest. Capture fixes the schedule and data-dependent indices for that input. Both timed replays recompute seed states, message hashes, chains and parent hashes. They rebuild chain inputs from the resulting bytes. All digest slots other than supplied inputs start at zero. Only the trace and initial inputs are prepared before timing.

After timing, each replay compares every emitted digest slot and message digest with the captured execution. During capture, the generated keys and entire deterministic signatures must match production and the verification must accept the production signature. A negative-control run advancing each chain’s first step by one failed the intermediate-digest comparison. The local independent RustCrypto test suite passed all 36 tests.

## Reproduction

From the repository root, run the following with Cargo on the path. The driver builds a benchmark-only full-round variant in a temporary directory. Production sources stay in their original tree.

```sh
python3 bench/sha-cost/replay/run.py > replay.csv
```

On Linux, prefix the command with `taskset -c 0`. To run one suite, pass the number of measured rounds and a parameter name, for example `6 SHA2_128S`. The benchmark uses the repository’s Rust lockfile and the recorded runs used rustc 1.100.0. See [paired medians](summary.csv), [raw timings including warm-up](samples.csv.gz), and [processor and compiler metadata](hosts/). Regenerate the checked summary with `python3 bench/sha-cost/replay/summarize.py`.
