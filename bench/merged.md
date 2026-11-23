# Merged SHAKE benchmark

The table gives the speedup from specializing the Keccak-f[1600] rho, pi and chi steps. Each entry is the median of twelve paired speedups covering all six SHAKE parameter sets at 32 bytes and 1 MiB. Key generation has no message input and was measured twice. The baseline uses the SHAKE permutation from commit `ccbda7b` with the same merged caller and release configuration. Lean proves the specialized permutation against the FIPS 202 specification for arbitrary states. [Permutation proof](../lean/Slhdsa/Proofs/Keccak.lean)

| CPU | Key generation | Sign | Verify |
|---|---:|---:|---:|
| Xeon 8124M | 5.78× | 5.76× | 5.55× |
| EPYC 9R45 | 6.52× | 6.48× | 6.48× |
| Xeon 6975P-C | 5.64× | 5.62× | 5.47× |
| Graviton2 | 5.94× | 5.91× | 5.91× |
| Graviton4 | 5.11× | 5.07× | 4.77× |
| Apple M5 Ultra | 5.04× | 5.03× | 4.64× |

Each CPU ran a warm-up pair and six timed pairs of the public APIs, alternating executable order. Linux runs pinned the benchmark process to one vCPU. The local Apple measurements used ordinary OS scheduling. The per-workload file includes median latencies in nanoseconds and the range of observed paired speedups. The SHA-2 study reports overhead against separately measured native SHA-256 and SHA-512 compression. SHAKE uses a different permutation. [Raw SHAKE samples](results/merged/shake.csv.gz) · [216 workload results](results/merged/shake-summary.csv) · [SHA-2 raw-throughput comparison](headroom.md)

## SHA-2 compression refactor

The AVX-512 kernels now expose a round-and-schedule step to the proof extractor while preserving their unrolled calls. The median paired speedups across the 36 SHA-2 workloads were 0.9994× on the older Xeon, 0.9999× on EPYC and 0.9986× on the newer Xeon. Individual workload medians ranged from 0.9812× to 1.0278×. The same three platforms passed the compression differential suite after the refactor. The merged platform builds also passed the full core and adapter suites on all five EC2 CPUs. [Raw measurements](results/merged/wide-refactor.csv.gz) · [108 workload results](results/merged/wide-refactor-summary.csv) · [Test counts](results/merged/validation.csv)

Run `python3 bench/summarize-merged.py` from the checkout to regenerate the summary tables from the raw samples.


## Eight-lane AVX2 fallback

The older Xeon also ran both AVX2 implementations with AVX-512 chain and tree dispatch disabled in both benchmark executables. It has no SHA-NI. Across the same 36 SHA-2 workloads, the median paired speedup was 1.0000×, with individual medians from 0.9864× to 1.0125×. The candidate passed 14 kernel and compression tests in that configuration. Its Lean theorem includes loading the eight 64-byte blocks, transposing their words, computing the full schedule and 64 rounds, and adding back the initial state in every lane. [Raw measurements](results/merged/avx2.csv.gz) · [36 workload results](results/merged/avx2-summary.csv)
