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


## Paired Arm SHA-512

The two-lane SHA-512 refactor ran the same 36-workload SHA-2 comparison on Apple M5 Ultra. The median paired speedup was 1.0001× and the workload medians ranged from 0.9921× to 1.0062×. Sixteen kernel and differential tests passed with platform acceleration enabled. The proof follows the production routine from input bytes through both 40-step instruction sequences to the truncated outputs. It assumes the Arm SHA-512 instructions are available and uses the same instruction model as the verified single-block path. [Proof](../lean-hw/Paired/Proof.lean) · [Raw measurements](results/merged/arm-pair.csv.gz) · [36 workload results](results/merged/arm-pair-summary.csv)

## Paired x86 SHA-NI

Both builds disabled AVX-512 dispatch to measure public operations using the paired SHA-NI chain kernel. The median of the 36 workload speedups was 1.1973× on EPYC 9R45 and 1.0321× on Xeon 6975P-C. Individual workload medians ranged from 1.0112× to 1.2916× on EPYC and from 1.0001× to 1.0531× on Xeon. Both hosts passed 14 kernel and compression tests. Normal dispatch can select AVX-512 on both hosts. The baseline is commit `3870dab`. The Lean theorem takes any packed chaining state and two arbitrary 64-byte inputs, and verifies both serialized 32-byte results against FIPS 180-4 under the x86 intrinsic model. [Proof](../lean-hw/Slhdsa/Proofs/ShaNi.lean) · [Raw measurements](results/merged/sha-ni.csv.gz) · [72 workload results](results/merged/sha-ni-summary.csv)

## Batched SHA-512 WOTS public-key digests on x86

The selected version retains the masked AVX-512 gather for input and writes digest words through Rust slices. A second candidate replaced input gathers with per-lane loads as well. All three versions used ordinary runtime dispatch. Each EC2 host ran six measured rounds after warming up. Build order rotated each round. The focused benchmark measured 4,096 calls per sample, checked every active output against Python hashlib and checked untouched output rows. It covered batches of one through eight keys and both 24-byte and 32-byte outputs. All three builds passed the 14 kernel and compression tests on all three CPUs.

| CPU | Slice writes, focused kernel | Slice reads and writes, focused kernel | Slice writes, public operations |
|---|---:|---:|---:|
| Xeon 8124M | 1.0006× | 1.0020× | 0.9999× |
| EPYC 9R45 | 1.0015× | 0.9845× | 0.9993× |
| Xeon 6975P-C | 1.0012× | 1.0013× | 1.0004× |

Each cell is the median of the paired workload speedups, over 16 kernel shapes or 36 public API workloads. The input gather earned its keep on EPYC, where it was faster in all 16 kernel shapes. The slice writes make output updates visible to the Rust proof extractor. [Public API results](results/merged/group-stores-summary.csv) · [All public samples](results/merged/group-stores.csv.gz) · [Kernel samples, ordered by CPU, build, round, digest size, active lanes and nanoseconds](results/merged/group-kernels.csv.gz) · [Three kernel sources, test harness and run script](results/merged/group-experiment.tar.gz)

## AVX-512 SHA-256 output stores

The FORS leaf, FORS parent and WOTS public-key kernels now transpose four digest words at a time, then write consecutive bytes to each output. The experiment rotated three builds on the same pinned vCPU for one warm-up and six measured rounds. The table reports the median paired speedup across workloads. The last two columns use SHA2-128s signing with a 32-byte message and the previously measured mixed raw SHA reference on the same CPU model.

| CPU | Kernel speedup | Public API speedup | Signing time | Signing time / raw reference |
|---|---:|---:|---:|---:|
| Xeon 8124M | 1.0393× | 1.0002× | 34.51 ms | 0.973× |
| EPYC 9R45 | 1.0635× | 1.0025× | 21.65 ms | 0.920× |
| Xeon 6975P-C | 1.0283× | 0.9994× | 28.33 ms | 0.930× |

The transposed stores improved all 94 recorded kernel workloads on each CPU. Scalar per-word stores slowed full-width FORS batches on both Xeons. Each build passed 15 tests per CPU, including a differential against portable SHA-256 for truncated leaves, overlapping parent batches, partial batches, untouched outputs and ten-block WOTS digests. All 95 kernel shapes passed the differential. The libtest output prefix obscured the first timing line for 16-byte leaves with one active lane, so that shape is excluded from the timing summaries. The raw reference charges general SHA compression for each required block. The library reuses common round prefixes across lanes. [Public API results](results/merged/transpose-stores-summary.csv) · [Public samples](results/merged/transpose-stores.csv.gz) · [Kernel samples](results/merged/transpose-kernels.csv.gz) · [Kernels and reproduction harness](results/merged/transpose-experiment.tar.gz) · [Raw reference methodology](headroom.md)
