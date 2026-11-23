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

A second SHA-NI experiment replaced the raw initial-state loads and mutable chunk iterator with indexed state words, explicit pairs and a one-block portable tail. This made the whole paired driver translatable with Aeneas. We compared the candidate against `df1fde9` with AVX-512 dispatch disabled in both builds. Across 36 workloads per host, the median paired speedup was 0.9990× on EPYC 9R45 (individual workload medians 0.9886–1.0070×) and 0.9997× on Xeon 6975P-C (0.9926–1.0084×). We excluded round zero and alternated candidate order over six timed rounds on the same vCPU. All four host/build combinations passed the 14 kernel and compression tests. [72 workload results](results/merged/sha-ni-driver-summary.csv) · [All 1,008 samples](results/merged/sha-ni-driver.csv.gz)


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

## SHA-512 FORS parent drivers

Three builds prepared the same parent blocks using an iterator, an indexed loop, or an explicit counter. We kept the indexed loop because it admits a direct proof of the in-place tree and path updates. Each machine ran one warmup and eight timed rounds in rotating build order. The speedup column is the median of 36 paired workload medians. The changes were small across all six machines. A fourth x86 candidate initialized only active XMSS message rows and showed no consistent public API advantage.

| CPU | Indexed loop speedup | SHA2-128s signing, 32 B | Sign / fresh raw SHA | Sign / previous fastest SHA |
|---|---:|---:|---:|---:|
| Xeon 8275CL (C5) | 1.0001× | 36.71 ms | 0.635× | 1.035×¹ |
| EPYC 9R45 | 0.9987× | 21.73 ms | 0.666× | 0.921× |
| Xeon 6975P-C | 1.0007× | 28.32 ms | 0.441× | 0.930× |
| Graviton2 | 1.0001× | 64.99 ms | 1.099× | 1.099× |
| Graviton4 | 1.0002× | 49.73 ms | 1.081× | 1.081× |
| Apple M5 Ultra | 0.9986× | 30.19 ms | 0.879× | 0.892× |

Fresh raw SHA uses this run’s fastest complete dedicated-instruction or bulk kernel for each hash width, falling back to the fastest measured C implementation on processors without that instruction. The previous fastest rate also admits the Rust transposed SIMD kernels on x86. Ratios use measured rounds 1–6, which have matching compression counts for the exact keys and messages. Latencies and paired speedups use all eight timed rounds. A ratio of 1.099× means 9.9% more time than the counted general-purpose SHA work. The library can share fixed message-prefix rounds. ¹ AWS assigned a Xeon 8275CL this time. The historical C5 reference used a Xeon 8124M, so only the fresh C5 comparison is on the same processor.

The CSV includes key generation, signing and verification for both message sizes and all six SHA-2 parameter sets. Regenerate it with `python3 bench/sha-cost/summarize-parents.py`. [216 workloads](results/merged/parent-driver-summary.csv) · [API samples](results/merged/parent-driver-samples.csv.gz) · [Fresh raw SHA samples](results/merged/parent-driver-raw.csv.gz) · [Candidate source and Linux runner](results/merged/parent-driver-experiment.tar.gz) · [Compression counts and baseline methodology](headroom.md)

The core and compatibility suites passed for each of the three parent-driver candidates on every EC2 host. Each build ran 188 tests on x86 or 190 on Arm across 14 test binaries and doctest groups. [Per-host test totals](results/merged/parent-driver-validation.csv)


## FORS leaf generation and same-host raw SHA on x86

The leaf experiment checked zero, full and partial batches at all three digest widths against the portable implementation, including untouched output slots. It compared the shipping chunk iterator, an indexed loop, and an indexed loop that shares the first two SHA-256 rounds between the PRF and leaf hash. The shared-prefix build took essentially the same public API time as the original. Its focused kernel medians were slightly slower on the two Xeons. Each build passed all 15 core kernel and compression tests on each host.

| CPU | Shared-prefix kernel speedup | Public API speedup | SHA2-128s signing, 32 B | Signing time / raw SHA time |
|---|---:|---:|---:|---:|
| Xeon 8275CL | 0.9960× | 0.9992× | 32.52 ms | 0.971× |
| EPYC 9R45 | 1.0000× | 1.0010× | 21.78 ms | 0.912× |
| Xeon 6975P-C | 0.9978× | 1.0005× | 28.38 ms | 0.931× |

Every raw SHA ratio uses the same host, pinned vCPU and release configuration as its public API sample. Each of six rounds measured independent, general-purpose 16-lane SHA-256 and eight-lane SHA-512 compression, including the schedule, rounds and feed-forward. The reference runs on already transposed words. It charges that round's exact compression count for the benchmark key, message and operation. The three EC2 instances terminated after the experiment. [108 same-host raw SHA ratios](results/merged/leaf-sha-summary.csv) · [Public API speedups](results/merged/leaves-summary.csv) · [API samples](results/merged/leaves.csv.gz) · [66 kernel shapes per CPU](results/merged/leaf-kernels.csv.gz) · [Raw compressor timings](results/merged/leaf-raw.csv.gz) · [Candidate sources and reproduction harness](results/merged/leaf-experiment.tar.gz)

## AVX-512 chain output stores

The adopted kernel keeps finished lane digests in registers and transposes them once to write the output blocks. For a group that finishes together it writes the final compression directly. The benchmark covers all three digest widths, twelve batch sizes from zero to 33, and four chain-length patterns. Each sample checks every byte against the portable implementation before timing. Each build also passed 15 kernel and compression tests per host.

| CPU | Chain kernel speedup | Mixed lengths | Uniform 15 steps | Median public API speedup | 32-byte SHA2-128s sign / raw SHA time |
|---|---:|---:|---:|---:|---:|
| Xeon 8275CL | 1.0774× | 1.1077× | 0.9965× | 0.9996× | 0.9726× |
| EPYC 9R45 | 1.1126× | 1.1439× | 1.0120× | 1.0012× | 0.9146× |
| Xeon 6975P-C | 1.0553× | 1.0695× | 0.9995× | 1.0009× | 0.9317× |

Kernel speedups are medians over 81 configurations with at least eight lanes and some active work. The other kernel columns restrict that set to mixed or uniform lengths. Public API medians cover 36 workloads per host. The raw SHA time is the sum of exact SHA-256 and SHA-512 block counts times the same-vCPU 16-way and 8-way general compressor times. Each round uses matching inputs and calibration. Round zero is excluded. API workloads also use specialized FORS and WOTS kernels, which limits how much these chain-driver improvements affect public operations. [Adopted kernel measurements](results/merged/chain-stores-fast-kernels.csv) · [API and raw SHA ratios](results/merged/chain-stores-fast.csv) · [Samples, sources and test results](results/merged/chain-stores-fast.tar.gz)

Two earlier runs compared scattering, immediate transposition and deferred transposition. Factoring the compression out of the loop reduced throughput for the common uniform-length case. The adopted version keeps compression inline and extracts the word-packing and finished-lane functions for Lean. [First comparison](results/merged/chain-stores-screen-kernels.csv) · [First run sources and samples](results/merged/chain-stores-screen.tar.gz) · [Independent comparison](results/merged/chain-stores-confirm-kernels.csv) · [Independent run sources and samples](results/merged/chain-stores-confirm.tar.gz)

The adopted Rust source passed 134 core and 54 compatibility tests per CPU with normal dispatch. EPYC and Xeon 6975P-C also passed all 188 tests with AVX-512 dispatch disabled for the SHA-256 driver, exercising the SHA-NI path. The older Xeon lacks SHA-NI. All three instances terminated. [Per-host counts](results/merged/chain-stores-validation.csv) · [Full logs, CPU identification and source hashes](results/merged/chain-stores-validation.tar.gz)

## Eight-lane AVX2 chain stores

On x86 machines that select the AVX2 fallback, the chain driver now checks each lane once before storing its digest words. Previously it repeated that check for each word. Each measurement used a pinned vCPU, release builds, rotating candidate order, and six paired rounds after warm-up. The public-operation columns show the median speedup over six SHA2 parameter sets and two message sizes.

| CPU, forced AVX2 | Key generation | Signing | Verification | 32-byte SHA2-128s signing | Signing time / raw AVX2 SHA time |
|---|---:|---:|---:|---:|---:|
| Older Xeon, c5.large | 1.028× | 1.023× | 1.024× | 162.56 ms | 1.285× |
| AMD EPYC, c8a.large | 1.013× | 1.011× | 1.004× | 81.08 ms | 1.091× |
| Newer Xeon, c8i.large | 1.014× | 1.015× | 1.020× | 94.75 ms | 1.045× |

These figures isolate the fallback by disabling SHA-NI and AVX-512 dispatch for both the baseline and candidates. The raw reference times eight independent full SHA-256 compressions on pretransposed inputs and checks each output against scalar SHA. Each signing ratio uses the exact compression count for its inputs. Only workloads that use SHA-256 exclusively have a raw ratio in the data. [Paired API measurements](results/merged/avx2-chain-stores.csv) · [144 chain shapes per host](results/merged/avx2-chain-stores-kernels.csv) · [Candidate sources, CPU details, tests and raw samples](results/merged/avx2-chain-stores.tar.gz)

The AVX2 revision passed all 134 core and 54 compatibility tests under both normal dispatch and forced AVX2 on all three hosts, for 1,128 passes. [Validation counts](results/merged/avx2-chain-validation.csv) · [Six configurations and source fingerprints](results/merged/avx2-chain-validation.tar.gz)

## WOTS endpoint and recovery stores on x86

Both AVX-512 routines now use the verified digest writer to serialize a batch before copying its live outputs. Endpoint generation copies consecutive chains into at most two keypair rows. Recovery selects the destination row of each finished chain. The measurements below compare this change against the previous masked scatter implementation on the same pinned vCPU, using six paired rounds after warm-up.

| CPU | Endpoint generation | Recovery | Public API median | SHA2-128s signing, 32 B | Signing time / raw SHA time |
|---|---:|---:|---:|---:|---:|
| Older Xeon, c5.large | 1.004× | 1.018× | 1.002× | 34.48 ms | 0.974× |
| AMD EPYC, c8a.large | 1.007× | 1.024× | 1.005× | 21.53 ms | 0.909× |
| Newer Xeon, c8i.large | 1.002× | 1.015× | 1.001× | 28.32 ms | 0.932× |

The endpoint median spans all three digest widths and eight nonempty batch sizes. Recovery spans ten digit distributions at each width. Individual shapes varied, including slowdowns. Every build compared whole output buffers with independent chain-by-chain results, including guard bytes, keypair boundaries and digits requiring zero steps. The API median covers 36 workloads per host. The raw denominator uses the exact input-specific compression counts and the same host's general 16-way SHA-256 and eight-way SHA-512 kernels. [Adopted kernel results](results/merged/wots-stores-bulk-kernels.csv) · [Public operations and raw ratios](results/merged/wots-stores-bulk.csv) · [Source, tests, and raw samples](results/merged/wots-stores-bulk.tar.gz)

Direct lane stores generally helped recovery but slowed endpoint generation on EPYC. Caching a fifth SHA round offered little additional end-to-end improvement across the three hosts. [Direct-store experiment](results/merged/wots-stores-confirm.tar.gz) · [Fifth-round experiment](results/merged/wots-stores-prefix.tar.gz)

The adopted version passed all 134 core tests and 54 compatibility tests with platform dispatch on each of the three x86 hosts, for 564 passes. [Validation counts](results/merged/wots-stores-validation.csv) · [Release logs, CPU details, source fingerprints and runner](results/merged/wots-stores-validation.tar.gz)

## BMI2 streaming SHA-256 and SHA-512

The const-generic round helper used for verification preserves the emitted scalar kernel on the x86-64 Linux release build. Against `df998a8`, the assembly bodies matched for both SHA-256 (2,800 lines) and SHA-512 (3,533 lines), including register allocation, instructions, and stack offsets. The comparison used `cargo rustc --locked --release --features platform-sha2 --target x86_64-unknown-linux-gnu --lib -- --emit=asm` and normalized local basic-block label numbers. This is a code-generation comparison for that build. [End-to-end kernel proofs](../lean-hw/Streamscalar/Top.lean)

## x86 streaming kernel verification build

The table compares the public SHA-2 APIs against `df998a8` across 36 workloads per host. Each workload ran six measured pairs on one pinned vCPU, alternating the build order after warm-up. The last two columns give elapsed signing time divided by the time to compress all counted SHA blocks for SHA2-128s signing on 32 bytes. A ratio of 0.90 means 10% less elapsed time. Signing can reuse common prefix rounds.

| CPU | Median paired speedup | Range of workload medians | Signing / native SHA | Signing / fastest C kernel |
|---|---:|---:|---:|---:|
| Xeon 8124M | 1.0000× | 0.9953–1.0042× | 0.646× | 0.646× |
| EPYC 9R45 | 0.9925× | 0.9839–1.0053× | 0.663× | 0.915× |
| Xeon 6975P-C | 0.9997× | 0.9927–1.0078× | 0.441× | 0.711× |

Native SHA uses the faster of the available SHA-instruction and library bulk controls, with the fastest measured C software kernel for an algorithm lacking dedicated instructions. The final column also considers the independent-block SIMD C controls. The earlier WOTS study measured separate Rust SIMD kernels. Its 0.974×, 0.909× and 0.932× results are also elapsed-time ratios. [108 workloads](results/merged/streaming-summary.csv) · [Ratios by workload](results/merged/streaming-sha-summary.csv) · [1,512 public API samples](results/merged/streaming.csv.gz) · [Raw controls](results/merged/streaming-raw.csv.gz)

The candidate gave the BMI2 verifier a separate round helper and replaced the AVX-512 row store with a native-endian bit reinterpretation. After the EC2 runs started, the gather's pointer calculation moved inside the word-loading closure to expose the source allocation to the proof. Relative to the baseline, both forms produced identical release assembly for each AVX-512 streaming function on the x86-64 Linux target with Rust 1.100.0 (1,954 lines for SHA-256 and 2,384 for SHA-512, normalizing local basic-block labels).
