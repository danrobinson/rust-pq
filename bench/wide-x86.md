# Wide x86 SHA kernels

The subsequent optimization study measures all six parameter sets on six processors. [Latest measurements](headroom.md)

On the AMD EPYC 9R45, SHA2-128s signing fell from 65.33 ms to 30.20 ms. Its 2,218,488 SHA-256 compression blocks cost 32.66 ms at eight-stream SHA-NI throughput, or 23.73 ms at 16-lane AVX-512 throughput. On the older Xeon Platinum 8124M the same operation fell from 187.92 ms to 66.16 ms, against 46.65 ms of raw AVX-512 work. This Xeon lacks SHA-NI. The previous implementation and the selected implementation ran on the same EC2 instance for each comparison.

## Signing a 32-byte message

Speedup is old API time divided by new API time. The last two columns divide new API time by the counted SHA work at two measured rates. The dedicated comparison uses native SHA instructions where available and the fastest measured complete software kernel otherwise. The fastest comparison also admits software SIMD when dedicated instructions exist. A ratio of 1.27 means 27% extra time.

| Host | Set | Old ms | New ms | Speedup | Time / dedicated SHA | Time / fastest SHA |
|---|---|---:|---:|---:|---:|---:|
| C8A | 128s | 65.33 | 30.20 | 2.16× | 0.92× | 1.27× |
| C8A | 128f | 3.22 | 1.65 | 1.96× | 1.05× | 1.44× |
| C8A | 192s | 147.85 | 61.45 | 2.41× | 1.03× | 1.34× |
| C8A | 192f | 6.31 | 3.03 | 2.08× | 1.15× | 1.52× |
| C8A | 256s | 143.45 | 58.15 | 2.47× | 1.09× | 1.39× |
| C8A | 256f | 13.04 | 5.93 | 2.20× | 1.09× | 1.44× |
| C5 | 128s | 187.92 | 66.16 | 2.84× | 1.42× | 1.42× |
| C5 | 128f | 10.07 | 3.92 | 2.58× | 1.74× | 1.74× |
| C5 | 192s | 381.93 | 112.02 | 3.41× | 1.24× | 1.24× |
| C5 | 192f | 17.41 | 5.81 | 3.00× | 1.48× | 1.48× |
| C5 | 256s | 363.50 | 105.21 | 3.45× | 1.27× | 1.27× |
| C5 | 256f | 34.37 | 11.09 | 3.10× | 1.37× | 1.37× |
| C8I | 128s | 77.55 | 37.81 | 2.05× | 0.59× | 0.95× |
| C8I | 128f | 3.84 | 2.06 | 1.87× | 0.67× | 1.08× |
| C8I | 192s | 186.83 | 78.91 | 2.37× | 0.69× | 1.03× |
| C8I | 192f | 7.85 | 3.88 | 2.02× | 0.76× | 1.16× |
| C8I | 256s | 184.61 | 74.52 | 2.48× | 0.73× | 1.06× |
| C8I | 256f | 16.31 | 7.62 | 2.14× | 0.72× | 1.10× |

For 128s keygen, sign and verify respectively, the ratios to fastest raw SHA were 1.25×, 1.27× and 2.36× on C8a, and 1.40×, 1.42× and 3.12× on C5. Verification follows individual authentication paths and has fewer full batches. For a 1 MiB message the 128s verification ratios rise to 2.78× and 13.36× respectively. Hashing a single long message feeds each block into the next, while the raw reference fills all lanes with independent blocks. On the C5, a host-specific build reduced 128s signing further to 62.45 ms. On AMD that build took 30.49 ms. [All operations, including 1 MiB messages, native builds, portable builds and RustCrypto](results/wide-x86/summary.csv)

## Kernel selection

- On C8a, four-way and eight-way SHA-NI took 61.31 ms and 55.03 ms for 128s signing in the three-round candidate comparison allowing AVX-512 registers. Sixteen-way AVX-512 took 34.40 ms. Dispatching short final groups to the existing SHA-NI pair reduced that to 30.32 ms.
- The selected SHA-256 kernel carries 16 independent chains in transposed form between steps, precomputes the first four rounds for each batch's fixed prefix, and stores each lane's output when its public step range ends. The dispatch threshold is eight blocks. Short groups can use SHA-NI on hosts that expose it. The previous SHA-NI, AVX2 and portable fallbacks cover other processors.
- For SHA2-192 and SHA2-256, eight-way SHA-512 also hashes the independent pairs at each FORS tree level. In the C5 candidate comparison, this reduced 256s signing from 212.34 ms to 105.08 ms with the same SHA-256 kernel. The scalar parent handles the last one to seven pairs.
- The raw kernels execute full compression rounds on independent blocks. The vector reference starts with pre-transposed words. SLH-DSA can reuse prefix rounds across steps, which helps explain ratios below one. Partially occupied lanes, dependencies and work outside SHA limit how closely a public operation can match the reference.

## Measurement

C8a.large used an EPYC 9R45, C5.large a Xeon Platinum 8124M, and C8i.large a Xeon 6975P-C. Release builds used Rust 1.100.0. The final runs rotated the order of five binaries or modes, pinned each to vCPU 0, discarded round zero and paired six deterministic input rounds for each of the six parameter sets and both message lengths. Each verification sample averaged 32 calls. Raw kernels ran before the APIs in even rounds and after them in odd rounds. The winning raw kernel for each comparison was selected once by its six-round median. Each operation was then divided by its own round's weighted raw time for the resulting median ratio. These counts describe the algorithm's compression work on those inputs. [Block counts](sha-cost/counts.csv) · [Benchmark driver](platforms.py) · [Raw kernel generator](sha-cost/generate.py)

| Host | Dedicated comparison, SHA-256 ns/block | Fastest SHA-256 ns/block | Fastest SHA-512 ns/block |
|---|---:|---:|---:|
| C8a | SHA-NI ×8, 14.72 | AVX-512 ×16, 10.69 | AVX-512 ×8, 26.66 |
| C5 | AVX-512 ×16, 21.03 | AVX-512 ×16, 21.03 | AVX-512 ×8, 53.55 |
| C8i | SHA-NI ×2, 28.93 | AVX-512 ×16, 17.94 | AVX-512 ×8, 45.70 |

The sample file includes warmups and the intermediate experiments. In the final phase, `base` is the previous platform implementation, `both` is the selected runtime dispatch, `native` adds host-specific code generation, and `peer` invokes RustCrypto. In the earlier phases, `wide` enables 16-way chains, `hybrid` adds short-group SHA-NI dispatch, and `sha4/sha8` and `reg4/reg8` exercise wider SHA-NI with ordinary and extended register allocation respectively. API observations are ns/operation and raw observations are ns/compression block. [Per-round samples](results/wide-x86/samples.csv.gz) · [Recompute the summary](sha-cost/summarize-wide.py)

## Validation

On all three EC2 hosts, all 89 core tests and 51 adapter tests passed, including NIST ACVP, RustCrypto interoperability for every set, and the heap and stack wiping checks. The host-tuned build also passed the 89 core tests on each CPU and the 51 adapter tests on C5. AddressSanitizer passed all 12 kernel and unit tests on each host, including the in-place SHA-512 parent comparison. Emulated Nehalem and Haswell both passed the 11-test kernel suite. The portable and Arm Aeneas translations changed only in source-location comments. The wide x86 backend has differential and hardware test coverage and lies outside the Lean proofs. [Test counts and two-seed dudect output](results/wide-x86/validation.txt)
