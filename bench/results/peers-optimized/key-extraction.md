# The five public-key extraction misses

The six-round matrix recorded five RustCrypto wins for extraction, all on a 32-byte public key. Three CPU/set pairs account for the five rows because the operation takes no message. The separate 100,000-call benchmark favored the library in all 20 measured pairs for each of those three cases. The primary matrix continues to report all five misses. [Primary samples](samples.csv.gz) · [Focused samples](raw-key-samples.csv.gz)

| CPU and set | Message sizes with a primary miss | Primary median paired difference, ns | Focused library, ns | Focused RustCrypto, ns | Focused median paired difference, ns |
|---|---|---:|---:|---:|---:|
| Xeon Platinum 8275CL, SHA2-128f | 32 B / 1 MiB | −0.340 / −0.375 | 0.979 | 1.881 | +0.900 [0.863, 0.903] |
| Xeon Platinum 8275CL, SHA2-128s | 1 MiB | −0.092 | 0.978 | 1.881 | +0.903 [0.793, 0.913] |
| Graviton4, SHA2-128s | 32 B / 1 MiB | −0.098 / −0.202 | 1.072 | 2.305 | +1.233 [1.228, 1.236] |

The paired difference subtracts the library time from RustCrypto’s time within each round. Brackets give the sixth and fifteenth ordered differences out of twenty. Under independent draws from a common continuous distribution, this interval has 95.86% coverage for the population median. The samples share a machine and process, so the interval describes repeatability within this run. Every one of the ten library-first and ten peer-first samples favored the library for each CPU/set. Primary SHA2-128f on the 8275CL favored RustCrypto in all six pairs at both message sizes. The two drivers therefore show a repeatable difference under their respective conditions. [Primary driver](../../peers/public.rs) · [Focused driver](../../peers/raw-keys.rs)

## Machine code

Extraction copies bytes 32 through 63 of a 64-byte private key into a 32-byte result. Cross-compiling the complete primary Rust driver with the recorded rustc 1.100.0 and LLVM 23.1.5 for each Linux target gave the following loop bodies for both SHA2-128s and SHA2-128f. The source driver runs as a library with an exported entry point so its assembly can be generated on another host. The timed code, inputs, Cargo release options and default CPU target are preserved. [Fixed-size API](../../../rust/src/sets.rs) · [Copy implementation](../../../rust/src/api.rs)

| Target | Library work per extraction | RustCrypto work per extraction |
|---|---|---|
| Generic x86-64 Linux (8275CL run) | Two 16-byte loads from offsets 32 and 48, two 16-byte stores | Two 16-byte source loads, two temporary stores, two temporary reloads, two result stores |
| AArch64 Linux (Graviton4 run) | One paired vector load and one paired vector store, 32 bytes each | One paired vector load, a 16-byte temporary store and reload, one paired result store |

The library’s loops contain only these copy instructions, the shared `black_box` pointer spill/reload and loop control. The fixed-size entry inlines, eliminating allocation, zeroing, checks, calls and hashing. The x86 default binary supports SSE2. Compiling its consumer for AVX with `-Ctarget-cpu=skylake-avx512` allows LLVM to collapse the two source loads and stores into one 32-byte load and one 32-byte store in the timed loop. Target-specific compilation already provides this option without a runtime CPU check for each 32-byte copy. There is no matched native timing for that optional AVX build.

The full driver enters each 256-call extraction measurement immediately after key generation, and uses a stack frame shared with the large signature workloads. The dedicated driver times 100,000 copies per sample and alternates the providers. Timer overhead, processor state after key generation, and code and stack placement can influence these subnanosecond differences. The archived samples do not identify their individual contributions. The focused samples and compiler output provide no evidence for a remaining library-side copy inefficiency on either CPU.

Run `python3 bench/peers/key-extraction.py` to reproduce the focused table. Add `--assembly x86_64-unknown-linux-gnu` or `--assembly aarch64-unknown-linux-gnu` to print both providers’ loops from the full driver, with the corresponding Rust standard-library target installed. Add `--cpu skylake-avx512` for the x86 AVX comparison. [Reproduction script](../../peers/key-extraction.py)
