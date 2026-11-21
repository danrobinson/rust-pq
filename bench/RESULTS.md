# SLH-DSA-SHA2-128s performance: the verified crate against other implementations

This file reports five benchmark runs of the same suite:

- **Run 5 (current; `results/run5/`, 2026-11-21 13:31–13:52)** repeats run 4 after the `hw-sha2` backend
  was rewritten so that Aeneas translates it (see `../HANDOFF.md`). The numbers did not move.
- **Run 4 (`results/run4/`, 2026-11-21 10:37–10:58)** measures the crate after the performance
  work of 2026-11-21: with `hw-sha2` it is faster than RustCrypto and OpenSSL. The earlier runs below
  describe the crate as it was when they were made.
- **Run 3 (`results/run3/`, 2026-11-21 06:45–07:07)** adds the verified crate built with its opt-in `hw-sha2`
  feature (ARMv8 SHA-256 instructions in the compression function; that module is not covered by the proofs).
- **Run 2 (`results/run2/`, 2026-11-21 00:18–01:16)** measures the *optimised* verified crate now in
  `../rust`, which has the seed midstate and no heap on the hot paths and has been re-proved in Lean (see
  `../opt/README.md`). The pre-optimisation crate is measured next to it as `verified-before`.
- **Run 1 (pre-optimisation; `results/run1/`, 2026-11-20 23:11–00:13)** is kept unchanged further down. In run 1,
  `verified` *means the crate now frozen at `../opt/original/rust`*, which run 2 calls `verified-before`.

Reproduce with `./run.sh` (all five build configurations, two rounds, about 40 minutes). To add rounds to an
existing results directory, use `STAMP=<dir> ROUND_START=3 [CONFIGS="default soft"] ./run.sh`.

# Run 5: the verified `hw-sha2` backend

Between run 4 and run 5 the hardware module of `../rust/src/sha256.rs` was rewritten as safe Rust over
eighteen one-line intrinsic wrappers, so that Aeneas translates it and the build with `hw-sha2` is proved
too (`../lean-hw`). `compress` and `chain_blocks` now hand off to `compress_portable` and
`chain_blocks_portable`. Same method as run 4: configurations `default` and `hw`, two rounds, load average
1.4–2.6 on 36 cores, nothing else running.

| | keygen | sign 32 B | sign 1 MiB | verify 32 B | verify 1 MiB |
|---|---|---|---|---|---|
| `verified` (portable, config `default`) | 39.86 ms | 303.6 ms | 309.1 ms | 316.2 µs | 2.67 ms |
| **`verified+hw-sha2`** (config `hw`) | **3.91 ms** | **30.21 ms** | **30.86 ms** | **35.36 µs** | **351.8 µs** |
| rustcrypto-slh-dsa (config `hw`) | 8.28 ms | 62.55 ms | 63.13 ms | 63.75 µs | 363.8 µs |
| openssl 4.1 (config `hw`) | 7.30 ms | 55.76 ms | 56.38 ms | 58.60 µs | 404.6 µs |
| slhdsa-c, portable C (config `hw`) | 28.63 ms | 218.3 ms | 221.7 ms | 224.9 µs | 1.86 ms |
| RustCrypto time / `verified+hw-sha2` time | 2.12 | 2.07 | 2.05 | 1.80 | 1.03 |
| OpenSSL time / `verified+hw-sha2` time | 1.87 | 1.85 | 1.83 | 1.66 | 1.15 |

- `verified+hw-sha2` is within 2.3% of run 4 in every column (3.91 ms / 30.21 ms / 35.36 µs against
  4.00 ms / 30.22 ms / 35.40 µs), and the portable build within 2.4%. Per-round spread of
  `verified+hw-sha2` is ±0.0% in every column.
- The compression count is unchanged (292,352 / 2,218,488 / 2,274), and interoperability is clean in both
  builds (`results/run5/interop.md`, `interop-hw.md`).

Full tables: `results/run5/summary.md`.

# Run 4: after the performance work

`../rust` was restructured around one primitive, `hash::chain_blocks` (iterated single-block hashing in
place, on many independent blocks), and its `hw-sha2` backend now works on four chains at once
(`../HANDOFF.md` has the design and what is and is not verified). Configurations `default` and `hw`, two
rounds each (`CONFIGS="default hw"`), load average 1.5–3.7 on 36 cores: Lean builds were running on the
machine during the run, most heavily in the first `default` round. Nothing else changed from run 3.

| | keygen | sign 32 B | sign 1 MiB | verify 32 B | verify 1 MiB |
|---|---|---|---|---|---|
| `verified` (portable, config `default`) | 40.40 ms | 305.2 ms | 311.3 ms | 323.9 µs | 2.69 ms |
| **`verified+hw-sha2`** (config `hw`) | **4.00 ms** | **30.22 ms** | **30.85 ms** | **35.40 µs** | **352.3 µs** |
| rustcrypto-slh-dsa (config `hw`) | 8.30 ms | 62.58 ms | 63.19 ms | 63.78 µs | 364.9 µs |
| openssl 4.1 (config `hw`) | 7.32 ms | 56.00 ms | 56.95 ms | 58.86 µs | 405.5 µs |
| slhdsa-c, portable C (config `hw`) | 29.27 ms | 220.1 ms | 223.1 ms | 225.8 µs | 1.87 ms |
| RustCrypto time / `verified+hw-sha2` time | 2.08 | 2.07 | 2.05 | 1.80 | 1.04 |
| OpenSSL time / `verified+hw-sha2` time | 1.83 | 1.85 | 1.85 | 1.66 | 1.15 |

- With `hw-sha2` the crate is faster than RustCrypto and OpenSSL in every operation measured. The margin
  is about 2× on key generation and signing, 1.7–1.8× on verification, and small on verifying a 1 MiB
  message, where all three spend their time hashing the message one block after another.
- Against run 3, `verified+hw-sha2` went from 11.54 ms / 83.65 ms / 85.34 µs to 4.00 ms / 30.22 ms /
  35.40 µs: 2.9×, 2.8× and 2.4×.
- The portable build went from 43.0 ms / 324.5 ms / 335.8 µs to 40.40 ms / 305.2 ms / 323.9 µs (5–6%). It
  is still 4.9× slower than RustCrypto, 1.4× slower than slhdsa-c and 1.5× faster than `fips205`.
- Per-round spread of `verified+hw-sha2` is ±0.0–0.3%; of the others in config `hw`, up to ±1.8%.
- The compression count is unchanged at 292,352 / 2,218,488 / 2,274 (`results/run4/compressions.md`): the
  same hashes in a different order. 2,218,488 compressions in 30.22 ms is 13.6 ns each; the SHA-256 round
  instructions of this CPU allow about 12.7 ns for a chain step (see `../HANDOFF.md`).
- Interoperability is clean in both builds on all five checks against `verified-before`,
  rustcrypto-slh-dsa, fips205, OpenSSL and slhdsa-c (`results/run4/interop.md`, `interop-hw.md`).
- `hw-sha2` is not covered by the proofs: the default build is what is verified, and the feature replaces
  two of its functions with tested, unproved code.

Full tables: `results/run4/summary.md`.

# Run 3: the opt-in `hw-sha2` backend

`../rust` now has a Cargo feature `hw-sha2`, off by default. Run 3 measures the crate with it on, as
`verified+hw-sha2`, in a new build configuration `hw` (`cargo bench --features hw`; default release profile).
It is a separate configuration because Cargo unifies features: one build cannot contain `../rust` both with and
without the feature. The hardware-SHA-2 libraries and portable C were run in the same configuration, back to
back with it; the `default` configuration was run again in the same session for the portable build.
Two rounds each (`CONFIGS="default hw"`), load average 1.3–2.3 on 36 cores. Nothing else changed from run 2.

| | keygen | sign 32 B | verify 32 B | sign, against `verified+hw-sha2` |
|---|---|---|---|---|
| `verified` (portable, config `default`) | 43.0 ms | 324.5 ms | 335.8 µs | 3.88× slower |
| **`verified+hw-sha2`** (config `hw`) | 11.54 ms | 83.65 ms | 85.34 µs | – |
| rustcrypto-slh-dsa (config `hw`) | 8.28 ms | 62.49 ms | 63.83 µs | 1.34× faster |
| openssl (config `hw`) | 7.32 ms | 55.80 ms | 58.54 µs | 1.50× faster |
| slhdsa-c, portable C (config `hw`) | 28.75 ms | 219.0 ms | 225.8 µs | 2.62× slower |

- The feature makes the crate 3.73× (keygen), 3.88× (sign) and 3.93× (verify) faster than its portable build.
- RustCrypto is still 1.34–1.39× faster and OpenSSL 1.46–1.58×. All three now spend their time in the same
  hardware compression function, so what is left is per-call overhead around it.
- `verified+hw-sha2` is within 2% of the unverified prototype `variant-D` from run 2 (82.2 ms sign in this run's
  `default` configuration), as expected: the feature is that prototype moved into the real crate, with runtime
  CPU detection added.
- Per-round spread of `verified+hw-sha2` is ±0.1–1.7%.
- Interoperability with the feature on is clean on all five checks against `verified-before`, rustcrypto-slh-dsa,
  fips205, OpenSSL and slhdsa-c (`results/run3/interop-hw.md`), and `cargo test --release --features hw-sha2`
  passes in `../rust` (ACVP vectors and `tests/compress.rs`).
- Compression counts are unchanged (2,218,488 per signature): the feature changes how a block is compressed,
  not how many.

Full tables: `results/run3/summary.md`.

# Run 2: after the optimisation

Hardware, OS, toolchain, library versions and method are the same as in run 1 (see "Setup" below). These things
changed:

- `verified` is the current `../rust` (path dependency).
- `verified-before` is `variants/base`. Cargo cannot link two path packages both named `slhdsa`, so this is a
  copy of `../opt/original/rust/src`. Its only addition is a compression counter compiled in only with feature
  `count`, which the benchmarks never enable. `run.sh` checks before every run that the copy still matches its
  source and stops if it does not (`results/run2/copies.txt`).
- `variants/current` is the same kind of counted copy of `../rust/src`, used only for compression counts.
- New `variant-D` (`variants/d`, **not verified**) is the current `../rust/src` with the ARMv8 SHA-2 `compress`
  from variant C, and nothing else changed. It measures what hardware SHA-2 would add on top of the verified
  structure.
- `src/bin/profile.rs` now passes `&hash::seed_ctx(&pk_seed)` to the internal functions and times
  `hash::thash_short`.
- Rounds: `default` and `soft` ran 4 rounds (rounds 1–2 00:18–00:52, rounds 3–4 00:53–01:16). `tuned` and
  `asm` ran 2 rounds. `variant-D` was added for rounds 3–4 only, so its cells have n = 2.
- Load: the machine was much quieter. The 1-minute load average was 1.5–3.1 on 36 cores, against 1.9–12 in run 1.

## Interoperability against the new crate (`results/run2/interop.md`)

Every FIPS 205 implementation agrees with the new `verified` crate on all five checks, for 32 B and 1 KiB
messages:

- the same SK/PK from the same seeds;
- each one verifies the verified crate's signature;
- the verified crate verifies each one's signature;
- byte-identical deterministic signatures;
- a 1-bit-flipped signature is rejected.

The implementations checked are `verified-before`, rustcrypto-slh-dsa, fips205, OpenSSL, slhdsa-c and variants
A–D. PQClean round 3 again gives the same keys, but its signatures do not cross-verify (expected). Every copy
under `variants/` (base, current, A, B, C, D) passes the NIST ACVP vectors (`results/run2/variants-acvp.txt`).
The real `../rust` crate was not tested with `cargo test` here, to avoid writing to `rust/target`. Its outputs
are checked only through interop, byte-identical to `verified-before`, which passes ACVP.

## Before / after (config `default`, median of 4 rounds)

| | keygen | sign 32 B | verify 32 B | verify 1 MiB | SHA-256 compressions per keygen / sign / verify |
|---|---|---|---|---|---|
| verified-before (`opt/original/rust`) | 102.5 ms | 785.0 ms | 805 µs | 3.17 ms | 580,094 / 4,404,707 / 4,476 |
| **verified (current `rust/`)** | **42.9 ms** | **325.2 ms** | **338 µs** | **2.79 ms** | 292,352 / 2,218,488 / 2,274 |
| speed-up | **2.39×** | **2.41×** | **2.39×** | 1.14× | 0.504× the compressions |

The new crate is about 1.15× faster than my safe-Rust variant B (369 ms). B has the same compression count but
fills a streaming buffer byte by byte, whereas the verified crate builds the single padded block for F/H/PRF
directly (`thash_short`). Verifying a 1 MiB message improves only 1.14×, because it is dominated by hashing the
message, which the optimisation does not change.

**Where the time goes now** (`src/bin/profile.rs`; `sample` over 6 s of signing, `results/run2/sample-sign.txt`):
- 98.9% of samples are in `sha256::compress`, and none in `malloc`/`free`, against 21% before.
- By timing: `thash_short` F takes 142 ns, the same as one compression (144 ns). 2,218,488 compressions ×
  143.7 ns = 319 ms of the 326 ms sign.
- Signing is therefore bounded by the portable compression function.

## Main table, run 2 (median; **bold** = speed-up over the NEW verified crate in the same build)

| implementation | keygen | sign 32 B | verify 32 B | verify 1 MiB |
|---|---|---|---|---|
| **verified (current)** | 42.9 ms | 325 ms | 338 µs | 2.79 ms |
| verified-before | 102.5 ms (**0.42×**) | 785 ms (**0.41×**) | 805 µs (**0.42×**) | 3.17 ms (**0.88×**) |
| rustcrypto-slh-dsa | 8.29 ms (**5.2×**) | 62.6 ms (**5.2×**) | 63.7 µs (**5.3×**) | 364 µs (**7.7×**) |
| openssl 4.1 | 7.39 ms (**5.8×**) | 56.4 ms (**5.8×**) | 58.7 µs (**5.8×**) | 405 µs (**6.9×**) |
| fips205 (portable SHA as shipped) | 61.2 ms (**0.70×**) | 472 ms (**0.69×**) | 483 µs (**0.70×**) | 2.16 ms (**1.3×**) |
| slhdsa-c (portable C) | 28.6 ms (**1.5×**) | 219 ms (**1.5×**) | 226 µs (**1.5×**) | 1.86 ms (**1.5×**) |
| pqclean-r3 (portable C, SPHINCS+ r3) | 35.2 ms (**1.2×**) | 267 ms (**1.2×**) | 263 µs (**1.3×**) | 1.93 ms (**1.4×**) |
| rustcrypto-slh-dsa, `soft` build | 29.6 ms (**1.4×**) | 226 ms (**1.4×**) | 231 µs (**1.5×**) | 1.78 ms (**1.6×**) |
| fips205, `asm` build (n=2) | 11.3 ms (**3.8×**) | 93.3 ms (**3.5×**) | 99.5 µs (**3.4×**) | 401 µs (**7.1×**) |
| rustcrypto-slh-dsa, `tuned` build (n=2) | 6.89 ms (**6.3×**) | 51.9 ms (**6.3×**) | 55.4 µs (**6.2×**) | 355 µs (**8.0×**) |
| variant-C (old structure + ARMv8) | 13.2 ms (**3.2×**) | 101 ms (**3.2×**) | 103 µs (**3.3×**) | 429 µs (**6.5×**) |
| variant-D (current structure + ARMv8; n=2) | 11.4 ms (**3.7×**) | 85.8 ms (**3.8×**) | 84.2 µs (**4.0×**) | 449 µs (**6.2×**) |

For the `asm` and `tuned` rows, the ratio is against the verified crate in that same build (43.0 ms / 326 ms /
338 µs and 43.2 ms / 328 ms / 343 µs, the same within 1%). LTO, codegen-units = 1 and target-cpu = native still
change the verified crate by under 2%.

**Remaining gap (conclusion).** The optimised verified crate signs in 325 ms. That is 5.2× slower than RustCrypto
(62.6 ms) and 5.8× slower than OpenSSL (56.4 ms). It is still 1.5× slower than portable C
(slhdsa-c, 219 ms) and 1.2× slower than PQClean (267 ms), but 1.45× faster than fips205 as shipped (472 ms). The 5.2× splits cleanly:

- **3.6× is hardware SHA-2.** RustCrypto takes 62.6 ms with it and 226 ms forced to portable SHA-256.
- **1.4× is the verified crate's portable compression function.** It is about 1.6× slower per block than
  `sha2`'s portable code: 2.56 µs against 1.60 µs per KiB in the micro-benchmark.

Per-call overhead is essentially gone: 99% of samples are in `compress`, and the compression count matches
RustCrypto's algorithm. The 1.4× could be won back in safe Rust by speeding up `compress`, for example a rolling
16-word message schedule and fewer bounds-checked byte loads. That is the "not proof-cheap" restructuring
`opt/README.md` mentions. Hardware SHA-2 on the current structure (variant D) gives 3.8× and 85.8 ms. That is
still 1.37× behind RustCrypto. With about 18 ns per hardware compression, D spends about 40 ms of its 86 ms in
`compress`; the rest is overhead that only matters once hashing is fast: slice→array copies, `ADRSc`
serialisation, and the remaining `Vec`s in WOTS+/XMSS/`base_2b`. D needs `unsafe` intrinsics, with the
verification consequences described under run 1's variants section.

**Absolute numbers against run 1.** On the quieter machine, the implementations that did not change came in
within about 0–5% of run 1, mostly slightly faster:

| implementation | run 1 | run 2 |
|---|---|---|
| verified-before sign | 789 ms | 785 ms |
| verified-before keygen | 108.4 ms | 102.5 ms |
| verified-before verify | 824 µs | 805 µs |
| rustcrypto sign | 62.6 ms | 62.6 ms |
| openssl sign | 55.9 ms | 56.4 ms |
| fips205 sign | 473 ms | 472 ms |
| slhdsa-c sign | 222 ms | 219 ms |
| pqclean sign | 272 ms | 267 ms |

Per-round spreads were also tighter (mostly ±0.1–1.6%, at most ±6% for variant D signing, against ±2–4% in
run 1). The run-1 ratios therefore stand. The opt/README estimate of 2.41× (from its own `bench.sh`) matches this
measurement exactly.

## Full tables, run 2 (`results/run2/summary.md`)

The summary header says "4 rounds" because that is the maximum: `tuned` and `asm` have 2 rounds, and variant-D
appears only in rounds 3–4.

#### Signature operations

Median time per operation over all samples of all 4 rounds; **bold** = speed-up over the verified crate
in the same build configuration (>1 = faster than verified); ±x% = half the range of the per-round medians.

##### config `default`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 42.88 ms <sub>±1.4%</sub> | 325.19 ms <sub>±0.8%</sub> | 332.85 ms <sub>±2.7%</sub> | 337.64 µs <sub>±1.4%</sub> | 2.79 ms <sub>±0.6%</sub> |
| verified-before | 102.50 ms **0.42×** <sub>±0.2%</sub> | 784.96 ms **0.41×** <sub>±1.4%</sub> | 788.48 ms **0.42×** <sub>±1.5%</sub> | 805.27 µs **0.42×** <sub>±1.3%</sub> | 3.17 ms **0.88×** <sub>±1.3%</sub> |
| variant-A | 58.94 ms **0.73×** <sub>±0.2%</sub> | 452.97 ms **0.72×** <sub>±2.9%</sub> | 459.80 ms **0.72×** <sub>±1.1%</sub> | 468.31 µs **0.72×** <sub>±1.0%</sub> | 2.94 ms **0.95×** <sub>±0.5%</sub> |
| variant-B | 48.46 ms **0.88×** <sub>±0.6%</sub> | 368.93 ms **0.88×** <sub>±4.3%</sub> | 380.65 ms **0.87×** <sub>±2.1%</sub> | 384.56 µs **0.88×** <sub>±0.4%</sub> | 2.80 ms **1.00×** <sub>±0.9%</sub> |
| variant-C | 13.20 ms **3.2×** <sub>±0.3%</sub> | 100.86 ms **3.2×** <sub>±3.5%</sub> | 101.63 ms **3.3×** <sub>±1.2%</sub> | 103.41 µs **3.3×** <sub>±0.7%</sub> | 428.97 µs **6.5×** <sub>±3.0%</sub> |
| variant-D | 11.44 ms **3.7×** <sub>±0.2%</sub> | 85.77 ms **3.8×** <sub>±6.4%</sub> | 86.27 ms **3.9×** <sub>±3.2%</sub> | 84.21 µs **4.0×** <sub>±3.1%</sub> | 449.09 µs **6.2×** <sub>±0.1%</sub> |
| rustcrypto-slh-dsa | 8.29 ms **5.2×** <sub>±0.8%</sub> | 62.55 ms **5.2×** <sub>±0.2%</sub> | 63.20 ms **5.3×** <sub>±1.0%</sub> | 63.72 µs **5.3×** <sub>±3.3%</sub> | 363.90 µs **7.7×** <sub>±0.1%</sub> |
| fips205 | 61.23 ms **0.70×** <sub>±0.3%</sub> | 471.76 ms **0.69×** <sub>±0.1%</sub> | 475.46 ms **0.70×** <sub>±1.3%</sub> | 483.26 µs **0.70×** <sub>±1.0%</sub> | 2.16 ms **1.3×** <sub>±0.2%</sub> |
| openssl | 7.39 ms **5.8×** <sub>±1.6%</sub> | 56.39 ms **5.8×** <sub>±1.6%</sub> | 56.51 ms **5.9×** <sub>±1.0%</sub> | 58.68 µs **5.8×** <sub>±0.9%</sub> | 405.13 µs **6.9×** <sub>±1.2%</sub> |
| slhdsa-c | 28.62 ms **1.5×** <sub>±0.1%</sub> | 218.79 ms **1.5×** <sub>±3.3%</sub> | 222.16 ms **1.5×** <sub>±1.0%</sub> | 225.61 µs **1.5×** <sub>±0.9%</sub> | 1.86 ms **1.5×** <sub>±0.1%</sub> |
| pqclean-r3 | 35.17 ms **1.2×** <sub>±0.1%</sub> | 267.25 ms **1.2×** <sub>±1.0%</sub> | 270.47 ms **1.2×** <sub>±0.9%</sub> | 263.14 µs **1.3×** <sub>±3.6%</sub> | 1.93 ms **1.4×** <sub>±1.7%</sub> |

##### config `soft`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 42.89 ms <sub>±1.2%</sub> | 324.36 ms <sub>±0.5%</sub> | 329.54 ms <sub>±0.9%</sub> | 335.35 µs <sub>±0.4%</sub> | 2.80 ms <sub>±0.7%</sub> |
| verified-before | 102.54 ms **0.42×** <sub>±0.8%</sub> | 787.56 ms **0.41×** <sub>±1.3%</sub> | 784.05 ms **0.42×** <sub>±0.6%</sub> | 801.06 µs **0.42×** <sub>±0.5%</sub> | 3.17 ms **0.89×** <sub>±0.5%</sub> |
| rustcrypto-slh-dsa | 29.62 ms **1.4×** <sub>±0.6%</sub> | 225.80 ms **1.4×** <sub>±0.5%</sub> | 229.03 ms **1.4×** <sub>±0.7%</sub> | 231.18 µs **1.5×** <sub>±0.3%</sub> | 1.78 ms **1.6×** <sub>±1.1%</sub> |
| fips205 | 61.17 ms **0.70×** <sub>±0.1%</sub> | 471.62 ms **0.69×** <sub>±0.2%</sub> | 474.41 ms **0.69×** <sub>±0.1%</sub> | 481.13 µs **0.70×** <sub>±0.0%</sub> | 2.16 ms **1.3×** <sub>±0.1%</sub> |

##### config `tuned`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 43.21 ms <sub>±1.0%</sub> | 327.95 ms <sub>±0.3%</sub> | 332.84 ms <sub>±0.4%</sub> | 342.65 µs <sub>±0.3%</sub> | 2.85 ms <sub>±0.3%</sub> |
| verified-before | 105.08 ms **0.41×** <sub>±0.2%</sub> | 802.82 ms **0.41×** <sub>±0.0%</sub> | 808.32 ms **0.41×** <sub>±0.5%</sub> | 820.42 µs **0.42×** <sub>±0.4%</sub> | 3.28 ms **0.87×** <sub>±0.5%</sub> |
| variant-A | 59.41 ms **0.73×** <sub>±0.2%</sub> | 454.95 ms **0.72×** <sub>±0.1%</sub> | 462.05 ms **0.72×** <sub>±0.0%</sub> | 472.32 µs **0.73×** <sub>±0.5%</sub> | 2.98 ms **0.96×** <sub>±1.3%</sub> |
| variant-B | 48.46 ms **0.89×** <sub>±0.3%</sub> | 371.37 ms **0.88×** <sub>±0.0%</sub> | 377.38 ms **0.88×** <sub>±1.8%</sub> | 381.78 µs **0.90×** <sub>±0.6%</sub> | 2.83 ms **1.0×** <sub>±0.2%</sub> |
| variant-C | 12.99 ms **3.3×** <sub>±0.7%</sub> | 100.16 ms **3.3×** <sub>±1.3%</sub> | 104.54 ms **3.2×** <sub>±2.4%</sub> | 104.52 µs **3.3×** <sub>±0.4%</sub> | 428.63 µs **6.7×** <sub>±0.9%</sub> |
| rustcrypto-slh-dsa | 6.89 ms **6.3×** <sub>±0.0%</sub> | 51.90 ms **6.3×** <sub>±0.1%</sub> | 52.50 ms **6.3×** <sub>±0.0%</sub> | 55.40 µs **6.2×** <sub>±0.0%</sub> | 355.14 µs **8.0×** <sub>±0.1%</sub> |
| fips205 | 62.23 ms **0.69×** <sub>±0.0%</sub> | 478.42 ms **0.69×** <sub>±0.0%</sub> | 482.02 ms **0.69×** <sub>±0.0%</sub> | 477.84 µs **0.72×** <sub>±0.8%</sub> | 2.15 ms **1.3×** <sub>±0.0%</sub> |

##### config `asm`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 43.02 ms <sub>±0.4%</sub> | 326.28 ms <sub>±0.0%</sub> | 329.40 ms <sub>±0.1%</sub> | 337.92 µs <sub>±0.3%</sub> | 2.83 ms <sub>±0.6%</sub> |
| verified-before | 101.73 ms **0.42×** <sub>±0.1%</sub> | 785.42 ms **0.42×** <sub>±0.6%</sub> | 784.75 ms **0.42×** <sub>±0.1%</sub> | 806.55 µs **0.42×** <sub>±0.3%</sub> | 3.15 ms **0.90×** <sub>±0.1%</sub> |
| fips205 | 11.26 ms **3.8×** <sub>±0.1%</sub> | 93.30 ms **3.5×** <sub>±0.0%</sub> | 93.90 ms **3.5×** <sub>±0.0%</sub> | 99.54 µs **3.4×** <sub>±1.2%</sub> | 401.22 µs **7.1×** <sub>±0.9%</sub> |

##### tuned / default, same implementation

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 0.99× | 0.99× | 1.00× | 0.99× | 0.98× |
| verified-before | 0.98× | 0.98× | 0.98× | 0.98× | 0.97× |
| variant-A | 0.99× | 1.00× | 1.00× | 0.99× | 0.99× |
| variant-B | 1.00× | 0.99× | 1.01× | 1.01× | 0.99× |
| variant-C | 1.02× | 1.01× | 0.97× | 0.99× | 1.00× |
| rustcrypto-slh-dsa | 1.20× | 1.21× | 1.20× | 1.15× | 1.02× |
| fips205 | 0.98× | 0.99× | 0.99× | 1.01× | 1.00× |


#### SHA-256 one-shot (median per call; MB/s in parentheses)

##### config `asm`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 34.7 ns (1845 MB/s) | 34.7 ns (2937 MB/s) | 302.8 ns (3382 MB/s) |
| sha2-0.10 | 29.5 ns (2172 MB/s) | 29.5 ns (3462 MB/s) | 299.3 ns (3421 MB/s) |
| sha2-0.11 | 32.8 ns (1951 MB/s) | 29.4 ns (3470 MB/s) | 299.9 ns (3414 MB/s) |
| variant-B-soft-streaming | 280.7 ns (228 MB/s) | 301.4 ns (338 MB/s) | 2.38 µs (431 MB/s) |
| variant-C-armv8 | 37.8 ns (1695 MB/s) | 54.7 ns (1865 MB/s) | 307.9 ns (3326 MB/s) |
| verified | 323.5 ns (198 MB/s) | 311.2 ns (328 MB/s) | 2.53 µs (404 MB/s) |

##### config `default`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 34.7 ns (1845 MB/s) | 34.7 ns (2939 MB/s) | 302.7 ns (3383 MB/s) |
| sha2-0.10 | 203.1 ns (315 MB/s) | 203.3 ns (502 MB/s) | 1.73 µs (593 MB/s) |
| sha2-0.11 | 32.8 ns (1952 MB/s) | 29.4 ns (3468 MB/s) | 300.0 ns (3413 MB/s) |
| variant-B-soft-streaming | 280.1 ns (228 MB/s) | 303.4 ns (336 MB/s) | 2.40 µs (427 MB/s) |
| variant-C-armv8 | 37.8 ns (1691 MB/s) | 55.4 ns (1843 MB/s) | 308.2 ns (3323 MB/s) |
| verified | 317.4 ns (202 MB/s) | 316.2 ns (323 MB/s) | 2.56 µs (399 MB/s) |

##### config `soft`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 34.7 ns (1845 MB/s) | 34.7 ns (2937 MB/s) | 302.7 ns (3383 MB/s) |
| sha2-0.10 | 203.3 ns (315 MB/s) | 203.3 ns (502 MB/s) | 1.73 µs (594 MB/s) |
| sha2-0.11 | 191.1 ns (335 MB/s) | 191.5 ns (533 MB/s) | 1.60 µs (638 MB/s) |
| variant-B-soft-streaming | 278.1 ns (230 MB/s) | 298.7 ns (342 MB/s) | 2.45 µs (418 MB/s) |
| variant-C-armv8 | 37.8 ns (1695 MB/s) | 54.7 ns (1865 MB/s) | 308.1 ns (3323 MB/s) |
| verified | 321.5 ns (199 MB/s) | 314.3 ns (325 MB/s) | 2.55 µs (401 MB/s) |

# Run 1: pre-optimisation (kept unchanged)

**In this run, `verified` is the pre-optimisation crate** (now `../opt/original/rust`, `verified-before` in
run 2). Every ratio here compares against that old crate. The variants A/B/C below are my experiments that
motivated the optimisation. The text is as written before the optimisation, so "not applied to `rust/`" was true
at the time. Numbers come from `results/run1/` (four rounds, 23:11–00:13, under heavier load).

## Setup

| | |
|---|---|
| Hardware | Apple M5 Ultra (arm64), 36 cores, 512 GiB. Single-threaded benchmarks. |
| OS | macOS 27.2 (26B118) |
| Toolchain | rustc/cargo 1.100.0 (LLVM 23.1.5); Apple clang 21.0.0 for C |
| Harness | criterion 0.8.2. Flat sampling, 10 samples for keygen/sign (≥1 s warm-up, 4–6 s measurement) and 30 for verify. |
| Load | Shared machine, with other agents running Lean builds. 1-minute load average was 1.9–12 (mostly 2–5) on 36 cores. |

**Implementations** (all SLH-DSA-SHA2-128s, pure interface, empty context):

| name | what | version | SHA-256 used |
|---|---|---|---|
| `verified` | `../rust` (crate `slhdsa`), unmodified | path dep | its own portable, verified code |
| `rustcrypto-slh-dsa` | RustCrypto `slh-dsa` | 0.2.0-rc.5 (sha2 0.11.1) | sha2 0.11: ARMv8 SHA-2 instructions, detected at run time |
| `fips205` | `fips205` crate | 0.5.0 (sha2 0.10.9) | sha2 0.10 **portable**: 0.10 uses the ARMv8 instructions only with its `asm` feature, which fips205 does not enable |
| `openssl` | Homebrew OpenSSL, EVP API through `c/ossl_harness.c` | 4.1.0 | ARMv8 assembly |
| `slhdsa-c` | slh-dsa/slhdsa-c, vendored in `vendor/`, `-O3 -fomit-frame-pointer` | commit 2b111e0 (2025-06-15) | portable C |
| `pqclean-r3` | PQClean `sphincs-sha2-128s-simple` "clean", through `pqcrypto-sphincsplus` | 0.7.2 | portable C. **Round-3 SPHINCS+, not FIPS 205.** |
| `variant-A/B/C` | modified copies of `../rust/src` in `variants/` (see below). **Not verified.** | – | portable / portable / ARMv8 |

**Build configurations**, each a separate build:

- `default`: plain `cargo bench`, i.e. the release profile (opt-level 3, no LTO, 16 codegen units, generic aarch64-apple-darwin target, which already includes `sha2`/`neon`). Every library as its users get it.
- `soft`: `RUSTFLAGS='--cfg sha2_backend="soft"'` (sha2 0.11) plus `sha2/force-soft` (sha2 0.10). This forces portable SHA-256 in the two RustCrypto-based crates.
- `tuned`: `lto = "fat"`, `codegen-units = 1`, `-C target-cpu=native`, applied to the Rust implementations.
- `asm`: default profile with sha2 0.10's `asm` feature, which gives fips205 the ARMv8 backend.

The verified crate does not use `sha2`, so it is identical in `default`, `soft` and `asm`. It is measured in every
configuration as the anchor, and every ratio below compares against the verified crate in the same build.

**Method.** Keys come from fixed seeds (SK.seed = 0x11…, SK.prf = 0x22…, PK.seed = 0x33…) through each library's
seeded keygen. Signing is deterministic (opt_rand = PK.seed) everywhere except PQClean, which has no deterministic
API and draws 16 random bytes per signature. Messages are 32 B and 1 MiB. Keys are parsed into each library's key
object before timing. OpenSSL creates its `EVP_PKEY_CTX` inside every timed call, as a typical caller would.
Within a round the implementations run back to back for each operation. Rounds alternate forward and reversed
library order, and also alternate the order of the configurations. Each table cell is the median of all
per-iteration samples from all four rounds. `±x%` is half the range of the four per-round medians, which shows
the drift between rounds.

## Interoperability (checked before timing; `src/bin/interop.rs`, `results/run1/interop.md`)

| implementation | scheme | same SK/PK from same seeds | verifies verified-crate sig | its sig verifies under verified crate | sig bytes identical | rejects 1-bit-flipped sig |
|---|---|---|---|---|---|---|
| rustcrypto-slh-dsa | FIPS 205 | yes | yes | yes | yes | yes |
| fips205 | FIPS 205 | yes | yes | yes | yes | yes |
| openssl | FIPS 205 | yes | yes | yes | yes | yes |
| slhdsa-c | FIPS 205 | yes | yes | yes | yes | yes |
| pqclean-r3 | SPHINCS+ r3 | yes | no (expected) | no (expected) | n/a (randomised) | yes |
| variant-A, B, C | FIPS 205 | yes | yes | yes | yes | yes |

These checks ran for 32 B and 1 KiB messages. Every FIPS 205 implementation produces exactly the verified crate's
deterministic signature bytes. The round-3 key generation matches FIPS 205 (same PK.root), but its signatures do
not cross-verify, as expected. Variants A, B and C also pass the crate's own NIST ACVP tests: `variants/*/tests/acvp.rs`
is a copy of `rust/tests/acvp.rs` (10 keyGen, 28 sigGen byte-exact, 28 sigVer, plus SHA-256 and HMAC checked
against `sha2`/`hmac`).

**Sizes** (all implementations): SK 64 B, PK 32 B, signature 7856 B.

## Main result (config `default`, median, speed-up over the verified crate)

| implementation | keygen | sign (32 B) | verify (32 B) | verify (1 MiB) |
|---|---|---|---|---|
| **verified** | 108 ms | 789 ms | 824 µs | 3.23 ms |
| rustcrypto-slh-dsa | 8.4 ms (12.9×) | 62.6 ms (12.6×) | 64.9 µs (12.7×) | 371 µs (8.7×) |
| openssl 4.1 | 7.7 ms (14.1×) | 55.9 ms (14.1×) | 59.5 µs (13.8×) | 407 µs (7.9×) |
| fips205 (portable SHA as shipped) | 64.6 ms (1.7×) | 473 ms (1.7×) | 488 µs (1.7×) | 2.21 ms (1.5×) |
| slhdsa-c (portable C) | 29.6 ms (3.7×) | 222 ms (3.6×) | 229 µs (3.6×) | 1.90 ms (1.7×) |
| pqclean-r3 (portable C, SPHINCS+ r3) | 36.9 ms (2.9×) | 272 ms (2.9×) | 280 µs (2.9×) | 1.96 ms (1.7×) |
| rustcrypto-slh-dsa, `soft` build | 30.4 ms (3.5×) | 231 ms (3.5×) | 237 µs (3.4×) | 1.82 ms (1.8×) |
| fips205, `asm` build | 11.5 ms (9.2×) | 95.2 ms (8.5×) | 99.8 µs (8.2×) | 407 µs (7.9×) |
| rustcrypto-slh-dsa, `tuned` build | 7.0 ms (15.7×) | 52.9 ms (15.9×) | 57.3 µs (14.9×) | 363 µs (9.2×) |

Signing a 1 MiB message costs the same as signing 32 B to within noise for every implementation. The
message is hashed only twice, against roughly 2–4 million compressions for the tree work. Verifying a 1 MiB
message, on the other hand, is dominated by hashing the message.

## Where the verified crate's time goes

**SHA-256 compression counts per operation** (`count/`, instrumented copy with a counter, deterministic signing, 32 B message):

| | keygen | sign | verify |
|---|---|---|---|
| verified crate (= `variants/base`) | 580,094 | 4,404,707 | 4,476 |
| with seed midstate (variants A/B/C) | 292,352 | 2,218,488 | 2,274 |

Keygen can be checked by hand: 512 WOTS+ leaves × (35 PRF + 35·15 F at 2 blocks each, plus one 11-block T_len)
plus 511 H at 2 blocks each gives 580,094. With the constant first block `PK.seed ‖ 0^48` precomputed, F, H and
PRF need 1 block each (22 + 32 + 9 ≤ 64) and T_len needs 10, giving 292,352 (−49.6%). Verify counts depend on the
digest (WOTS+ digits); they are 4,281 / 2,184 for the 1 KiB message.

**Profile of `slh_sign`** (macOS `sample`, 6 s over a signing loop, `results/run1/sample-sign.txt`; timings from
`src/bin/profile.rs`):
- 92% of signing is `ht_sign` (7 XMSS layers, each rebuilding a 511-leaf authentication path) and 8% is `fors_sign`.
- By leaf function: 79% is in `sha256` (compression plus padding, inlined). 21% is in `malloc`/`realloc`/`free`/`memmove`:
  every `thash` builds a fresh `Vec`, and `pad` builds another by pushing bytes one at a time.
- A `thash` F call costs about 350 ns: 2 × 141 ns of compression plus about 70 ns of allocation and copying.

**SHA-256 micro-benchmark** (one-shot, median per call; full tables below):

| | 64 B (2 blocks) | 102 B (2 blocks; the `F` input) | 1 KiB (17 blocks) |
|---|---|---|---|
| verified `sha256` | 317 ns | 311 ns | 2.49 µs (411 MB/s) |
| sha2 0.11, soft backend | 196 ns | 196 ns | 1.64 µs (625 MB/s) |
| sha2 0.10, soft (fips205's default) | 207 ns | 207 ns | 1.77 µs (580 MB/s) |
| sha2 0.11, ARMv8 (default) | 33 ns | 30 ns | 307 ns (3334 MB/s) |
| OpenSSL EVP, ARMv8 | 35 ns | 35 ns | 312 ns (3283 MB/s) |
| variant C (ARMv8 intrinsics) | 38 ns | 57 ns | 315 ns (3256 MB/s) |

The verified crate's portable compression function is about 1.5× slower than sha2's portable one, and the
ARMv8 instructions are about 8× faster than sha2's portable code.

**How the 12.6× gap to RustCrypto (signing) splits.** Hardware SHA-2 accounts for 3.7×: RustCrypto drops from
62.6 ms to 231 ms when forced to portable SHA-256. The remaining 3.5× comes from everything else:

- about 2× from recompressing the constant first block in every `thash` (RustCrypto caches the midstate; verified does not);
- about 1.25× from heap allocation and copying;
- about 1.5× from the slower portable compression function.

Multiplied together these give 1.7 × 1.25 × 1.5 ≈ 3.2, which roughly matches the 3.5× measured. Plain fips205
hashes with portable code (sha2 0.10 without `asm`) and, like the verified crate, does not cache the midstate.
It runs 1.7× faster than the verified crate.

## Optimisation variants (copies in `variants/`; none applied to `rust/`)

These variants are cumulative:

- **A, seed midstate**: `SeedCtx { seed, mid = compress(H0, PK.seed ‖ 0^48) }` is computed once per operation and
  threaded through every function in place of `pk_seed`. `thash` continues from `mid`, with the length counted
  from 64. Safe Rust, still uses `Vec`.
- **B, A plus no heap in hashing**: a streaming SHA-256 (`Sha256 { state, buf: [u8; 64], … }`) replaces
  `pad`/`Vec`. `thash`, `hash2`, HMAC and `H_msg` use stack buffers only. Safe Rust. The other `Vec`s (WOTS+
  public-key buffer, signature assembly, `base_2b`) are unchanged.
- **C, B plus ARMv8 SHA-2 intrinsics** in `compress` only (`vsha256hq_u32`, `vsha256h2q_u32`,
  `vsha256su0q_u32`, `vsha256su1q_u32`), selected at compile time by `target_feature = "sha2"`, with the portable
  code as fallback. This needs `unsafe` (`#![deny(unsafe_code)]` with one allowed module).

All three pass the ACVP vectors, and their signatures are byte-identical to the verified crate's (checked by
interop and by `count`).

Median, config `default` (step speed-up in parentheses, cumulative speed-up in bold):

| | keygen | sign 32 B | verify 32 B | SHA-256 compressions / sign |
|---|---|---|---|---|
| base (verified crate) | 108.4 ms | 789 ms | 824 µs | 4,404,707 |
| A: seed midstate | 61.2 ms (1.77×) | 468 ms (1.69×) **1.7×** | 477 µs (1.73×) | 2,218,488 |
| B: + no heap in hashing | 49.4 ms (1.24×) | 375 ms (1.25×) **2.1×** | 387 µs (1.23×) | 2,218,488 |
| C: + ARMv8 SHA-2 | 13.4 ms (3.69×) | 104 ms (3.61×) **7.6×** | 104 µs (3.71×) | 2,218,488 |
| *for reference: rustcrypto-slh-dsa* | 8.4 ms | 62.6 ms **12.6×** | 64.9 µs | – |
| *for reference: openssl* | 7.7 ms | 55.9 ms **14.1×** | 59.5 µs | – |

The `tuned` build changes none of base, A, B or C by more than about 2%. C is still about 1.7× slower than
RustCrypto. With hardware hashing, the remaining per-call overhead dominates:

- the streaming buffer is filled byte by byte (C's `sha256` of 102 B takes 57 ns against 30 ns for `sha2`);
- `ADRSc` is serialised on every call;
- `base_2b` and the WOTS+ and XMSS buffers still use `Vec`.

A further variant would probably bring C close to RustCrypto and OpenSSL: block-at-a-time `copy_from_slice`
and precomputed single-block layouts for F and H. This was not measured.

**Which optimisations require re-verification.** All of them change `rust/src`, so each one requires
re-running the Aeneas extraction and redoing the proofs.

- **A**: a new `SeedCtx` type appears in every signature. The proofs need a lemma that SHA-256 of `B ‖ m`
  equals continuing from `compress(H0, B)` with the length offset by 64. This follows naturally from a
  pad-then-fold specification, and the rest of the proofs mostly carry over.
- **B**: introduces a mutable streaming state with its own buffer invariants. It stays in the safe,
  Aeneas-translatable subset (no traits or closures), but the SHA-256 correctness proof has to be redone.
- **C**: needs `unsafe` and `core::arch` intrinsics, which Aeneas cannot translate. The intrinsics would need a
  Lean model, trusted or checked against ARM's pseudocode. That changes the trust base, since "no hash function is
  assumed correct" no longer holds unless the instruction semantics are themselves verified.

So the safe, verifiable steps (A+B, 2.1×) are cheap relative to C, which delivers the remaining 3.6× but at a
cost to the trust story.

## Full tables, run 1

(Generated by `summarize.py` from `results/run1/`; times are medians over 4 rounds.)

### Signature operations

Median time per operation over all samples of all 4 rounds; **bold** = speed-up over the verified crate
in the same build configuration (>1 = faster than verified); ±x% = half the range of the per-round medians.

#### config `default`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 108.44 ms <sub>±2.9%</sub> | 789.23 ms <sub>±3.8%</sub> | 818.43 ms <sub>±3.5%</sub> | 824.03 µs <sub>±2.2%</sub> | 3.23 ms <sub>±2.1%</sub> |
| variant-A | 61.20 ms **1.8×** <sub>±4.1%</sub> | 467.64 ms **1.7×** <sub>±3.7%</sub> | 475.71 ms **1.7×** <sub>±3.9%</sub> | 477.39 µs **1.7×** <sub>±2.3%</sub> | 3.04 ms **1.1×** <sub>±2.3%</sub> |
| variant-B | 49.38 ms **2.2×** <sub>±3.1%</sub> | 374.89 ms **2.1×** <sub>±2.3%</sub> | 378.56 ms **2.2×** <sub>±0.7%</sub> | 386.79 µs **2.1×** <sub>±2.6%</sub> | 2.86 ms **1.1×** <sub>±2.6%</sub> |
| variant-C | 13.38 ms **8.1×** <sub>±2.6%</sub> | 103.86 ms **7.6×** <sub>±3.1%</sub> | 103.31 ms **7.9×** <sub>±1.7%</sub> | 104.13 µs **7.9×** <sub>±2.0%</sub> | 436.43 µs **7.4×** <sub>±3.4%</sub> |
| rustcrypto-slh-dsa | 8.43 ms **12.9×** <sub>±1.8%</sub> | 62.63 ms **12.6×** <sub>±3.2%</sub> | 64.33 ms **12.7×** <sub>±3.1%</sub> | 64.94 µs **12.7×** <sub>±2.5%</sub> | 371.47 µs **8.7×** <sub>±2.8%</sub> |
| fips205 | 64.55 ms **1.7×** <sub>±3.2%</sub> | 473.06 ms **1.7×** <sub>±3.3%</sub> | 486.17 ms **1.7×** <sub>±3.4%</sub> | 487.59 µs **1.7×** <sub>±0.8%</sub> | 2.21 ms **1.5×** <sub>±3.4%</sub> |
| openssl | 7.71 ms **14.1×** <sub>±2.6%</sub> | 55.89 ms **14.1×** <sub>±3.5%</sub> | 58.42 ms **14.0×** <sub>±3.0%</sub> | 59.54 µs **13.8×** <sub>±1.7%</sub> | 407.04 µs **7.9×** <sub>±3.5%</sub> |
| slhdsa-c | 29.63 ms **3.7×** <sub>±3.4%</sub> | 222.21 ms **3.6×** <sub>±3.3%</sub> | 225.95 ms **3.6×** <sub>±3.1%</sub> | 229.46 µs **3.6×** <sub>±3.3%</sub> | 1.90 ms **1.7×** <sub>±3.4%</sub> |
| pqclean-r3 | 36.85 ms **2.9×** <sub>±5.3%</sub> | 272.47 ms **2.9×** <sub>±1.7%</sub> | 275.28 ms **3.0×** <sub>±3.1%</sub> | 279.86 µs **2.9×** <sub>±3.6%</sub> | 1.96 ms **1.7×** <sub>±3.5%</sub> |

#### config `soft`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 105.56 ms <sub>±3.1%</sub> | 808.68 ms <sub>±3.0%</sub> | 804.02 ms <sub>±2.4%</sub> | 814.43 µs <sub>±1.2%</sub> | 3.20 ms <sub>±1.9%</sub> |
| rustcrypto-slh-dsa | 30.35 ms **3.5×** <sub>±3.3%</sub> | 230.96 ms **3.5×** <sub>±3.2%</sub> | 233.62 ms **3.4×** <sub>±2.4%</sub> | 236.55 µs **3.4×** <sub>±2.3%</sub> | 1.82 ms **1.8×** <sub>±1.2%</sub> |
| fips205 | 62.37 ms **1.7×** <sub>±3.3%</sub> | 480.63 ms **1.7×** <sub>±3.2%</sub> | 481.70 ms **1.7×** <sub>±0.9%</sub> | 491.58 µs **1.7×** <sub>±3.0%</sub> | 2.20 ms **1.5×** <sub>±1.2%</sub> |

#### config `tuned`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 109.93 ms <sub>±2.4%</sub> | 840.81 ms <sub>±2.8%</sub> | 837.63 ms <sub>±2.4%</sub> | 855.44 µs <sub>±2.5%</sub> | 3.34 ms <sub>±3.5%</sub> |
| variant-A | 61.42 ms **1.8×** <sub>±1.9%</sub> | 476.61 ms **1.8×** <sub>±2.7%</sub> | 469.84 ms **1.8×** <sub>±2.3%</sub> | 485.20 µs **1.8×** <sub>±2.3%</sub> | 2.98 ms **1.1×** <sub>±1.4%</sub> |
| variant-B | 48.62 ms **2.3×** <sub>±2.2%</sub> | 373.29 ms **2.3×** <sub>±3.3%</sub> | 375.10 ms **2.2×** <sub>±3.2%</sub> | 392.80 µs **2.2×** <sub>±3.6%</sub> | 2.83 ms **1.2×** <sub>±2.0%</sub> |
| variant-C | 13.34 ms **8.2×** <sub>±2.1%</sub> | 102.00 ms **8.2×** <sub>±2.9%</sub> | 100.98 ms **8.3×** <sub>±3.6%</sub> | 104.47 µs **8.2×** <sub>±2.9%</sub> | 431.96 µs **7.7×** <sub>±3.2%</sub> |
| rustcrypto-slh-dsa | 7.01 ms **15.7×** <sub>±3.3%</sub> | 52.94 ms **15.9×** <sub>±3.3%</sub> | 53.56 ms **15.6×** <sub>±3.2%</sub> | 57.34 µs **14.9×** <sub>±3.3%</sub> | 362.64 µs **9.2×** <sub>±3.1%</sub> |
| fips205 | 63.43 ms **1.7×** <sub>±3.0%</sub> | 488.36 ms **1.7×** <sub>±3.2%</sub> | 491.01 ms **1.7×** <sub>±3.1%</sub> | 492.94 µs **1.7×** <sub>±2.3%</sub> | 2.21 ms **1.5×** <sub>±3.3%</sub> |

#### config `asm`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 105.08 ms <sub>±1.3%</sub> | 804.50 ms <sub>±2.2%</sub> | 811.47 ms <sub>±1.7%</sub> | 822.95 µs <sub>±2.9%</sub> | 3.21 ms <sub>±0.8%</sub> |
| fips205 | 11.48 ms **9.2×** <sub>±2.2%</sub> | 95.19 ms **8.5×** <sub>±2.2%</sub> | 95.87 ms **8.5×** <sub>±2.4%</sub> | 99.84 µs **8.2×** <sub>±3.0%</sub> | 407.24 µs **7.9×** <sub>±2.7%</sub> |

#### tuned / default, same implementation

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 0.99× | 0.94× | 0.98× | 0.96× | 0.97× |
| variant-A | 1.00× | 0.98× | 1.01× | 0.98× | 1.02× |
| variant-B | 1.02× | 1.00× | 1.01× | 0.98× | 1.01× |
| variant-C | 1.00× | 1.02× | 1.02× | 1.00× | 1.01× |
| rustcrypto-slh-dsa | 1.20× | 1.18× | 1.20× | 1.13× | 1.02× |
| fips205 | 1.02× | 0.97× | 0.99× | 0.99× | 1.00× |

### SHA-256 one-shot (median per call; MB/s in parentheses)

#### config `asm`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 35.4 ns (1807 MB/s) | 35.4 ns (2878 MB/s) | 310.4 ns (3299 MB/s) |
| sha2-0.10 | 30.8 ns (2080 MB/s) | 30.5 ns (3347 MB/s) | 304.7 ns (3361 MB/s) |
| sha2-0.11 | 33.4 ns (1916 MB/s) | 30.1 ns (3383 MB/s) | 305.7 ns (3350 MB/s) |
| variant-B-soft-streaming | 296.5 ns (216 MB/s) | 315.8 ns (323 MB/s) | 2.46 µs (416 MB/s) |
| variant-C-armv8 | 39.2 ns (1634 MB/s) | 57.0 ns (1789 MB/s) | 314.9 ns (3252 MB/s) |
| verified | 327.0 ns (196 MB/s) | 312.8 ns (326 MB/s) | 2.49 µs (410 MB/s) |

#### config `default`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 35.4 ns (1805 MB/s) | 35.4 ns (2880 MB/s) | 311.9 ns (3283 MB/s) |
| sha2-0.10 | 207.1 ns (309 MB/s) | 207.1 ns (493 MB/s) | 1.77 µs (580 MB/s) |
| sha2-0.11 | 33.4 ns (1915 MB/s) | 30.0 ns (3400 MB/s) | 307.1 ns (3334 MB/s) |
| variant-B-soft-streaming | 287.6 ns (223 MB/s) | 308.9 ns (330 MB/s) | 2.43 µs (422 MB/s) |
| variant-C-armv8 | 38.4 ns (1667 MB/s) | 56.8 ns (1795 MB/s) | 314.5 ns (3256 MB/s) |
| verified | 317.2 ns (202 MB/s) | 311.2 ns (328 MB/s) | 2.49 µs (411 MB/s) |

#### config `soft`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 36.5 ns (1751 MB/s) | 35.7 ns (2861 MB/s) | 313.6 ns (3265 MB/s) |
| sha2-0.10 | 207.5 ns (308 MB/s) | 207.5 ns (492 MB/s) | 1.76 µs (581 MB/s) |
| sha2-0.11 | 195.8 ns (327 MB/s) | 196.0 ns (520 MB/s) | 1.64 µs (625 MB/s) |
| variant-B-soft-streaming | 284.2 ns (225 MB/s) | 315.3 ns (324 MB/s) | 2.43 µs (421 MB/s) |
| variant-C-armv8 | 38.5 ns (1664 MB/s) | 57.1 ns (1788 MB/s) | 313.6 ns (3265 MB/s) |
| verified | 320.2 ns (200 MB/s) | 322.7 ns (316 MB/s) | 2.54 µs (403 MB/s) |

# Both runs

## Not measured, and why

- **liboqs**: the `oqs-sys` crate and liboqs itself build with CMake, which is not installed. Installing it was
  not essential (OpenSSL already covers optimised C with hardware SHA-2), so it was skipped. `oqs-sys` 0.11 also
  bundles liboqs 0.13.
- **AWS-LC**: `aws-lc-sys` 0.47.0 has no SLH-DSA (only ML-DSA in `pqdsa`).
- **BoringSSL**: has SLH-DSA-SHA2-128s but needs CMake/Go to build. Skipped.
- **`.tools/formosa-slhdsa`**: EasyCrypt security proofs only. It contains no executable implementation.
- **`openssl speed`**: the FFI harness was used instead, so that OpenSSL runs under the same criterion loop,
  deterministic signing, keys and messages as the others.
- **Randomised (hedged) signing** for the FIPS 205 libraries: it adds one 16-byte RNG call per signature, which
  is negligible against about 4.4 million (verified) or 2.2 million (others) compressions. PQClean is measured
  randomised because it has no deterministic API.
- **Multi-threading, memory use, other parameter sets** (including the `multi/` copy) and other platforms (x86-64,
  where sha2 and OpenSSL would use SHA-NI or AVX2).
- Constant-time behaviour was not assessed here.

## Caveats

- **Load.** Other agents were building Lean concurrently (1-minute load average 1.9–12 on 36 cores). Each
  benchmark is single-threaded and per-round medians agree within about ±4%, but absolute times may be a few
  percent pessimistic. The conclusions use ratios within one build, measured minutes apart with library order
  alternated.
- **Round 3 vs FIPS 205.** `pqclean-r3` is SPHINCS+ round 3.1 (sha2-128s-simple). It has the same sizes and
  the same number of hash calls, but different message processing (no context prefix, different digest-to-index
  mapping), so its signatures are not FIPS 205 signatures. It is included only as a portable-C cost reference.
- **Deterministic vs randomised.** All FIPS 205 rows sign deterministically with opt_rand = PK.seed. PQClean signs
  randomised.
- **"As shipped" for fips205 means portable SHA-256** on this platform, because sha2 0.10 needs its `asm` feature
  to use the ARMv8 instructions. The `asm` row shows what fips205 gains when an application enables it.
- **Variants A–D are not verified code** (the optimised `../rust` is). Their correctness evidence is the ACVP vectors and byte-identical
  output, nothing more.
- The `tuned` build recompiles everything with `-C target-cpu=native`. The C code is not affected; the C
  libraries were built with cc's release defaults (`-O3`), and slhdsa-c additionally with its Makefile flags.

## Files

- `Cargo.toml`, `build.rs`, `src/lib.rs`: uniform wrappers for all implementations.
- `benches/sig.rs`: keygen, sign and verify benchmarks. `benches/sha.rs`: SHA-256 micro-benchmark.
- `src/bin/interop.rs`: interoperability check. `src/bin/profile.rs`: coarse timing breakdown and a signing loop for `sample`.
- `count/`: compression counts.
- `variants/`, each with its ACVP tests:
  - `base`: the pre-optimisation crate (`../opt/original/rust/src`), benchmarked as `verified-before`.
  - `current`: a counted copy of today's `../rust/src`.
  - `a`, `b`, `c`: run-1 experiments on the old crate.
  - `d`: today's crate plus ARMv8 `compress`.
- `c/ossl_harness.c`: OpenSSL harness. `vendor/slhdsa-c`: vendored C implementation (ISC/MIT licensed, see `LICENSE` there).
- `run.sh`: runs everything. `summarize.py`: builds the tables. `results/run1/` (pre-optimisation) and `results/run2/` (after): raw criterion data, logs, interop, count, copy-check and `sample` output.
