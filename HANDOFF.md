# Handoff — state at 2026-11-21

Both composed theorems are finished: neither has a hypothesis left that is not about the forger.
The repository is under git from 2026-11-21 (first commit `d2a5a9b` is the whole project as it
stood then; nothing is pushed anywhere). For what the project proves overall, read `README.md`;
this file covers the two composed theorems, the Rust optimisation, the opt-in hardware backend,
the performance work of 2026-11-21 and the benchmark.

This file replaces the handoff of 2026-11-20, which described both theorems as unfinished.
`quantum/HANDOFF.md` and `security/Ideal/HANDOFF.md` are that older state and are kept for the
record only.

## Summary

| | Quantum random oracle | Ideal compression function |
|---|---|---|
| Headline | `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc_closed` (`quantum/Integration/SlhDsaComposedClosed.lean:64`, `:93`) | `suf_ideal_closed`, `euf_ideal_closed` (`security/Ideal/Realize/Final.lean:74`, `:91`) |
| Hypotheses | on the forger: `hq`, `hqs`, `hcap`; and `35 ≤ c.tl` | on the forger: `hqf`, `hqs`, `hlong`, `hout`; and arithmetic `QcAll qf qs ℓ ≤ 2^126` |
| Formerly assumed, now proved | `hInd` and all eleven bridge statements | all twelve realisers |
| Numeric, machine-checked | `≤ 2^-22` at `q = 2^40`, `qs = 2^20` (`…_qrom_enc_closed_num`, `SlhDsaComposedClosedNum.lean:187`, `:200`) | three points, table below (`Final.lean:108`–`:183`) |
| Rust-level statement | — | `rust_ideal_security_closed` (`security/Ideal/RustFinalClosed.lean:36`) |
| Build (coordinator ran) | `scripts/check-integration.sh` PASS: default target 7248 jobs, 103 `security` modules fresh, 46 Integration files compiled from scratch, 348 theorems, standard axioms only | `lake build` 8035 jobs; 1529 axiom reports parsed, all standard; no `sorry` |
| Independent audit | `quantum/AUDIT-closed.md`: nothing false or overstated; caveats below | `security/status/AUDIT-closed.md`: nothing false or overstated; caveats below |

Ideal-model numeric points (SUF and EUF, messages up to 2^26 bytes):

| signatures `qs` | forger's compression queries `qf` | forgery probability at most |
|---|---|---|
| ≤ 2^20 | ≤ 2^60 − 2^46 | 2^-70 + 2^-128 + 2^-61 |
| ≤ 2^40 | ≤ 2^64 | 2^-50 + 2^-88 + 2^-41 |
| ≤ 2^64 | ≤ 2^64 | 2^-44 + 2^-43 + 2^-31 |

## What exactly is proved (the auditors' wording)

**Ideal compression function.** SHA-256's compression function is replaced by a uniformly random
function, used for every SHA-256 call of SLH-DSA-SHA2-128s, and the forger may query it. For
every `opt_rand` sampler that depends only on (PK.seed, PK.root), and every forger that on every
execution path makes at most `qf` table queries and `qs` signing queries on messages of at most
`ℓ` bytes and outputs a message of at most `ℓ` bytes: the probability (over the table, the
uniform seeds, `opt_rand` and the forger's coins) of a strong forgery is at most
`epsItsrF qf (2·qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ + (66·QcAll + 40)/2^128 + polyP …/2^256`
(EUF likewise). The scheme is the INTERNAL interface, FIPS 205 Algorithms 18–20.

**Quantum random oracle.** For any caps `c` with `c.tl ≥ 35`, the four hash components (Thash,
H_msg, PRF, PRF_msg) are independent uniform random functions on the capped domains, extended by
constants outside. The scheme is the EXTERNAL pure byte interface (Algorithms 21/22/24, context
strings). For every quantum forger — one fixed program with arbitrary finite workspace and
initial state, whose only access to the hashes is one quantum oracle `|x,y⟩ ↦ |x, y + H(x)⟩`
(bytewise addition mod 256) on the disjoint union of the four domains, plus classical signing —
that on every path makes at most `q` oracle calls and `qs` signing queries, all within the caps:
its SUF-CMA (resp. EUF-CMA) advantage, averaged over the functions, is at most
`composedBoundFinal q qs (openCounts128s qs).noPrfMsg`.

## Caveats the claims carry

Ideal side:
- **Internal interface only.** No ideal-model theorem covers `slh_sign` / `slh_verify` with a
  context string. The auditor judges the extension an easy reduction; it is not done.
- **Random function, not SHA-256's compression.** No Davies–Meyer / ideal-cipher model.
- **Message length.** `hout` excludes forgeries on messages longer than `ℓ`; the numeric points
  take `ℓ ≤ 2^26` bytes.
- **Weak at many signatures.** About 2^-31 at 2^64 signatures: each signature is charged 2^25
  compression calls. Counts are deliberately coarse (every hash query charged 11 compressions).
- **ITSR leg** vacuous once `qf + 2·qs` reaches about 2^70 (proof technique, not an attack). The
  bound never drops below about 2^-80.
- **The Rust link is narrow.** The security conjunct averages over random tables; the Rust
  conjuncts are about the real compression function. They share the scheme, not a security claim.

Quantum side:
- **Reduction's hashing charged as quantum queries.** About 2.0·10^6 per signature, quadratically.
  Auditor's evaluation (Python, not machine-checked): 2^-22.9 at (2^40, 2^20); the bound exceeds 1
  for `qs ≥ 2^28` at any `q`, and for `q ≥ 2^53` at `qs = 2^20`.
- **Caps.** Outside the caps the hash functions are constants. That the experiment stays inside
  the caps is the hypothesis `hcap`; equivalence with unbounded random oracles is informal. The
  bound does not depend on `c.ml`, so any forger with bounded message length is covered.
- **Additive oracle**, not XOR: an XOR-model forger with `q` queries needs `2q` port calls.
- **`opt_rand`** may depend only on (PK.seed, PK.root); PK.seed distribution arbitrary.
- **Independence of the four components** idealises SHA-2 domain separation.
- **ITSR** keeps the reprogramming loss `2q'√(qs/2^128)`, which dominates the bound.

Both: FIPS 205 conformance of the shared scheme code and the Aeneas extraction were not re-audited
this round. The audits checked statements and definitions, not proofs (the kernel checks those),
and spot-checked two of the twelve realisers.

## Where the new work is

Ideal side (`security/`, all imported by `Ideal.lean`):
- `Ideal/Transport/*` (ten files from the previous round, now in the default target) and
  `Ideal/Transport/AdvTcr.lean` (whole-adversary invariance for class TCR).
- `Ideal/Realize/{Chain,Walk,Port,Phase1}.lean`: generic layer (reference core, hash query →
  compression chain, forger with a compression port, first-phase embedding).
- Realisers: `Tcr.lean`, `TcrCount.lean` (class TCR ×4); `PrfTr/PrfPort/PrfCount/PrfReal.lean`;
  `MsgHarness/MsgPort/MsgCount/MsgReal.lean`; `Itsr*.lean` (six files); `Fors*.lean` (seven);
  `Wots*.lean` (seven, headline file `WotsRealizers.lean`).
- `Ideal/Realize/FinalCore.lean`, `Final.lean` (assembly), `Ideal/RustFinalClosed.lean`.
- Notes per piece: `security/status/R-{tcr,prfmsg,itsr,fors,wots,final}.md`.

Quantum side (`quantum/`):
- Generic (`PQ/`, all in `PQ.lean`): `Interactive/QromBridgeEvalProg.lean` (`PUE.exists_prog`,
  `PUE.exists_model`, `PUE.compileQ`), `QromBridgeEvalQ.lean`, `QromBridgeEvalIAdv.lean`
  (`PUE.exists_iadv`), `QromBridgeTcr.lean`, `QromBridgeFors.lean`, `QromBridgeWotsPre.lean`,
  `QromBridgeWotsUd.lean`; `QROM/HybridRows.lean`, `ForsPullback.lean`, `ItsrPullback.lean`,
  `WotsPullbackUdTight.lean`.
- Per term (`Integration/`):

| term | closed theorem | file |
|---|---|---|
| PRF | `prf_term_suf/euf` + `QInd.prfMachSuf_withPrf` | `SlhDsaBridgeInd.lean` |
| PRF_msg | `QMsg.msg_term_suf/euf` | `SlhDsaBridgeMsg.lean` |
| class TCR ×4 | `tcr_terms_closed_128s` | `SlhDsaBridgeTcrClosed.lean` |
| FORS TCR | `tcrFv_term_closed_128s` | `SlhDsaBridgeForsClosed.lean` |
| FORS DSPR | `dspr_term_closed_128s` | `SlhDsaBridgeForsClosed2.lean` |
| WOTS TCR | `tcrT_term_closed_128s` | `SlhDsaBridgeTcrTClosed.lean` |
| WOTS UD, PRE | `ud_closed`, `pre_closed` | `SlhDsaBridgeWotsClosed.lean` |
| ITSR | `itsr_closed` | `SlhDsaBridgeMachItsr2.lean` |

- Machine models: `SlhDsaBridgeMach{,Fors,Fors2,Wots,Itsr,Itsr2}.lean`. Assembly:
  `SlhDsaComposedClosed.lean`, `SlhDsaComposedClosedNum.lean`. Intermediate headlines
  (`SlhDsaComposedEnc2.lean`, `SlhDsaComposedEnc2Msg.lean`) remain.
- Notes per piece: `quantum/HANDOFF-{qprf,qmach,qtcr,qfors,qwots}.md`.

Two technical points worth knowing before touching these proofs:
- Equalities between programs over different worlds or bundles are closed by kernel-only `rfl`
  tactics (`krfl`/`kexact`, `qm_kernel_rfl`, `qtcr_kernel_rfl`): they assign `Eq.refl` and let the
  kernel check it. No axiom. The elaborator's own `rfl` times out or overflows on these; one
  attempt at a direct kernel `rfl` without first stripping `Coded.View` arguments used over 60 GB.
- Statements whose type mentions an `IsQueryBoundP` of a closed key-structure program can make
  `whnf` evaluate the structure walk. The fixes used are `irreducible` wrappers and stating lemmas
  over a variable program with an equation hypothesis.

## Rust optimisation and benchmark

- `rust/src` and `lean/Slhdsa` now hold an optimised, re-verified crate: the constant first
  SHA-256 block (`PK.seed ‖ 0^48`) is compressed once per operation, and `F`/`PRF`/`H` build their
  single block on the stack. Public API, `lean/Spec`, and `lean/Slhdsa/Theorems.lean` are
  unchanged; re-extraction reproduces the generated Lean; `lean/` and `security/` rebuild green.
- The previous crate and proofs are in `opt/original/`. `opt/` is the working copy the change was
  developed in (`opt/README.md` has the per-file detail).
- Benchmark: `bench/RESULTS.md` (`bench/run.sh` reproduces it, about 35 minutes; Apple Silicon,
  default release build, median of 4 rounds). Run 2 is against the optimised crate; run 1, kept
  below it in the file, is the original.

  | | keygen | sign | verify | compressions per sign |
  |---|---|---|---|---|
  | before | 102.5 ms | 785 ms | 805 µs | 4,404,707 |
  | after | 42.9 ms | 325 ms | 338 µs | 2,218,488 |

  After the change the crate is 5.2× slower than RustCrypto `slh-dsa` (was 12.6×) and 5.8×
  slower than OpenSSL 4.1 (was 14.1×); 1.45× faster than `fips205` as shipped; 1.5× behind
  portable C (slhdsa-c). Of the remaining 5.2×, about 3.6× is hardware SHA-2 and about 1.4× is
  the crate's portable compression function (about 1.6× slower per block than the `sha2`
  crate's portable code); per-call overhead is now negligible (99% of signing is `compress`).
- Interoperability is clean before and after: same keys from the same seeds, cross-verification
  both ways and byte-identical deterministic signatures against RustCrypto, `fips205`, OpenSSL
  and slhdsa-c. Not built: liboqs, BoringSSL (need CMake), AWS-LC (no SLH-DSA in the crate).

## Opt-in hardware SHA-2 (`hw-sha2`) and the performance work of 2026-11-21

The crate was restructured so that, with the opt-in `hw-sha2` feature, it is faster than
RustCrypto and OpenSSL on this machine, and the proofs were redone for the new code. The six
headline theorems and `lean/Spec` are unchanged.

**Numbers** (`bench/results/run4`, criterion, 2 rounds, Apple M5 Ultra; keygen / sign 32 B /
verify 32 B / verify 1 MiB):

| | keygen | sign | verify | verify 1 MiB |
|---|---|---|---|---|
| this crate, default build | 40.4 ms | 305 ms | 324 µs | 2.69 ms |
| this crate, `hw-sha2` | 4.00 ms | 30.2 ms | 35.4 µs | 352 µs |
| RustCrypto `slh-dsa` | 8.30 ms | 62.6 ms | 63.8 µs | 365 µs |
| OpenSSL 4.1 | 7.32 ms | 56.0 ms | 58.9 µs | 405 µs |

Before this work `hw-sha2` was 11.5 ms / 83.7 ms / 85.3 µs (run 3).

**Verified code (`rust/src`, all re-proved):**
- `hash::chain_blocks(state, blocks, start, end)` is the one hot primitive: for each block `i`,
  for `t` in `start[i]..end[i]`: write `t` into bytes 18..22, compress, put the first 16 bytes
  of the digest into bytes 22..38. One step is `F`, `PRF` or `H`. The portable code is two
  nested loops.
- WOTS+ (`wots.rs`): the 35 `PRF` blocks are built once; one step `0..1` on all of them gives
  the secret values in place; byte 9 (the address type) is switched, which turns each into its
  chain block; the chains are `chain_blocks` with `(0, 15)`, `(0, digit)` or `(digit, 15)`.
  `hash::thash_values` builds the ten blocks of `T_len` on the stack from the block values.
- FORS (`fors.rs`): `fors_batch` computes a subtree of up to 128 leaves: leaves are two steps
  (`PRF`, type switch, `F`) numbered by the tree index, and each level is one step on
  `pair_block`s. `fors_node` uses it for heights up to 7 and the old recursion above.
  `fors_pk_from_sig` climbs the 14 trees together, one `chain_blocks` call per level.
- `sha256::sha256_from` compresses whole blocks straight from the message and copies only the
  tail; `hash::h_msg_inner` assembles the first block `R ‖ PK.seed ‖ PK.root ‖ M[0..16]` and
  hashes the rest of a long message where it lies.
- `#[inline]` hints on `compress` and the small block-building helpers (no effect on the
  translation beyond line numbers).

**Proofs:** `lean/Slhdsa/Proofs/{Sha256,Hash,Wots,Fors}.lean`. The model of one step is
`stepBlock` / `runBlock` in `Hash.lean`; `chain_blocks_spec` says each block ends as `runBlock`
of its start. Layout lemmas (`stepBlock_thash`, `runBlock_chain`, `stepBlock_pair_value`,
`block_set_typ`, `padFrom_values`) connect that to `Spec.thash` and `Spec.chain`.
- One internal statement changed: `fors_node_spec` now requires `(i + 1)·2^z < 2^32` where it
  had `≤`. The batch forms `idx + 1` for each leaf index, which overflows at `idx = 2^32 − 1`;
  the old statement is false for the new code (the proof agent machine-checked a
  counterexample, `fors_node 4294967295 0` panics). Every use in the scheme has indices below
  14·2^12. `fors_sign_spec` and everything above it are unchanged.
- Checked after the final re-extraction: `scripts/check.sh` (tests in both builds,
  re-extraction, `lean/`, `spectest`, `security/`, no placeholder) and
  `quantum/scripts/check-integration.sh`.

**Unverified code (`hw-sha2`):** module `hw` of `rust/src/sha256.rs`, about 330 lines with
comments, the crate's only `unsafe`. Off by default, AArch64 little-endian only, runtime CPU
detection off Apple targets. It replaces exactly two functions, `sha256::compress` and
`hash::chain_blocks`; a build with the feature equals the verified build provided those two
replacements return what the portable code returns. That is tested, not proved.
- `hw::chain_blocks` takes chains in order into four slots, runs until the first slot is out of
  steps, writes finished chains back and refills. `run` keeps each chain's value in registers
  across steps and rebuilds only the words that change.
- Why it is fast, measured on this CPU: `sha256h` and `sha256h2` share one execution unit at two
  cycles each (throughput), four-cycle latency; the schedule instructions run elsewhere. So a
  hash costs 64 cycles of that unit, and one hash alone leaves it idle about a third of the
  time. Four lanes fill it. Lanes are staggered by a quarter of a hash because otherwise all
  four are between hashes at once and the unit idles. Rounds 0..3 depend only on bytes 0..16 of
  the block, which are the same for a whole WOTS+ key or FORS instance, so they are computed
  once and cached by those bytes; the last `sha256h2` is skipped because only four output
  words are kept. That is 29 round instructions per hash instead of 32; the kernel measures
  12.97 ns per hash against 12.7 ns for 58 cycles.
- Tests (`rust/tests/compress.rs`, run with and without the feature; `scripts/check.sh` runs
  both): `compress` against the `sha2` crate on 200,000 random and 5,140 edge-case inputs;
  `chain_blocks` against a reference written from that function on 7,360 random batches (0 to
  41, 64, 70, 128, 140 blocks; uniform, mixed, single-step and random ranges; equal and
  different block heads; step numbers around 2^16, 2^24 and 2^32); independence of chains;
  the same panics. ACVP vectors pass both ways, in debug, and with
  `RUSTFLAGS='-C target-feature=-sha2'` (the runtime-detection path).
- Interoperability with the feature on is clean (`bench/results/run4/interop-hw.md`), and the
  compression count is unchanged at 2,218,488 per signature: the same hashes, in a different
  order.

**Tried and rejected** (all measured in scratch copies, nothing kept):
- A fifth chain on scalar integer SHA-256, woven between the lanes. Correct, but slower: one
  scalar round per tick made the kernel 13.3 ns per hash against 12.97 without it.
- Hashing the `T_len` of two adjacent leaves side by side: 0.3%.
- Larger FORS batches than 128 leaves: under 0.1%.
- Keeping long-message hashing state in registers across blocks would need a new verified
  multi-block function; the gain is about 4% on the message part of a 1 MiB verification.

**Not tested:** a CPU without the instructions with the feature on (the fall-through to the
portable code; no such machine here), and any real non-Apple AArch64 machine. The staggering
and lane count are tuned to this CPU.

**History:** commit `2a4bea5` is an intermediate, fully verified design (lockstep chains with
`compress_many`, 41 ms sign); `ad4e485` is the first `hw-sha2` (one block at a time, 84 ms).

## Not done

- **x86 SHA-NI backend.** `hw-sha2` does nothing on x86-64.
- **A formal statement for the `hw-sha2` build.** The assumption above is written in prose and
  tested. It could be stated in Lean, and the build with the feature proved correct from a model
  of the four SHA-256 instructions; nothing of that exists.
- **Ideal-model theorem for the context-string interface** (first ideal caveat above).
- **`rust/ct-evidence`** was not re-run against the optimised crate, and its harness still calls
  `wots::chain`, which no longer exists. The new code's data-dependent control flow is in
  `chain_blocks` (step ranges, which are WOTS+ digits and tree indices) and, with `hw-sha2`, in
  the slot scheduling and the cache of the first rounds (keyed on the first 16 block bytes, an
  address prefix); none of it was traced. **`multi/`** (six parameter
  sets) still has the old hashing code.
- **Stale text.** These still describe the theorems as conditional: the headers of
  `security/Ideal/ComposeFinal.lean`, `quantum/Integration/SlhDsaComposedFinal.lean` (lines 35–55),
  `SlhDsaBridgePrf.lean` (30–37), `SlhDsaOpenCounts.lean` (15–17); the bodies of
  `quantum/STATUS.md` and `security/IDEAL_STATUS.md` below their top notes; `quantum/HANDOFF.md`;
  `security/Ideal/HANDOFF.md`. The Lean headers were left alone so as not to invalidate the
  builds that were just checked. One line of `security/status/AUDIT-closed.md` is wrong: it says
  `Ideal.lean` does not import the headline files; it does (lines 90 and 122).
- **Proof audit.** Nobody has read the new proofs. The audits cover statements and definitions.

## Commands

```
cd quantum  && PATH=$HOME/.elan/bin:$PATH scripts/check-integration.sh
cd security && PATH=$HOME/.elan/bin:$PATH lake build
cd lean     && PATH=$HOME/.elan/bin:$PATH lake build
cd rust     && cargo test --release
cd rust     && cargo test --release --features hw-sha2
cd bench    && ./run.sh
```
