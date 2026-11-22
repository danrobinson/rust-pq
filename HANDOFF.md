# Handoff — state at 2026-11-21

Both composed theorems are finished: neither has a hypothesis left that is not about the forger.
The repository is under git from 2026-11-21 (first commit `d2a5a9b` is the whole project as it
stood then; nothing is pushed anywhere). For what the project proves overall, read `README.md`;
this file covers the two composed theorems, the Rust optimisation, the opt-in hardware backend
(its performance and its proof) and the benchmark.

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
- **Context strings (added 2026-11-21, after the audit).** The audited theorems are for the
  internal interface. `suf_ideal_pure_closed`, `euf_ideal_pure_closed` and their numeric points
  (`security/Ideal/Realize/FinalPure.lean`), with `rust_ideal_security_closed_pure`
  (`Ideal/RustFinalClosedPure.lean`), cover `slh_sign` / `slh_verify` with a context string on
  the byte-level game `pureBytesAlg`: an external forger becomes an internal one that prepends
  the two header bytes and the context (`ForgerP.toI`, freshness by `pureEncode_injective`), so
  the bound is the internal one at message length `ℓ + 257`; `qf`, `qs` unchanged. Not reviewed.
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

**Numbers** (`bench/results/run5`, criterion, 2 rounds, Apple M5 Ultra; keygen / sign 32 B /
verify 32 B / verify 1 MiB):

| | keygen | sign | verify | verify 1 MiB |
|---|---|---|---|---|
| this crate, default build | 39.9 ms | 304 ms | 316 µs | 2.67 ms |
| this crate, `hw-sha2` | 3.91 ms | 30.2 ms | 35.4 µs | 352 µs |
| RustCrypto `slh-dsa` | 8.28 ms | 62.5 ms | 63.8 µs | 364 µs |
| OpenSSL 4.1 | 7.30 ms | 55.8 ms | 58.6 µs | 405 µs |

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
- `scripts/check.sh` runs the tests in both builds, both re-extractions, `lean/`, `spectest`,
  `security/`, `lean-hw/`, the instruction-model test, and the placeholder search;
  `quantum/scripts/check-integration.sh` is separate.

**The `hw-sha2` build is proved too** (third round, 2026-11-21), relative to a model of the
processor instructions. Module `hw` of `rust/src/sha256.rs` was rewritten in two layers:
- `hw::arm`: eighteen wrappers, each one to three intrinsics; the only code Aeneas does not
  translate. The three that touch a caller's memory (`load_words`, `load_be`, `store_be`) check
  their bounds with an overflow-free `assert!`; `store_words` writes its own array and needs
  none. The module's other two `unsafe` blocks are in translated code: the calls in
  `hw::compress` and `hw::chain_blocks` that enter the kernel after `available()`.
- Everything else in safe Rust in the Aeneas subset: `compress_block`, and the chain kernel
  (`Slot`, `First`, `Lanes`, `chain_all`, `enter`, `leave`, `run`, `period`, `tick`, `lane_tick`,
  `lane_step`). The staggered schedule that used to be macro-generated is now const-generic
  functions (`lane_step::<L, J, LANE>`), so the translation has one definition of a lane step
  and 60 calls per period. The functions are `inline(always)` where the target has the
  instructions unconditionally and `target_feature` + `inline` elsewhere (macro `kernel!`);
  both variants measure the same.
- `sha256::compress` and `hash::chain_blocks` now call `compress_portable` /
  `chain_blocks_portable` after the cfg'd hand-off, so the portable code is a named function in
  both builds.

`lean-hw/` is a second Lake package for the crate built with the feature:
- `scripts/extract-hw.sh`: Charon with `--features hw-sha2` and `--opaque
  'slhdsa::sha256::hw::arm'`, then Aeneas into `lean-hw/Slhdsa/{Types,Funs}.lean`. Aeneas lists
  what it left out as axioms in two template files; the script fails unless each has a
  definition in `TypesExternal.lean` / `FunsExternal.lean`, then deletes the templates.
- `lean-hw/Arm.lean`: the instruction model (core Lean only), transcribed from the Arm ARM
  pseudocode. `haveSha2` is an opaque Boolean; everything is proved for both values.
- `lean-hw/Slhdsa/FunsExternal.lean`: the eighteen wrappers defined over `Arm.lean`. **These two
  files are the trusted addition.**
- `lean-hw/Slhdsa/Proofs/`: symbolic links to `lean/Slhdsa/Proofs/*.lean` for every file that
  does not depend on the build (and `Theorems.lean` likewise), plus:
  - `CompressTop.lean`, `ChainTop.lean`: `compress_spec`, `chain_blocks_spec` with the default
    build's statements, by cases on the hand-off;
  - `Hw/Model.lean` (`kstep`, `kcompress`), `Hw/Rounds.lean` (`sha256h_rounds`, `su_eq`,
    `kcompress_eq`: sixteen kernel steps are `Spec.SHA256.compress`), `Hw/Compress.lean`
    (`hw_compress_block_spec`);
  - `Hw/ChainModel.lean` (the words a lane rebuilds are those of the block with the new counter
    and value; one hash step is `stepBlock`), `ChainLane.lean`, `ChainRun.lean` (`run_spec`: the
    staggered periods give each lane exactly `steps` hash steps), `ChainLoop.lean` (`enter`,
    `leave`, the cache invariant `FirstOk`, the minimum and compaction loops), `ChainMain.lean`,
    `ChainAll.lean` (the slot invariant `MInv`), `Chain.lean` (`hw_chain_all_spec`).
  - `Hw/Wrappers.lean`: each wrapper's definition equals a bounds check around a plain
    function; `lean-hw/ArmTest.lean` runs those plain functions (Aeneas's `Result` is
    coinductive and cannot be executed).
- To make the sharing possible `lean/Slhdsa/Proofs/Sha256.lean` was split: `Sha256Core.lean`
  (through `compress_portable_spec`), `CompressTop.lean`, `Sha256.lean` (the rest); and
  `chain_blocks_spec` moved to `ChainTop.lean`.
- Result: `lake build` in `lean-hw` prints the same six theorems on the three standard axioms.

`security-hw/` attaches the security theorems to the `hw-sha2` build. It is a Lake package with
no source of its own: `Spec`, `Link`, `E2E`, `Reduction` and `Ideal` are compiled in place from
`../lean` and `../security`, and `Slhdsa` and `Arm` from `../lean-hw`. Only `E2E/*` and
`Ideal/Rust*.lean` depend on the translation, and they compile unchanged. Checked there, all on
the three standard axioms: `E2E.end_to_end`, `E2E.standard_model_security_split`,
`E2E.pure_standard_model_security_split`, `E2E.bytes_end_to_end`, `E2E.pure_bytes_end_to_end`,
`E2E.rust_security`, `E2E.rust_pure_security`, `Ideal.rust_ideal_security_closed`, and
`Ideal.rust_ideal_security_closed_pure` (built there; its axioms were printed in `security/`). It compiles
its own copies of the security libraries; a build from a clean state takes about four minutes
(checked in a scratch copy). The quantum theorems are about the scheme at the byte
interface and do not mention the Rust code; `E2E.pure_bytes_end_to_end` is what connects
either build to them.

What the `hw-sha2` theorems rest on beyond the default build's:
- The model against the processor: `vectors/arm-wrappers.txt` holds 1,745 cases recorded from
  an Apple M5 by the unit test `sha256::hw::vectors` (`ARM_VECTORS_WRITE=1` rewrites it; without
  it the test checks the processor against the file); `ArmTest.lean` checks the model against
  the file: 0 mismatches, and a deliberately wrong model gives 320.
- That each wrapper's intrinsics are the instructions named, with the operand order in its
  definition; and rustc/LLVM.
- Not covered: other AArch64 processors (the model is architectural, but only this CPU was
  compared), and the behaviour when `std`'s feature detection is wrong.

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

## Interface module, checked signer and wiping (2026-11-21, later the same day)

Decisions by the owner, in order: make the RustCrypto-style crate the main interface and verify
what can be verified of it; then, on learning that neither RustCrypto nor OpenSSL has the fault
check, **make the check opt-in** so that default signing does the same work as RustCrypto's.

- **`rust/src/api.rs`** (translated, proved): `keygen(seeds, &mut sk, &mut pk)`, `public_key`,
  `sign`, `sign_deterministic`, `sign_checked`, `sign_deterministic_checked`, `verify`. Nothing
  returns a secret by value.
- **Checked signer** (`slh::slh_sign_internal_checked`, `slh_sign_checked`, `ht::ht_sign_checked`,
  `fors::fors_pk_gen`): the FORS public key and every XMSS root are computed twice, as a verifier
  would from the signature and as key generation would from the seed (the top one is `PK.root`);
  each layer signs one copy and recomputes with the other. Measured 56.5 ms against 30.2 ms
  (`hw-sha2`), 570 ms against 304 ms (portable): 1.87×. Reason it exists: a fault in one tree
  yields a wrong root that the next layer signs correctly, so the faulty signature verifies and
  a check of the finished signature (or of the top root alone) cannot see it. RustCrypto
  0.2.0-rc.5 (source read) and OpenSSL (its reply to the SLasH-DSA authors, and a sign/keygen
  time ratio of 7.6 like every unprotected signer) do not guard against this.
- **`hash::prf_msg`** was rewritten so that HMAC's key blocks live on the stack; nothing derived
  from the secret seed is written to the heap any more. `sha256::hmac_sha256` remains, unused by
  the crate.
- **Proofs** (`lean/Slhdsa/ApiTheorems.lean`, 29 statements, both packages, standard axioms):
  the interface functions against FIPS 205; the checked signer returns the standard's signature
  when it returns one, what it returns always verifies, and it always returns one for a
  well-formed key (`Spec.KeyOk`); and completeness, which the repository lacked: for a key from
  key generation, sign then verify gives `true` (`Spec/Correctness.lean`: `wots_correct`,
  `xmss_correct`, `fors_correct`). `prf_msg_spec` was re-proved with its statement unchanged.
  Nothing is proved about faults.
- **`compat/`**: default signing is the plain signer (86 same-source results equal RustCrypto's);
  `try_sign_checked` is the opt-in. The signing key's secret is in a `Box` (a moved key used to
  leave a copy of itself on the stack; the leftover test found it). After each key generation
  and signature the adapter overwrites 64 KiB of stack (`src/scrub.rs`); the verified functions
  that handle the seed are `#[inline(never)]` so their frames lie below the adapter's.
  `tests/wipe.rs` (signer run on a stack the test owns, then searched for 208 forms of the
  secrets) and `tests/heap.rs` (allocator that searches every freed block) pass, and each fails
  when the scrub or the key wipe is removed. Measured stack use of keygen plus checked signing:
  about 15 KiB. Not covered: registers, unoptimised builds, compiler-made copies.
- **Benchmark**: entry `verified-api` added (the adapter); `bench/variants/current` re-synced.
  **Not rerun yet**: the numbers in `bench/RESULTS.md` predate this round.

## Constant time proved for the default build (`lean/Ct`, 2026-11-21)

`lean/CT_STATUS.md` is the reference. In short: `lean/Ct/` instruments the verified translation's
own text (branch outcomes, access indices and lengths, ranges, copy lengths, comparison prefix
lengths, division operands), proves that erasing the trace gives the verified functions (190
theorems), and proves in `Ct/Theorems.lean` (16 statements, standard axioms): key generation's
trace is the same for all seeds; every signer's trace on a run that returns a signature equals
that of a simulator given only (public key, message, context, signature); verification has only
public inputs. No functional hypothesis was assumed beyond the message-length bound. Checked by
rebuilding (`lake build Ct`, 3,701 jobs; 221 definitions pass the checker).
- A research report on the method and its limits is in `reports/Constant time proofs for SLH
  DSA.md`; the simulator form of the signing theorem comes from it.
- **The `hw-sha2` build is covered too** (`lean-hw/Ct`, same day): the same 16 statements over
  that build's translation (261 definitions pass the checker, 226 erasure theorems). Shared by
  link with `lean/Ct` except the instrumented copy, `CompressTop.lean`, `ChainTop.lean`,
  `Hw/Lanes.lean`, `Hw/Chain.lean` and the trusted wrapper model `ModelBuild.lean` (memory
  wrappers record their range; register-only instructions record nothing, an assumption about
  the processor that needs Arm's data-independent-timing mode). To share the callers, the
  `chain_blocks` lemma now requires the two runs' blocks to agree on their first 16 bytes
  (`Ct/Heads.lean`), which is what the kernel's cache of the first rounds compares; every caller
  proves it from public addresses. Changes to meaning-bearing shared files: `Do.lean` accepts one
  form of `match` (on an `Option`, recorded as a branch on `isSome`), needed by the hardware
  `compress`; `Check.lean` accepts the build's wrapper list. `Model.lean`, the simulators and
  `Theorems.lean` did not change. `scripts/ct-gen.sh hw` generates the hardware copy.
- Not done: anything below the source (compiler, processor timing mode, speculation, power).
  `rust/ct-evidence` results are still those of 2026-11-20.
- Observation, not a defect: when a checked signer returns nothing after a failed recomputation,
  its trace shows the common-prefix length of the two roots.

## Adapter for RustCrypto's interface (`compat/`, 2026-11-21)

`compat/` (package `slhdsa-compat`, library name `slh_dsa`) gives the verified crate the
public interface of RustCrypto `slh-dsa` 0.2.0-rc.5 for `Sha2_128s`: the three types, the
`signature` 3.0 traits, byte conversions, PKCS#8 and SubjectPublicKeyInfo. It is glue and
is not verified. It adds `SigningKey::generate` and `try_sign_hedged` (operating-system
randomness through `getrandom`), wipes the signing key on drop, and keeps the secret out of
`Debug`. `tests/dropin.rs` compiles one source text against both crates and compares 86
results; `tests/extras.rs` covers the additions and random inputs. Each of four deliberate
breakages (no wipe, secret in `Debug`, wrong default randomiser, comparison skipping a
byte) made the matching test fail. Limits: one parameter set; needs `std`; the verified
crate itself still wipes nothing. The interface and the encoding glue follow RustCrypto's
crate (Apache-2.0 OR MIT), credited in `compat/README.md` with both licence texts.
(Superseded in part by the section above: the adapter now calls `slhdsa::api`, keeps the secret
in a `Box`, and scrubs the stack.)

## A second processor (`scripts/check-arm.sh`, 2026-11-21)

The instruction model has been compared with one processor (Apple M5). `scripts/check-arm.sh`
replays `vectors/arm-wrappers.txt` on whatever AArch64 machine it runs on, prints the
processor's identity, and runs the crate's and the adapter's tests on the hardware backend;
it needs only Rust. It has been run on the M5 only. On Linux the crate takes the
runtime-detection path (`target_feature = "sha2"` is not static there), which the Mac never
compiles by default; that path was built and tested here with
`RUSTFLAGS="-C target-feature=-sha2,-sha3"`: all tests pass at the same speed.

## Independent review of the trusted statements (2026-11-21)

`reports/Trusted statements review.md`: a fresh reviewer compared `lean-hw/Arm.lean` with Arm's
pseudocode (from a mirror of Arm's export and the Sail translation; Arm's own site did not
render), the eighteen wrapper definitions with the Rust, and read the context-string ideal-model
statements. No definition or statement was found wrong. What it did find, and what was done:
- The documentation called `hw::arm` the crate's only `unsafe`; there are two more blocks, at the
  guarded entries to the kernel. Corrected in README, this file and the Rust comments.
- The model did not make an instruction fail on a CPU without it, so the theorems were symmetric
  in the feature test and would still have held with the test inverted. **Repaired the same
  day:** the seventeen wrappers other than `available` are now `fail .undef` when
  `Arm.haveSha2 = false`; `Proofs/Hw/*` carry the hypothesis `Arm.haveSha2 = true`, which the two
  top proofs obtain from the code's own `available()` test; `Proofs/Hw/Guard.lean` proves that
  both kernels fail without the feature (`compress_block_undef`, `chain_all_undef`). No headline
  statement changed. `ArmTest.lean` now calls the very functions the `wr_*` lemmas are about
  instead of re-typed copies.
- The trusted definitions number twenty-one in three files, not eighteen in two (the vector type,
  its `clone`, and an unused `panic_bounds_check`).
- The record covers 17 of the 18 wrappers on in-bounds inputs only; the failure branches rest on
  reading (the reviewer tested 11,412 out-of-bounds calls natively: all panic where the Lean
  definitions fail). `ArmTest.lean` re-types the right-hand sides of the plain functions.
- `scripts/check.sh` did not scan `security/Ideal` or `security/Reduction` for placeholders; it
  does now, and `lean/Ct` too.
- Not done by the reviewer: no Lean run, proofs not read.

## Not done

- **x86 SHA-NI backend.** `hw-sha2` does nothing on x86-64.
- **A machine-readable Arm specification.** `lean-hw/Arm.lean` is a hand transcription, tested
  against one processor. Deriving it from Arm's published ASL was not attempted.
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
cd lean-hw  && PATH=$HOME/.elan/bin:$PATH lake build
cd security-hw && PATH=$HOME/.elan/bin:$PATH lake build
cd lean-hw  && PATH=$HOME/.elan/bin:$PATH lake build Slhdsa.Proofs.Hw.Wrappers && lake env lean --run ArmTest.lean ../vectors/arm-wrappers.txt
cd rust     && cargo test --release
cd rust     && cargo test --release --features hw-sha2
cd compat   && cargo test && cargo test --features hw-sha2
./scripts/check.sh        # all of the above except quantum, with both re-extractions
cd bench    && ./run.sh
```
