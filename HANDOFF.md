# Handoff — state at 2026-11-22

The repository is the **six-set tree**: one verified Rust implementation of SLH-DSA-SHA2-{128s,
128f, 192s, 192f, 256s, 256f} with functional-correctness, constant-time and security proofs, for
the default build and the `hw-sha2` build. On 2026-11-22 it replaced the single-set tree
(SLH-DSA-SHA2-128s only), which until then was the top level while the six-set tree lived in a
subdirectory beside it. **The single-set tree is git commit `26aa3d8`**; nothing of it is lost
from history. For what is proved read `README.md`; details: `STATUS.md` (crate and functional
proofs), `lean/CT_STATUS.md` (constant time), `security/STATUS.md` (security),
`security-hw/README.md`, `quantum/STATUS.md`, `compat/README.md`, `ct-evidence/README.md`.

This file replaces the handoff of 2026-11-21 (git `26aa3d8:HANDOFF.md`), which described the
single-set tree. `quantum/HANDOFF*.md` and `security/Ideal/HANDOFF.md` are older states, kept for
the record.

## Added on 2026-11-22: the adapter's decisions in the verified crate

New `rust/src/adapter.rs` (translated in both builds; proofs `lean/Slhdsa/Proofs/Adapter.lean`,
headline list `lean/Slhdsa/AdapterTheorems.lean`, 14 `#print axioms`, checked by
`scripts/check.sh` in both builds): `append` (one part of a multi-part message), `randomizer`
(`addrnd` or `PK.seed`; wrong length fails the `assert!`), `sign_into` (context test first, then
Algorithm 22 into the caller's buffer), `sign_internal_into`, `keygen_seeds`, `signing_key_from`
(`4n` bytes, public key `Spec.skPk`), `signature_from`, `bytes_equal`; `slh::with_context` became
`pub(crate)`; `Spec.slhSignInternal_length` added to `Spec/Correctness.lean`. `compat/src` now only
forwards (to these and to `api::keygen`, `api::verify`, `slh::slh_verify_internal`,
`encoding::{public_key_from, secret_keys_equal, der_encode}`); the OID test of PKCS#8/SPKI
decoding uses the verified `bytes_equal` and produces `spki`'s error. What is left there, exactly:
`compat/README.md`, "The exact remaining unproved surface"; the survey of the rest of what a user
runs: `README.md`, "What is not proven". Not done: `&[&[u8]]` cannot be translated (nested
borrows), so the loop over the parts stays in `compat`; `Option<&[u8]>` became a flag and bytes
(the constant-time erasure step does not handle a `match` on `Option`); no relational
constant-time theorem about the adapter's functions (they pass the checker and erasure only).
Constant-time model additions: `massert` (portable `lean/Ct/ModelBuild.lean`), `instDecidableNot`,
`Bool.or` (`lean/Ct/Check.lean`). `lean-hw` also proves `sha256_hw_active_eq` and
`sha512_hw_active_eq` (the `hw_active` functions return the feature tests' answers).

## Added on 2026-11-22: verified hardware SHA-512

The SHA-512 backend (FEAT_SHA512: `SHA512H`, `SHA512H2`, `SHA512SU0`, `SHA512SU1`), until then the
separate unproved feature `hw-sha512`, is now part of `hw-sha2`, with its own run-time test
(`sha512::hw::arm::available`, `neon` + `sha3`), translated and proved, so `lean-hw` stays the one
hardware translation. Rust: `rust/src/sha512.rs`, module `hw` (ten wrappers in `hw::arm`, one to
three intrinsics each; `compress_block` and `compress` in the Aeneas subset; the store wrapper now
writes two vectors and the kernel joins the halves); feature `hw-sha512` removed from `rust/` and
`compat/`. Model: `lean-hw/Arm.lean` (`V2`, `SHA512H`, `SHA512H2`, `SHA512SU0`, `SHA512SU1`,
`ADD2`, `EXT1`, `beWord64`, `haveSha512`), `Slhdsa/{Types,Funs}External.lean` (the vector type
and the ten wrappers; 32 declarations left out of the extraction). Record: `vectors/arm-wrappers.txt`
grew from 1,745 to 2,961 cases (the first 1,745 unchanged), written by the hardware test with
`ARM_VECTORS_WRITE=1`; `ArmTest`: 2,961 cases, 0 mismatches (and 10 of 10 deliberately altered
SHA-512 results caught). Proofs: `lean-hw/Slhdsa/Proofs/Hw512/{Rounds,Wrappers,Compress,Guard}.lean`,
`lean-hw/Slhdsa/Proofs/Compress512Top.lean`; the default build's SHA-512 proof was split into
`Sha512Core.lean` / `Compress512Top.lean` / `Sha512.lean` (statements unchanged) so that only
`Compress512Top` differs between the builds. Constant time: `lean/Ct/Sha512.lean` split the same
way; `lean-hw/Ct/Compress512Top.lean`; ten new entries in `lean-hw/Ct/ModelBuild.lean`
(`lean/CT_STATUS.md`, Part 2). Timing (`compat/examples/timing.rs`, `hw-sha2`): 192s signing
67.7 ms, 256s 65.1 ms (the unproved feature: about 68 and 65 ms).

## Removed on 2026-11-22: the fault-check signer

**Removed on 2026-11-22 at the owner's request** (the fault-tolerance feature is not needed). It
exists, with everything below, up to git commit `01580f6`. Removed: the Rust functions
`sign_checked`, `sign_deterministic_checked` (`api` and per set), `slh_sign_checked`,
`slh_sign_internal_checked` (`slh` and per set), `ht_sign_checked`, `fors_pk_gen`, and their
tests; `lean/Spec/Checked.lean` (`forsPkGen`, `htCheckedStep`, `htSignChecked`,
`slhSignInternalChecked`, `slhSignChecked`; `KeyOk` and `skPk`, which the completeness statements
use, moved to the new `lean/Spec/Keys.lean`), the checked-signer theorems of
`lean/Spec/Correctness.lean` (`htSignChecked_sound`/`_complete`, `slhSignInternalChecked_sound`/
`_complete`, `slhSignChecked_sound`/`_complete`; `slh_complete_internal` and `slh_complete` are
now proved directly, through the new `htRoot_keyOk`, with unchanged statements; `fors_correct`
now states its right-hand side without `forsPkGen`), the same definitions in
`lean/Spec/Old128.lean` and their equalities in `lean/Spec/Compat128.lean` (the copy of the
single-set specification keeps the FIPS 205 functions and `KeyOk`, `skPk`), `lean/Slhdsa/Proofs/Checked.lean`, the
`api_sign_checked_spec`-style lemmas of `Proofs/{Api,Sets,Fors}.lean`, 18 theorems per set of
`ApiTheorems.lean` (`…_checked_correct`, `…_checked_verifies`, `…_checked_complete`,
`complete_internal_checked`, `complete_checked`, `api_complete_sign_checked`,
`api_complete_sign_deterministic_checked`, `spec_sign_…_checked_verifies`) and the 12 128s
restatements in `Compat128.lean` (headlines 307 → 187 per build); in `lean/Ct` the checked
simulators and theorems (`Ct.Sign.sign_internal_checked`, `slh_sign_checked`, `api_sign_checked`,
`api_sign_deterministic_checked`, `Ct.Fors.fors_pk_gen*`, four per set; the two early-exit
theorems lost their conjuncts about the checked signers) (171 → 143 per build); in `security`
`ME2E.spec_slhSignChecked_eq` and per set `api_sign_checked_eq_sign`,
`api_sign_deterministic_checked_eq`, `api_keygen_checked_eq`, `keygen_internal_checked_eq`,
`api_sign_checked_bytes`, `api_sign_deterministic_checked_bytes`, `api_checked_pure_cores`
(headlines 263 → 232, both builds); in `compat` `SigningKey::try_sign_checked` and the
`ParameterSet::sign_checked` method; the copy in `bench/variants/current` (its copy check in
`bench/run.sh` now allows removed lines); the entries of `ct-evidence` (harness, raw outputs of
those entries, template; `RESULTS.md` regenerated). Generated files were regenerated.

## The restructuring of 2026-11-22

**Moved** (with `mv`, build caches included): the six-set `rust`, `lean` (with its `.lake`),
`lean-hw`, `security-hw`, `compat` to the top level; the six-set `security` project merged into
`security/` (its `.lake` replaced the single-set build); its `scripts` and `vectors` merged into
`scripts/`, `vectors/` (the 128s vector file was identical); its `STATUS.md` is now `STATUS.md`,
its `CT_STATUS.md` `lean/CT_STATUS.md` (with the single-set `lean/CT_STATUS.md` appended as
"Part 3: the method"); `rust/ct-evidence` (the binary timing harness) to `ct-evidence/`.

**Borrowed files made real.** `lean/` and `lean-hw/` had used single-set files by symbolic link or
by compiling them in place; these are now ordinary files, unchanged:
`lean/Ct/{Arith,Attr,CheckTest,CompressTop,Do,Facts,Heads,Leak,Model,Rel,Sha256,Sha256Core,Sim}.lean`;
`lean-hw/Arm.lean` (the `Arm` library now has the default source directory), `ArmTest.lean`,
`Slhdsa/{Types,Funs}External.lean`, `Slhdsa/Proofs/CompressTop.lean`,
`Slhdsa/Proofs/Hw/{Model,Rounds,Compress,Wrappers}.lean`, `Ct/CompressTop.lean`. Every remaining
symbolic link points inside the tree (`lean-hw` into `lean`).

**Deleted** (tracked content, all in `26aa3d8`):
- the single-set `rust/` (crate and tests), `lean/`, `lean-hw/`, `security-hw/`, `compat/`;
  `opt/` (the working copy of the 2026-11-20 optimisation, including `opt/original` and the
  differential harness `opt/difftest`); the single-set `scripts/{check,ct-gen,extract,extract-hw}.sh`;
- in `security/`: `Link/{Climb,Encoding,Fors,Hypertree,Keygen,Main,Sign,SignParts,Wots,Xmss}.lean`
  and the originals of `Link/{Basic,Hash,Verify,Sha256}.lean`;
  `E2E/{Api,Bytes,External,Final,FinalSplit,Headline,HeadlineGen,Main,PureRom,PureRomBytes,Reduction}.lean`;
  `Ideal/Rust*.lean` (13 files); the single-set `lakefile.toml`, `README.md`.
- Untracked build products went with their directories (the single-set `lean/.lake`,
  `security/.lake`, `security-hw/.lake`, cargo `target/`s).

**Kept in `security/`, unmodified:** `Reduction/**` (including `Reduction/Gen`, which uses only
`Link.vp`, `Link.prims` and now compiles over the stand-ins; it was not built by the six-set
project before), `Ideal/**` except `Ideal/Rust*.lean`, `Link/Security.lean`,
`E2E/{GuardedRom,CodedRom}.lean`, `status/` (one dated correction in `R-final.md`), `scratch/`,
`REDUCTION_STATUS.md`, `IDEAL_STATUS.md` (each given a dated note at the top). The exception, as
planned: `Reduction/PrfDomainNonVacuity.lean` is now the stand-in (the original minus
`prf_128s_spec` and its `#print axioms`, 7 lines).

**Stand-ins.** `Link/{Basic,Hash,Verify,Sha256}.lean` are the six-set project's Spec-free stand-ins
at the original paths; only their module docstrings were reworded. The shim-fidelity diff was run
one last time before the originals were deleted: `PrfDomainNonVacuity` 0 added / 7 removed,
`Link/Sha256` (docstring aside) 0 added / 251 removed, both as expected; the table with all five
files is in `security/STATUS.md`, "The stand-ins". The diff step was then removed from
`security/scripts/check.sh`.

**Lake.** `security/lakefile.toml`: libraries `Spec`, `Slhdsa` (from `../lean`), `Link`,
`Reduction`, `E2E`, `Ideal` (each with its root file `Link.lean`, …, which imports every module of
the directory; the explicit module lists, which existed only to exclude single-set files, are
gone, and the six-set project's `Shim`, `LinkSecurity`, `E2ERom`, `ReductionOpen` libraries are
merged into these), `MLink`, `MReduction`, `ME2E`, `MIdeal`. **Everything is a default target**,
`Ideal` and `MIdeal` included: `lake build` from scratch took 4 min 16 s (8205 jobs) on this
machine, which did not seem too slow. `Link.lean`, `E2E.lean` were rewritten as import lists of
the kept modules; `Ideal.lean` lost its 13 imports of `Ideal/Rust*` (the duplicate
`import Ideal.RustFinalClosedTight6` mentioned in the brief was not present: every import
appeared once). `security-hw/lakefile.toml`: the same libraries from `../security`, `Slhdsa` and
`Arm` from `../lean-hw`. Package names: `security`, `security_hw`, `slhdsa`, `slhdsa_hw`. All
`packagesDir`/`path` entries point at `../.tools/…` (manifests updated accordingly; the security
manifest is identical to the single-set one).

**Scripts and generators changed.**
- `scripts/check.sh` is the one end-to-end check (the six-set one, with paths fixed; it now also
  runs the crate's tests with `--features hw-sha512` alone). `scripts/extract.sh`,
  `extract-hw.sh`: tool paths fixed (the first run of `check.sh` stopped here: `../.tools` where
  `.tools` was meant); re-extraction reproduces both translations byte for byte.
  `scripts/ct-gen.sh`: header now `GENERATED BY scripts/ct-gen.sh FROM lean/Slhdsa/Funs.lean`
  (the single-set form). `scripts/gen/*.py`: repository-relative paths; `api.py`, `enc.py` read
  their single-set templates with `git show 26aa3d8:…`; rerunning `thms.py`, `sets.py`, `api.py`,
  `enc.py`, `compat.py`, `ct_thms.py` reproduces the checked-in files except for the header lines
  that named the old paths (a fixed point).
- `security/ME2E/gen/gen.py`, `security/scripts/gen_api_rom.py`, `security/scripts/check_ideal128s.py`
  read the single-set statements with `git show 26aa3d8:…` (`SLHDSA_REPO` overrides the
  repository); `security/MReduction/gen/*.py` have repository-relative paths and are now re-run by
  `check.sh` step 0 too (`gen_sec.py` excepted: it was a scaffold for the hand-finished
  `MLink/Security.lean`, noted in the file). Regenerated outputs differ from the old ones only in
  "GENERATED by" headers and provenance comments.
- `security/scripts/check.sh`: step 0c now checks that every root file imports its whole directory
  and that `Link`, `Reduction`, `E2E`, `Ideal` import nothing of `Spec`, `Slhdsa`, `M*`, and that
  `Link/` mentions no `Spec`/`sp`/`spA`; step 1 is `lake build`; the placeholder grep covers every
  source of the eight libraries.
- `security-hw/scripts/check.sh`: paths and the library comparison updated.
- `quantum/scripts/check-integration.sh`: unchanged; it passes against the new `security/`
  without any change to an Integration file.
- `bench/`: repointed (below). `ct-evidence/`: repointed (below). `scripts/check-arm.sh`: still
  meaningful and unchanged (the record test has the same name in the six-set crate).

**Rust.** The dev-dependency on the single-set crate and the test
`cross_128s_against_original_crate` (128s byte-identical to the single-set crate; it passed at
`26aa3d8`) were removed. The record-writing mode `ARM_VECTORS_WRITE=1` of the wrapper test was
ported from the single-set crate (only comment lines and test code changed; the translations are
unchanged).

**Lean source changes.** Comments only (paths and the words "main tree"; `[multi]` markers in
`lean/Ct/{Check,Tactic}.lean` became `[six-set]`), plus the regenerated headers. No statement or
proof changed in `lean/`, `lean-hw/`, `Reduction/`, `Ideal/`, `MLink`, `MReduction`, `ME2E`,
`MIdeal`.

**New Lean file (a port).** `security/ME2E/Gen128s.lean`: the single-set
`E2E.rust_securityG`, `rust_security_linearG`, `rust_pure_securityG`,
`rust_pure_security_linearG`, `rust_security_resourcesG` and `E2E.api_pure_securityG` (forgers
over a general sampling spec, `Reduction/Gen`), for the six-set tree's 128s functions
(`ME2E.sha2_128s.*`). Statements are the single-set text under renamings of the Rust names and of
part (a)'s spelling, checked textually by `security/scripts/check_ideal128s.py`; proofs are the
same one-liners. That raises the headline count of the security checks from 257 to **263**.

**Bench.** `bench/` uses `slhdsa::sha2_128s` for the `verified` entries; `variants/` are frozen
copies of single-set code, now checked against `git show 26aa3d8:…` by `run.sh`; new
`benches/sets.rs` benchmarks the six sets against RustCrypto (checks byte-identical keys and
signatures first). The single-set results from runs 1–6 are archived in Git at `be142b7:bench/results`. Smoke run: see "Checks".

**Binary timing evidence (`ct-evidence/`).** The harness (emulator traces with Unicorn, dudect
timing, disassembly checks; `run.sh`, `scripts/disasm_check.py`, `scripts/make_results.py`,
`RESULTS.md`) was repointed at the six-set crate's 128s functions (`slhdsa::sha2_128s`, the
generic internals at `N = 16` with `params::SHA2_128S`; same inputs, layout and experiments). It
builds, and `cttrace hwcheck` passes on both builds (emulated output equal to native on every row;
SHA-256 instructions only in the `hw-sha2` build). **The recorded results are still the single-set
crate's** (2026-11-21): traces, disassembly and timing were not rerun, and the sets other than
128s are not exercised. `RESULTS.md` carries that note (added through its template; regeneration
otherwise reproduces it exactly).

## Checks

Run after the last edit, from the state described here (2026-11-22):

- `scripts/check.sh` (run after the last edit of 2026-11-22, after the three changes above): the
  crate's tests in two builds (default 87, `hw-sha2` 90), both re-extractions (32 declarations
  left to the hardware model), `lean` and `lean-hw` with their headline axiom checks (37 + 66 + 72
  + 12 + 14 theorems each, plus 13 kernel and guard theorems and 2 `hw_active` lemmas on
  `[propext, Quot.sound]`), ArmTest (2,961 cases), the spec on the sigVer vectors of the six sets,
  constant time for both builds (11 + 6 × 22 theorems each), the two security checks and the
  adapter's tests in two builds (51 and 53). Its last lines:

  ```
  security: 232 / 232 headline theorems reported CHECK PASSED
  security-hw: 232 / 232 headline theorems reported CHECK PASSED
  ...
  All checks passed.
  ```
  Not rerun after the three changes: `quantum/scripts/check-integration.sh`, `bench/run.sh`,
  `ct-evidence/run.sh` (its `cttrace hwcheck` was run: AS EXPECTED, both builds), and
  `scripts/check-arm.sh` beyond its record test. The lines below are of the earlier state.
- `quantum/scripts/check-integration.sh` (no Integration file changed):

  ```
  checked 93 modules of ../security (93 with source hash)
  all present and up to date
  ...
  348 theorems checked, 0 with non-standard axioms

  PASS: default target built, security oleans up to date, all Integration files compiled, only standard axioms.
  ```
- Smoke runs: `bench`: `cargo run --release --bin interop` (every FIPS 205 implementation agrees
  with the verified 128s functions on keys, signatures and verdicts; PQClean's round-3 SPHINCS+
  differs, as before) and `cargo bench --bench sets` (all six sets; e.g. 128s portable keygen
  40.5 ms, verify 324 µs; RustCrypto sign 62.6 ms), the `run.sh` copy check against `26aa3d8`;
  `ct-evidence`: `cttrace hwcheck`, both builds, AS EXPECTED; `scripts/check-arm.sh`: the processor
  agrees with all 1745 recorded calls; `ARM_VECTORS_WRITE=1` rewrote the record byte for byte.
- Placeholders: no `sorry`, `axiom`, `native_decide`, `bv_decide` (grepped by the checks above);
  every `#print axioms` of the headlines reports `[propext, Classical.choice, Quot.sound]`.

## What the single-set tree had that this tree does not

Nothing below is silently dropped; all of it is in git commit `26aa3d8`.

- **Binary-level timing and trace evidence for the current crate.** Exists only for the
  single-set crate (2026-11-21). The harness now targets this crate's 128s functions, but only
  its emulator self-check was run; the other five sets have none.
- **Rust-level secondary theorems** (single-set `security/E2E/*`):
  - `E2E.api_pure_standard_model_security_split` and the `E2E/FinalSplit.lean` forms
    `standard_model_security_split`, `pure_standard_model_security_split` (the loose-cap typed
    headlines). The six-set tree has the Reduction-level split headlines at every set
    (`MReduction.slhdsa_sha2_<set>_{,pure_}{suf,euf}_cma_final_split`) but not their Rust-level
    restatement; superseded by `ME2E.sha2_<set>.{rust,api}_pure_security` (tight caps). Not ported:
    it needs the typed (`EndToEnd`-style) Rust attachment of `E2E/Main.lean`.
  - `E2E.api_pure_securityG` and `E2E/HeadlineGen.lean`: **ported** for 128s
    (`ME2E.sha2_128s.*G`, above). Not for the other sets (`Reduction/Gen` is stated at `Link.vp`).
  - `E2E/Main.lean`: the typed-value end-to-end forms `EndToEnd`, `end_to_end`,
    `end_to_end_verify`, `rust_verify_internal'`, `rust_sign_internal'` and helpers (`nodeOfBytes`,
    `nd_node`, …). The six-set counterparts are the byte-level and typed `PureEndToEnd`,
    `pure_end_to_end`, `rust_keygen`, `rust_sign`, `rust_verify` of `ME2E.sha2_<set>`; the internal
    typed `EndToEnd` with its ROM instantiation has no counterpart.
  - `E2E/Bytes.lean`: `bytes_standard_model_security`, `pure_bytes_standard_model_security`,
    `…_resources` (earlier-stage bounds; superseded by `rust_security`, `rust_pure_security`,
    `…_resources`); `E2E/Final.lean` (`standard_model_security_final`, one cross-arity TCR term);
    `E2E/Reduction.lean` (phase-1 `standard_model_security`, superseded and with a vacuous PRF
    game); `E2E/Headline.lean`, `External.lean`, `Api.lean` (all other declarations),
    `PureRom.lean`, `PureRomBytes.lean`: ported to all six sets (`ME2E`).
- **The single-set link `Spec` = VCVio** (`security/Link/*`): replaced by `MLink`, generic in the
  set (`MLink.keygen_eq`, `sign_eq`, `verify_eq`, `sha256_eq`, …). Not restated:
  `Link.romScheme_verify_eq_spec` (`Link/Main.lean`; follows from `MLink.romScheme_verify_eq` and
  `verify_eq_typed`), the 35 SHA-256 facts of the original `Link/Sha256.lean` at the single-set
  `Spec` (their six-set counterparts are in `MLink/Sha256.lean`), `Reduction.prf_128s_spec`
  (replaced by `MReduction.prf_spec S`), `stepPRFC_128s`, `skPrf_broken_128s_half`, per-set copies
  of single-adversary numeral lemmas (their content is in `final_resources_final_<set>`).
- **Single-set ideal-model Rust corollaries** (`security/Ideal/Rust*.lean`):
  `Ideal.rust_ideal_security`, `rust_ideal_security_final`, `rust_ideal_security_closed`,
  `rust_ideal_security_closed_pure`, `api_ideal_security_closed_pure`, `pureBytesAlg_realCF`, and
  the `…_tight` … `…_tight7` forms. Only the `…_tight8` forms (the strongest) are attached to the
  six-set functions (`MIdeal.sha2_128s.*_tight8`, with `pure_bytes_end_to_end` and
  `pureBytesAlg_realCF`); the bounds of all the earlier stages are still proved in `Ideal`.
- **The cross-test against the single-set crate** (`cross_128s_against_original_crate`): removed
  with that crate; it passed at `26aa3d8`. The equality of the 128s statements is kept in Lean
  (`lean/Slhdsa/Compat128.lean`, `security/MReduction/Check128s.lean`, the generators' textual
  checks).
- **The single-set specification** `lean/Spec/SlhDsa.lean` (128s): kept verbatim as
  `lean/Spec/Old128.lean` (namespace `Spec128`) and proved equal to the six-set spec at 128s.
- **`opt/`** (the optimisation's working copy and `opt/original`, the pre-optimisation crate and
  proofs) and **`opt/difftest`** (a differential test and timing harness, old against new crate):
  deleted. The pre-optimisation crate survives as `bench/variants/base` (benchmarked as
  `verified-before`).
- **The single-set adapter** (`compat/`, 128s, 86-result drop-in comparison): replaced by the
  six-set adapter (516 results; wipe and heap tests per set).
- **Bench comparisons with OpenSSL, `fips205`, slhdsa-c, PQClean**: only for the single-set crate
  (results kept, dated); `bench/run.sh` would redo them for this crate's 128s functions (not run:
  about 40 minutes).
- **A Rust-level statement for the quantum result:** none, in either tree. The quantum theorem is
  about the scheme `Reduction.pureBytesAlg Link.vp (randPrims ω.toRand) (codecR …)` averaged over
  uniformly random four-component hash tuples `ω` on length-capped domains (constant outside the
  caps); SLH-DSA-SHA2-128s parameters, external pure byte interface. The Rust 128s functions
  compute the cores of the same generic definition at the real SHA-2 primitives
  (`MIdeal.sha2_128s.pure_bytes_end_to_end`), but the real functions are not of the form
  `ω.toRand` (they are not constant outside the caps), and the single-set tree's informal
  "equivalence with unbounded random oracles" is not formalised, so no analogue of the `MIdeal`
  conjunct 2 (the game's scheme at the real primitive is the Rust scheme) can be stated. None was
  added.

## Caveats of the closed results

Ideal compression function (`Ideal`, `MIdeal`, SLH-DSA-SHA2-128s):
- **Random function, not SHA-256's compression.** No Davies–Meyer / ideal-cipher model; the
  security conjunct averages over random tables, the Rust conjuncts are about the real
  compression function: they share the scheme, not a security claim.
- **Message length.** Forgeries on messages longer than `ℓ` are excluded; the numeric points take
  `ℓ ≤ 2^26` bytes (`ℓ + 257` at the context-string interface).
- **ITSR leg** vacuous once **`qf + 4·qs + 2`** reaches about 2^70 (the argument of `reuseSum` in
  `epsItsrF qf (2·qs) …` is `qf + 2·qs + 2·(qs + 1)`; the handoff of 2026-11-21 said `qf + 2·qs`,
  which was wrong). A proof-technique limit, not an attack.
- **Weak at many signatures.** About 2^-39 at 2^64 signatures (tight8); reaching the
  generic-attack level needs a different proof (`security/status/TIGHT.md`).

Quantum random oracle (`quantum/`, SLH-DSA-SHA2-128s scheme only):
- the reduction's own hashing is charged as quantum queries (the bound exceeds 1 for
  `qs ≥ 2^28` at any `q`, and for `q ≥ 2^53` at `qs = 2^20`; evaluated outside Lean);
- caps: outside them the hash functions are constants; that the experiment stays inside is the
  hypothesis `hcap`;
- additive oracle, not XOR; independence of the four components idealises SHA-2 domain separation;
  ITSR keeps the reprogramming loss `2q'√(qs/2^128)`, which dominates.

Both: FIPS 205 conformance of the shared scheme code and the Aeneas extraction were not
re-audited; the audits (`quantum/AUDIT-closed.md`, `security/status/AUDIT-closed.md`, of the
single-set statements) checked statements and definitions, not proofs.

## Technical points worth knowing before touching the proofs

- Equalities between programs over different worlds or bundles are closed by kernel-only `rfl`
  tactics (`krfl`/`kexact`, `qm_kernel_rfl`, `qtcr_kernel_rfl`). The elaborator's own `rfl` times
  out or overflows on these.
- Statements whose type mentions an `IsQueryBoundP` of a closed key-structure program can make
  `whnf` evaluate the structure walk; the fixes used are `irreducible` wrappers and stating lemmas
  over a variable program with an equation hypothesis.
- Changing a line count in `rust/src` before translated items changes the generated Lean (source
  positions) and forces a rebuild of all of `lean/`; comment edits that keep line counts do not.
- `lean-hw` and `security-hw` compile files of `lean/` and `security/` in place; editing a shared
  file rebuilds three packages.

## Trusted pieces of the `hw-sha2` build

`lean-hw/Arm.lean` and `lean-hw/Slhdsa/{Types,Funs}External.lean` (thirty-two definitions since
2026-11-22: the SHA-256 part's twenty-one and the SHA-512 vector type and ten wrappers): a
hand transcription of Arm's pseudocode, tested against one processor (Apple M5) through
`vectors/arm-wrappers.txt` (2,961 cases; `rust` checks the processor against it, `ArmTest.lean`
the model); the SHA-256 part reviewed in `reports/Trusted statements review.md` (single-set
tree, same wrappers); the SHA-512 part (2026-11-22) not reviewed by anyone else.
Not covered: other AArch64 processors, a CPU without the instructions running the feature, and
`std`'s feature detection being wrong. The constant-time proof of the build additionally assumes
that the register-only vector, SHA-256 and SHA-512 instructions take operand-independent time
(Arm's `PSTATE.DIT`).

## In progress, unfinished: a tighter ideal-compression bound (`security/Ideal/Direct`)

Started 2026-11-22; 45 files, about 14,400 lines, all compiled and imported from
`security/Ideal.lean`; no `sorry`. **It proves no new unconditional bound.** The proved closed
bound for SLH-DSA-SHA2-128s is still tight8's (2^-63, 2^-59, 2^-39 at 2^20, 2^40, 2^64
signatures).

The route: reduce the compression-function game to VCVio's random-oracle theorem
(`strongUnforgeableAdvantage_romScheme_le_securityBound`) through a simulator that answers the
forger's compression queries from the oracles. `Ideal/Direct/Headline.lean` collects sixteen
bounds for the same game objects as tight8 (2^-67, 2^-63, about 2^-62.4 at the three points),
each **conditional** on the hypothesis `DeferCoreGhostSufH` / `DeferCoreGhostEufH`. Those follow,
by proved implications (`CoupleDomP.lean`, `deferCoreGhost*H_of_bad`), from the one statement
that is left: `BadJS` / `BadJE` (`CoupleJ.lean:222`, `:234`), the bound on the bad event of the
coupling. Its right-hand side, `epsHalf + qs/2^128`, is an allocation supported by a paper
derivation, not a machine-checked value; if the true value is larger the numbers change.

`security/status/DIRECT.md` is the full record: the plan and what was wrong in it (§§1–8), the
change of route (§§9–10), and in §14 what is proved, the exact remaining statements and a
cold-start plan (estimate 1.8–2.9k lines). The early files (`Toy*`, `TwoColour`, `DagSwap`,
`Extract*`, `Bridge`, `Tagged`, `Parse`) belong to the abandoned direct route; some are reused,
the rest are kept as proved lemmas with no use yet.

## Not done

- **The tighter ideal-compression bound** (section above): one statement short.

- **SHAKE parameter sets**, pre-hash variants.
- **Ideal-compression bound** for the sets other than 128s (needs the counting re-instantiated
  and, at n = 24, 32, an ideal SHA-512 compression function).
- **Binary-level evidence** for this crate (above).
- **x86 SHA-NI backend.** `hw-sha2` does nothing on x86-64.
- **A machine-readable Arm specification** for the instruction model.
- **Proof audit.** Nobody has read the proofs; the audits cover statements and definitions.
- **Stale text** in the kept single-set documents (`security/IDEAL_STATUS.md` below its notes,
  `REDUCTION_STATUS.md`, `security/status/*`, `quantum/STATUS.md` body, `quantum/HANDOFF*.md`,
  `security/Ideal/HANDOFF.md`): they describe their state at the time, with paths of the
  single-set tree (`26aa3d8`).

## Commands

```
./scripts/check.sh                       # everything below except quantum, with both re-extractions
./scripts/check.sh full                  # also the slow spec keygen/signing vectors
cd quantum     && scripts/check-integration.sh
cd security    && lake build && scripts/check.sh
cd security-hw && lake build && scripts/check.sh
cd lean        && lake build Slhdsa Spec Ct spectest
cd lean-hw     && lake build && lake build Ct
cd lean-hw     && lake build Slhdsa.Proofs.Hw.Wrappers Slhdsa.Proofs.Hw512.Wrappers && lake env lean --run ArmTest.lean ../vectors/arm-wrappers.txt
cd rust        && cargo test --release [--features hw-sha2]
cd compat      && cargo test --release [--features hw-sha2]
cd bench       && ./run.sh               # about 40 minutes; cargo bench --bench sets for the six sets
cd ct-evidence && ./run.sh setup         # see its README
./scripts/check-arm.sh                   # on another AArch64 machine
```
