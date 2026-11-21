# Handoff — state at 2026-11-21

Both composed theorems are finished: neither has a hypothesis left that is not about the forger.
**Nothing is committed** (the repo is `git init` only). For what the project proves overall, read
`README.md`; this file covers the two composed theorems, the Rust optimisation and the benchmark.

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

## Not done

- **Opt-in ARM SHA-2 backend.** An unverified prototype on top of the current structure
  (`bench/variants`, "variant D") measured 3.8× (sign 85.8 ms), still 1.37× behind RustCrypto.
  It needs `unsafe`, so the compression function would become one explicit assumption in that
  build. Awaiting a decision; nothing started in `rust/`.
- **Ideal-model theorem for the context-string interface** (first ideal caveat above).
- **`rust/ct-evidence`** was not re-run against the optimised crate. **`multi/`** (six parameter
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
cd bench    && ./run.sh
```
