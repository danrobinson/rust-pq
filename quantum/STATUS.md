# Post-quantum security workstream — status (end of phase 4 consolidation)

> **Update (2026-11-22): `../security` is now the six-set tree's security project.** The
> `Reduction`, `Reduction.Open` and `Ideal.Transport` modules these Integration files import are the
> same sources as before, but `Link.Basic`, `Link.Hash`, `Link.Verify`, `Link.Sha256` are now the
> Spec-free stand-ins (the single-set `Spec` = VCVio proofs were removed with the single-set tree,
> git commit `26aa3d8`; `../security/STATUS.md`, "The stand-ins"). No Integration file needed a
> change: `scripts/check-integration.sh` passes against the new `../security` (93 `security`
> modules checked, 46 Integration files, 348 theorems, standard axioms only; the last run is
> recorded in `../HANDOFF.md`, "Checks"). The quantum theorems are about SLH-DSA-SHA2-128s at
> VCVio's level (`Reduction.pureBytesAlg Link.vp (randPrims ω) …` averaged over capped random
> functions `ω`); there is no statement about the Rust functions (`../README.md`, "Quantum
> adversaries").

> **Update (2026-11-21): the composed QROM theorem is finished. Read this first; everything
> below it describes an earlier, conditional state.**
> `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc_closed`
> (`Integration/SlhDsaComposedClosed.lean:64`, `:93`) has hypotheses on the forger only (`hq`,
> `hqs`, `hcap`) and `35 ≤ c.tl`; `hInd` and all eleven bridge statements are proved. Numeric:
> `≤ 2^-22` at `q = 2^40`, `qs = 2^20` (`SlhDsaComposedClosedNum.lean`). `scripts/check-integration.sh`
> passes (46 Integration files, 348 theorems, standard axioms). State, file map, caveats and the
> statement-level audit: `../HANDOFF.md`, `AUDIT-closed.md`, `HANDOFF-{qprf,qmach,qtcr,qfors,qwots}.md`.


> **Update (handoff).** See `quantum/HANDOFF.md` for the full state and the ordered remaining
> chain. Since the note below: `PQ/Interactive/QromBridgeCall.lean` (`run₂_callBasis_branch`:
> branch law of a computational-basis call on a general register against the additive oracle —
> PROVED) and `PQ/Interactive/QromBridgeEval.lean` (`PUE`: port-uniform machines with
> classical-evaluation nodes and weighted interface queries; closure lemmas, `EvalCost`,
> `PUE.close` — PROVED; `PUE.compileQ`, `PUE.exists_prog`, the hybrid model — NOT done). Both in
> the default target. Headlines and `BridgesRest` unchanged; no field discharged.

> **Update (bridge, stage report).** The composed QROM theorem is STILL CONDITIONAL. Proved since
> the last note (all `[propext, Classical.choice, Quot.sound]`, default target green,
> `scripts/check-integration.sh` PASS):
> * **Encoding fixed** (`Integration/SlhDsaBridgePrf.lean`): `EncX c` (tagged union of the four
>   bounded hash domains), `EncY = Bytes n × Bytes m` with bytewise addition mod 256
>   (`bytesGroup`), `encΩ ω : EncX c → EncY`; one port call evaluates one component
>   (`encΩ_thash/_hmsg/_prf/_prfMsg`), `encΩ_withPrf_local`.
> * **Bridge infrastructure** (`PQ/Interactive/QromBridgeUnif.lean`, in the default target):
>   port-uniform machine families `PU Mach q`; closure under `bind`, `liftQ`, `map`, `wrap`,
>   `wrap0`, and `close` with ANY stateful probabilistic implementation (`PU.close`);
>   `PU.compileQ`; `PU.exists_prog(_qprob)`: one VCVio query program for all port functions,
>   Part-2 `qprob` = Part-1 Born weight, uniform-sampling nodes as uniform-coin instruments.
>   This covers uniform-sampling nodes and probabilistic/lazy challengers for ONE-port,
>   ONE-phase games.
> * **PRF in the Part-1 model** (`PQ/QROM/ExactPrfStruct.lean`,
>   `PQ/Interactive/QromBridgePrfStruct.lean`): `prfStruct_real_le_ideal_add` (tight PRF bound
>   for an oracle built locally from the keyed function), `lazy_eq_avg` (VCVio's lazy random
>   function around any Part-1 machine = average over eager tables through an injective key
>   map), `prf_PU_real_le_ideal_add`: for port-uniform machines,
>   `E qPrfRealPr ≤ E qPrfIdealPr + 8q²/|K|`.
> * **`PRF` term** (`prf_term_suf`, `prf_term_euf`): the `TermBounds.prf` inequality with count
>   `q` (reduction's hashing not charged), for every port forger over `encΩ`, UNDER ONE NAMED
>   HYPOTHESIS `hInd : ∀ ω g H, prfMachSuf (ω.withPrf g) H = prfMachSuf ω H`.
> * **Headline** `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc`
>   (`Integration/SlhDsaComposedEnc.lean`): encoding fixed; hypotheses `hq`, `hqs`, `hcap`,
>   `hInd`, and `BridgesRest` (the eleven other bridge fields); bound
>   `composedBoundFinal q qs r.noPrf`.
>
> **Added after the stage report (coordinator: transport is built elsewhere, under
> `security/Ideal/Transport/`; `hInd` stays a named hypothesis here):**
> * `PQ/QROM/HybridPullback.lean` (default target): `HybridModel.pullback` — a `q`-query hybrid
>   model whose real oracle is `φ H`, built locally from `H` through an embedding of domains, is
>   a hybrid model for `H`. This is the structured-oracle form of every leaf-level Part-2 bound
>   stated on `HybridModel` (in particular `spr_embedded_obs_weighted_le`, the core of the TCR
>   family), so no ancilla simulation is needed for the FORGER's port queries.
> * `Integration/SlhDsaOpenCounts.lean`: `openCounts128s_sound` — the fields of `openCounts128s`
>   are exactly the hash-query bounds of `Reduction.Open.final_resources_final_open_128s`
>   (classical open programs at `Link.prims`); `security/Reduction/Open/Bundle` is now imported.
> * `_qrom_enc` headlines take the explicit hypothesis `35 ≤ c.tl` (not used by the proof).
> * NOT done, and why: stage 2(b) proper (a classical hash evaluation inside the quantum
>   reduction machine as an oracle call of the Part-2 program) needs (i) a port-uniformity
>   notion with classical-evaluation nodes and the branch law of VCVio's `QComp.callBasis`
>   against `additiveOracleRuntime` on a general register (only the trivial-register /
>   emulated-oracle forms exist: `fid_run_query`, `EmulatedOracle.branch_run₂_callBasis`), and
>   (ii) the quantum reduction machines in open form (their hashing is `pure (PublicHash.impl
>   prims q)` inside `liftQ` code). Stage 2(c) and every Thash/H_msg field are not started.
>
> **Blocked / not done:**
> * `hInd` (PRF-independence of the reduction machine) is NOT `rfl`: `PublicKeyCore core`,
>   `SignatureCore core`, `ForsTreeSigCore`, `XmssSigCore` are structures indexed by the whole
>   `core`, which contains `PRF` and `PRF_msg`. Needed: a transport of signing, verification,
>   the codecs and the logging harness along `core ↦ {core with PRF := g}` (not built in
>   `security/` either, `status/OPEN.md` §6). The same obstacle applies to the `msg` term.
> * Stage 2(b) (a classical hash evaluation of the reduction = a port call) and 2(c) (two ports /
>   two phases) are not started; `openCounts128s` is still hand-copied numerals. No field of
>   `msg`, `itsr`, `dspr`, `tcrFv`, `tcr*`, `ud`, `pre`, `tcrT` is discharged.
> * Limitation unchanged: at `r = openCounts128s qs` the reduction's classical hashing is charged
>   quadratically (bound ≈ 2^-22.9 at `q = 2^40, qs = 2^20`; vacuous for `qs ≳ 2^28` (ITSR) /
>   `2^39` (other terms) and for `q = 2^64`).
>
> **Earlier in this round** (`Integration/SlhDsaComposedFinal.lean`): `…_qrom_of_bridges`,
> `…_qrom_closed`: every numerical term derived from its Part-2 theorem, hypotheses `Bridges`
> (twelve simulation statements over `MixLE`/`MixPair` and the value classes), tight DSPR
> `168q'²/2^128`, UD `8q'²/2^128`, `composedBoundFinal_open_le`. `epsDspr` in
> `Integration/SlhDsaComposed.lean` switched to the tight shape.

> **Update (coordinator, after consolidation).** Tight exact DSPR-FV is now proved and imported:
> `dspr_exact_tight`, `dspr_exact_tight_of_card`, `dspr_exact_tight_zeroPre_of_card`
> (`PQ/QROM/ExactDsprTightCore.lean`, `ExactDsprTightGame.lean`): with `2 ≤ |Y| ≤ |Msg|` and no
> quantum queries before the seed reveal, `dsprSucc − dsprSP ≤ 168·q₂²/|Y|`, independent of the
> number of targets, no named hypothesis; for general `q₁` the old `2·seedLoss Sd q₁` term remains.
> Default target rebuilt (7200 jobs) and `scripts/check-integration.sh` re-run: PASS. This
> supersedes item A.2 and the DSPR row of the bounds table below (≈ 2^-40.6 at q₂ = 2^40).
> `epsDspr` in `Integration/SlhDsaComposed.lean` still uses the old shape. Not independently audited.


Lake project `quantum/` (library `PQ`, ~33k lines; `Integration/`, ~5.5k lines), Lean 4.36.0,
depends on VCVio (`../.tools/VCVio-upstream`, commit a10530a) by path.

```
cd quantum && PATH=$HOME/.elan/bin:$PATH lake build     # default target PQ: 7208 jobs, green
cd quantum && scripts/check-integration.sh               # PQ + staleness check of security/'s oleans (no lake run
                                                         # there) + every Integration/*.lean; fails on error / sorry /
                                                         # non-standard axiom. Last solo run: PASS, 204 theorems.
```
No `sorry`/`axiom`/`native_decide`/`bv_decide`. 456 `#print axioms` lines in `PQ`, 204 in
`Integration/`, all `[propext, Classical.choice, Quot.sound]`. `PQ.lean` imports every module
under `PQ/QROM` and `PQ/Interactive`.

## A. What is conditional / open (read this first)

1. **The single composed QROM theorem is NOT established.** Strongest form:
   `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc` (`Integration/SlhDsaComposedEnc.lean`):
   port function fixed to `encΩ`; forgery probability `≤ composedBoundFinal q qs r.noPrf`.
   Unproved hypotheses: `hInd` (the `PRF` distinguisher machine does not depend on the `PRF`
   component of the world; needs a transport along `core ↦ {core with PRF := g}`), and
   `BridgesRest` — eleven simulation statements (`msg`, `itsr`, `dspr`, `tcrFv`, `tcr1`, `tcr2`,
   `tcrLen`, `tcrK`, `ud`, `pre`, `tcrT`): the `ω`-averaged Part-1 game is dominated by a
   sub-convex combination of Part-2 exact-game values for adversaries with no first-phase quantum
   query and at most `q + r.<term>` quantum queries, sizes `2^128`. Formal hypotheses on the
   forger: one port program over `encΩ` with bounds `q`, `qs`; message-length cap;
   oracle-independent `optRand`/`pkSeedDist`. Pure-bytes interface only. Loose: `r` is a free
   parameter (`openCounts128s qs` = numerals copied from `security/Reduction/Open/Bundle.lean`);
   the tweak-list cap `c.tl ≥ 35` is not a hypothesis; the Open results R1–R7 of `security/` are
   not used by any proof here. The older forms (`…_qrom_of_bridges`, `…_qrom_closed`,
   `…_qrom_conditional`) quantify over an arbitrary encoding `enc`.
2. **Tight exact DSPR-FV**: PROVED and imported (`dspr_exact_tight`, `dspr_exact_tight_of_card`,
   `dspr_exact_tight_zeroPre_of_card`, `PQ/QROM/ExactDsprTightGame.lean`):
   `Success − SPprob ≤ 168·q₂²/|Y| + 2·seedLoss Sd q₁` for `2 ≤ |Y| ≤ |Msg|`, independent of the
   number of targets. Used by the composed statements. Not independently audited.
3. **Adaptive ITSR, general regime** (hash queries interleaved with target requests): the
   reprogramming term `2q√(s/|K|)` makes it vacuous at `s = 2^64`, `|K| = 2^128` for `q ≥ 2^31`.
   No known technique (incl. Grilo–Hövelmanns–Hülsing–Majenz, ≈2^30.6 there) is informative.
4. **Bridge**: one-port, one-phase. Bridged: classical requests and the PRF game for port
   programs (`QromBridgeReq/Prf.lean`); uniform-sampling nodes and probabilistic/lazy classical
   challengers and wrappers, for port-uniform machine families (`QromBridgeUnif.lean`: `PU`,
   `PU.close`, `PU.exists_prog_qprob`); the PRF game of the Part-1 model with VCVio's lazy ideal
   oracle (`QromBridgePrfStruct.lean`). NOT bridged: the two-port seed-keyed two-phase games; a
   classical hash evaluation by the reduction machine as a port call; the reduction's machines
   at the random primitives beyond port-uniformity of the two `PRF` distinguishers
   (`pu_qbPrfWC`, `pu_qbPrfC`), whose `PRF`-independence is the open hypothesis `hInd`.
5. **Fidelity** equalities hold for classical adversaries that are coin-free or draw ONE uniform
   coin up front and query the random hash classically (adaptive coins not covered). The UD
   fidelity is for the older `ExactUd.lean` game (collection = the same function, `M' = Msg`),
   not for `ExactGenUd.lean`.
6. Not proved: a uniform `Bytes m` digest pushes forward uniformly through `splitDigest` (FORS
   cover relation is on pre-split digests); the counterexample showing the OLD ITSR hybrid's
   collision term could not be dropped is a paper argument; that the `ReductionCertificate`
   "excludes a second run / classical simulation" is prose; first-phase independence from the
   forger is proved only for `bTcrArM`/`bTcrArST`; `p_cov ≈ 2^-133.7` at 128s, `s = 2^64` is the
   auditor's evaluation, not machine-checked; no running-time model; nothing about SHA-2 itself.
7. Literature status of DSPR: a single-target quantum bound for DSPR of a random function is in
   the literature (Bernstein–Hülsing, ePrint 2019/492, per a search summary); the dependence on
   the number of targets there is unconfirmed (theorem statements not read). No novelty is
   claimed for any multi-target bound here.

### Requests to the reduction lead (R1–R7; unchanged)
`HSpec prims` := `publicHashSpec prims.core` + a `.prfmsg` query.
* R1 `bPrfOpen A`, `bPrfWOpen w A` (and behind `restrictImpl`): every `Thash`/`Hmsg`/`PRFmsg`
  evaluation and the final verification as oracle queries; equation back to `bPrf`/`bPrfW`;
  count `keygenHashes + qs·signHashes + verifyHashes`, `≤ qs` `.prfmsg` queries.
* R2 `msgOpenV`, `msgOpenWV`: lazy distinguishers with the final verification open; equation;
  count `c.lazyHashes + verifyHashes`.
* R3 second-phase open programs of `toDspr/toTcr (Lazy.bOpenPreS ·)`, `bTcrArM n`,
  `rUd/rPre/rTcrT (Lazy.bWotsS ·)` provably contain EVERY hash evaluation (incl. `wotsAnswer`).
* R4 first phases do no hashing (formal: `choose`/`pick` unchanged when only the hash functions
  change). R5 same for the wrappers. R6 one bundle `final_resources_final_open`.
* R7 second phases DEFINED as the `Lazy.tblImpl` interpretation of the open program, or the
  interpretation lemmas generic in the forger program.

## B. Part 1 — the reduction against all quantum forgers (standard model) — CLOSED

Model: `QOC W spec α := OracleComp (instrSpec W + spec) α`; Born semantics `qWeight`; all quantum
games defined by `qWeight`. `RationalBorn` removed by a limit of classical approximants
(`Approx*.lean`); no change to `security/`.

Headlines, all amplitudes, no hypothesis on the forger:
`slhdsa_{,pure_,bytes_,pure_bytes_}{euf,suf}_cma_final{,_linear}_quantum_all` (`SlhDsaAll.lean`),
at SLH-DSA-SHA2-128s (`SlhDsaAll128s.lean`), general-game right-hand sides
(`SlhDsaAllGeneral.lean`), tight caps (`SlhDsaAllTight.lean`), at `randPrims f` / uniformly over a
finite function space (`SlhDsaRandom.lean`, `SlhDsaRandomFinite.lean`).
Resources: `reduction_certificate` (`SlhDsaAllCertificate.lean`): for EVERY sampler, each
reduction machine's classicalisation is syntactically the classical reduction adversary applied
to the forger's classicalisation (headline resource fact); trace inclusions
(`SlhDsaAllResources.lean`), classical counts (`SlhDsaAllCounts.lean`).
General two-phase games (`GamesGeneral.lean`) are limits of unbounded classical games
(`ApproxGeneral.lean`); they are not "the" quantum hardness assumptions.

## C. Part 2 — QROM bounds (`PQ/QROM/`), random function, all VCVio programs

| game (exact = adaptive two-phase / interactive, as the reduction uses) | theorem | bound |
|---|---|---|
| SM-DT-TCR; indexed-family collection | `tcr_exact_le`, `gen_coll_tcr_exact_le`; `…_zeroPre` | `(√((2q₂+1)²/N) + 2q₁/√|Sd|)²`; `q₁=0`: `(2q₂+1)²/N` |
| TCR final-validity | `tcr_fv_exact_le` | same |
| SM-DT-PRE (VCVio shape, planted type `M'`) | `gen_pre_sub_exact_le`, `gen_pre_exact_le` | `(√((2q₂+1)²(1/N+1/|M'|)) + 2q₁/√|Sd|)²` |
| SM-DT-UD (VCVio shape: planted `Mp ↪ Msg`, collection on other members) | `gen_ud_exact_tight` (`ExactGenUd`) | `8(q₁+q₂)²/|Mp|` |
| SM-DT-UD, older game (collection on attacked member) | `ud_exact_tight` | `(16(q₁+q₂)²+2n)/|Msg|` |
| DSPR final-validity, `Succ − SPprob` | `dspr_exact_adv_le_of_card'` | `8q₂/√N + 8q₁/√|Sd|` (O2H) |
| PRF (classical PRF oracle, quantum access to the keyed function) | `prfExact_tight_abs_le` | `8q²/|K|` |
| adaptive ITSR, no collision term | `itsr4_adaptive_le`; weighted `itsr4_adaptive_weighted_le`; queries after the last target request `itsr4_adaptive_noloss_le`; FORS `itsr4_adaptive_fors_*` | `(√((2q+1)²p_cov) + 2q√(s/|K|))²`; no-loss: `(2q+1)²·p_cov` |
| one-shot PRF / UD / DSPR, tight | `prf_tight_program`, `ud_tight_program`, `dspr_tight_program`, `dspr_tight_adv_program_of_card_le` | `8q²/size` |

Superseded but kept: O2H forms, `ExactItsr.lean`/`ExactItsr3.lean` (collision terms), circuit-only
tight forms.

Fidelity to VCVio's definitions at a uniformly random hash (classical adversaries, ≤ one
up-front coin): TCR `fid_tcrExp_eq`; TCR-FV `fid_fv_tcrFvExp_eq`; PRE `fid_pre_genPreSubExp_eq`
(+ pre-sampling `fid_pre_presample`); PRF `fid_prf_real_eq`, `fid_prf_ideal_eq` (incl. lazy =
eager ideal oracle); UD `fid_ud_real_eq`, `fid_ud_ideal_eq` (older game); DSPR-FV
`fid_dspr_succ_eq`, `fid_dspr_sp_eq`; ITSR `fid_itsr_eq`.

"Seed hidden then revealed": `Th : Sd × Tw × Msg → Y` uniform, quantum access to all of it in
both phases; phase 1 is not a function of the seed `P` (sees it only through classical answers);
phase 2 gets `P`, phase 1's classical output and the register.

### Numbers at 128s sizes (N = |Msg| = |K| = |Sd| = 2^128), q = q₁ = q₂

| bound | q = 2^40 | q = 2^60 | q = 2^64 |
|---|---|---|---|
| exact TCR / TCR-FV (`q₁ = 0`: `(2q+1)²/2^128`) | ≈2^-44 (2^-46) | ≈2^-4 (2^-6) | vacuous |
| exact PRE | ≈2^-43.5 | ≈2^-3.5 | vacuous |
| exact PRF `8q²/2^128` | 2^-45 | 2^-5 | vacuous |
| exact UD (VCVio shape) `32q²/2^128` (×14 in the headline) | 2^-43 | 2^-3 | vacuous |
| exact DSPR-FV, O2H `16q/2^64` (`q₁=0`: `8q/2^64`) | 2^-20 (2^-21) | vacuous | vacuous |
| adaptive ITSR, s = 2^64, queries after last request (`p_cov ≈ 2^-133.7`, not checked) | ≈2^-51.7 | ≈2^-11.7 | vacuous |
| adaptive ITSR, s = 2^64, general | vacuous | vacuous | vacuous |

Uninformative at realistic `q`: exact DSPR-FV (pending item A.2) and ITSR in the general regime
at `s = 2^64`. Everything is vacuous at q = 2^64 (inherent for search).

Non-vacuity: `NonVacuity*.lean` (Deutsch; Grover N=4 vs classical incl. mixtures),
`FidelityNonVacuity.lean`, `ExactPrfNonVacuity.lean`, `Examples.lean`.

## D. Composition — the strongest justified statement
(1) Standard model, machine-checked: every quantum forger (classical signing queries) against
SLH-DSA-SHA2-128s (internal/pure/byte-level, EUF/SUF) satisfies the linear inequality with
explicit reduction machines certified syntactically; also uniformly over a finite random-function
space. (2) QROM, machine-checked: the exact games above for a random function, faithful to
VCVio's definitions for classical adversaries. (1) and (2) are NOT composed (item A.1).
