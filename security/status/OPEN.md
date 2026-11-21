# Work package OPEN — hash evaluations of the reduction adversaries as oracle queries

Spec: `../quantum/STATUS.md` §0, R1–R7. New files only, in `Reduction/Open/`, namespace `Reduction.Open`. Per-package
details (verbatim signatures): `status/OPEN-O1.md` … `OPEN-O9.md`. Common binder `hA : ∀ pk, IsQueryBoundP (A.main pk)
(fun i => i.isRight = true) qs` (≤ `qs` signing queries). No `Structural` hypothesis except in the store variant (§5).

## 0. Integration (lead)
All 19 files of `Reduction/Open/` are imported by `Reduction.lean`; `lake build Link E2E Reduction`: "Build completed
successfully (7788 jobs)". Four helper names clashed between packages and were renamed by the lead in the NEW files
only (`status/OPEN-rename.patch`, applied): `MsgV.lean` `hashEmb → hashEmbR`, `emb → embR`; `Tcr.lean` `ForgerProg →
TcrForgerProg`; `Phase1Wots.lean` `tcrPhase1 → wotsTcrPhase1` (the WOTS-TCR first-phase program; `Phase1Tcr.tcrPhase1`
is the class-TCR one). Lemma names unchanged. Where a package report (`OPEN-O2/O4/O7b.md`) uses an old helper name,
read the renamed one.

## 1. Delivered, by request
**R1** (`HSpec.lean`, `Prf.lean`; O1). `HSpec prims := publicHashSpec prims.core + ((SkPrf × Y × List Byte) →ₒ Y)`,
`PSpec prims D := unifSpec + ((D →ₒ Y) + HSpec prims)`, `closeImpl`, `restrictO` (open `restrictImpl`).
Programs `bPrfOpen A`, `bPrfWOpen wO A`, `bPrfCOpen A`, `bPrfWCOpen wO A`, checks `sufCheckOpen`, `eufCheckOpen`.
- `bPrfOpen_close : simulateQ (closeImpl prims (PkSeed × Adrs)) (bPrfOpen A) = bPrf A`; `bPrfCOpen_close`
  (`… (PkSeed × SkAdrs vp)) (bPrfCOpen A) = bPrfC A`); `bPrfWOpen_close w wO hw`, `bPrfWCOpen_close`;
  `bPrfWCOpen_close_suf : … (bPrfWCOpen sufCheckOpen A) = bPrfWC sufCheck A`; `close_restrictO`.
- `bPrfOpen_kindBound`, `bPrfWOpen_kindBound` (any kind ≠ unif, `prfB`); `*_hashes`: `.hash ≤ keygenHashes +
  qs·signHashes + (1 + verifyHashes)`; `*_prfmsg`: `.prfmsg ≤ qs`; `*_game`: `≤ 2^h'·len + qs·signReads`.
**R2** (`MsgV.lean`; O2). `msgOpenV A`, `msgOpenWV wO A : OracleComp (OSpec prims (msgG prims)) Bool`
(`wO : WinCheckO`; `sufCheckO`, `eufCheckO` = VCVio's `verifyInternalM` embedded as hash queries).
- `lazyRun_msgOpenV : lazyRun (PublicHash.impl prims) (msgOpenV A) = bPrfMsgL A`; `lazyRun_msgOpenWV_sufCheck :
  … (msgOpenWV sufCheckO A) = bPrfMsgWL sufCheck A`; `lazyRun_msgOpenWV_of_eval` (general `w`, `hw : wO.eval = w`).
- `msgOpenV_hashes`, `msgOpenWV_suf_hashes` (+ `lazyRes_…`): `≤ keygenHashes + qs·signHashes + (1 + verifyHashes)`;
  `_game ≤ qs`; `_sec ≤ 2^h'·len + qs·signReads`. ITSR: `Lazy.itsrOpen` has no final check; existing counts
  suffice; `itsrOpen_castForger`, `bItsrL_castForger_main`. Uniformity: `bPrfMsgL_castForger`, `bPrfMsgWL_castForger`.
**R3** second phases contain every `Thash`/`H_msg` evaluation.
- FORS (`Fors.lean`; O3): `forsTcr_phase2_open_eq`, `forsDspr_phase2_open_eq`: `(toTcr/toDspr (bOpenPreS A)).forge/guess
  (tbl,tg,ys) pk = forsRun (PublicHash.impl prims) tbl tg (forsFindOpen optRand A.main pk ys) >>= pure ∘ forsTcrPost /
  forsDsprPost tg`; `…_open_hashes`; `forsFindOpen_withTH`, `forsRun_withTH`, `…_open_eq_withTH` (for all `T`, `H`
  one fixed program interpreted by `PublicHash.impl (withTH prims T H)`). No extension of `findOpenFull` was needed.
- Class TCR (`Tcr.lean`; O4): `tcrM_phase2_open_eq gspec n A tbl L pk : liftM ((bTcrArM n A).forge (tbl,L) pk) =
  simulateQ (tblImpl (PublicHash.impl prims) tbl) (tcrMOpen optRand gspec A.main L pk) >>= pure ∘ classOut prims n L`;
  `tcrM_phase2_open_hashes`; `classOut_withTH`, `tcrMOpen_withTH`, `memoForgeOpen_withTH`,
  `tcrM_phase2_open_uniform`, `bTcrArM_phase2_open_uniform` (all `T`, `H`).
- WOTS (`Wots.lean`; O5): `wotsAnswerOpen` (open `wotsAnswer`; `wotsAnswerOpen_tbl`), `wotsUdOpenAll`,
  `wotsPreOpenAll`, `wotsTcrOpenAll`; `wotsUd/wotsPre/wotsTcrT/wotsTcr_phase2_open_eq : liftM (second phase) =
  simulateQ (tblImpl (PublicHash.impl prims) tbl) (open program)` (no post-processing); `…_open_hashes`;
  `wotsUd/Pre/TcrOpenAll_hashfree`.
**R4** first phases do no hashing of their own (O7a `Phase1Fors.lean`, `Phase1Tcr.lean`; O7b `Phase1Wots.lean`).
`forsDspr/forsTcr_phase1_hashfree T H A`, `tcrM_phase1_hashfree T H n A`, `wotsUd/wotsPre/wotsTcr/wotsTcrT_phase1_hashfree
T H A`: `.choose`/`.pick` at `castForger T H A` over `withTH prims T H` = the one at `A`. Stronger `withHash` forms
(all four components, ARBITRARY forger of the replaced scheme): `forsDspr/forsTcr_phase1_withHash`,
`tcrM_phase1_withHash`, `wots*_phase1_hashfree_all`. Explicit forger-free programs: `forsPhase1`, `tcrPhase1`
(Phase1Tcr), `udPhase1`/`prePhase1`/`wotsTcrPhase1` (Phase1Wots) with `toDspr_choose_eq`, `bTcrArM_choose_eq`,
`wots*_phase1_q1_zero`, `*_phase1_q1`, `phase1_programs_hashfree`.
**R5** wrappers (`Wrappers.lean`; O8). `toInternal_open`, `toInternalS_open`, `bytesToTyped_open`, `bytesToTypedS_open`,
`pureBytesToTyped_open`, `pureBytesToTypedS_open` (`W (cast… T H A) = cast… T H (W A)`, `rfl`),
`headline_bytes_open`, `headline_pureBytes_open`; explicit programs over `CorePrimitives` only: `extProg`,
`bytesProg`, `pureBytesProg` with `toInternal_main`, `bytesToTyped_main`, `pureBytesToTyped_main`, `headline_*_main`.
**R6** (`Bundle.lean`; see §0). `structure FinalResourcesOpen (A) (qs) : Prop` (45 fields), `theorem
final_resources_final_open (A) (qs) (hA) : FinalResourcesOpen A qs`; `final_resources_final_open_external`
(`ExtForger`, via `toInternal`), `final_resources_final_open_bytes` (`BytesForger`, via `bytesToTyped`);
`FinalResourcesOpen128s`, `final_resources_final_open_128s … : FinalResourcesOpen A qs ∧ FinalResourcesOpen128s A qs`.
New proofs only: `itsrOpen_hashes/_game/_sec` (closed forms from `Lazy.itsrOpen_kindBound`).
**R7** both forms where applicable: lemmas generic in the forger PROGRAM (`ForgerProg`; `TcrForgerProg` in Tcr.lean): `forsFindOpen_tbl`,
`forsFindOpen_kindBound/_hashes`, `tcrMForge_eq`, `tcrM_phase2_open_hashes` (takes `main`), `wots*_phase2_open_eq_main`,
`wotsForgeOpen_eq_main`; second phases DEFINED as interpretations: `forsTcrPhase2`, `forsDsprPhase2`
(`forsTcr/forsDspr_phase2_def`), `tcrMForge` (`tcrM_phase2_eq_tcrMForge`). WOTS: equation is already "= interpretation".

## 2. R6 table (hash-kind queries of the open program per run; 128s = `FinalResourcesOpen128s`)
| adversary | open program | equation | count lemma | closed form | 128s |
|---|---|---|---|---|---|
| `bPrfC A` | `bPrfCOpen A` | `bPrfCOpen_close` | `bPrfCOpen_hashes` (`_prfmsg ≤ qs`, `_game`) | `kgH + qs·sH + (1+vH)` | `269824 + qs·2007385 + 3929` |
| `bPrfWC sufCheck A` | `bPrfWCOpen sufCheckOpen A` | `bPrfWCOpen_close_suf` | `bPrfWCOpen_suf_hashes` | same | same |
| `Lazy.bPrfMsgL A` | `msgOpenV A` | `lazyRun_msgOpenV` | `msgOpenV_hashes` | same | same |
| `Lazy.bPrfMsgWL sufCheck A` | `msgOpenWV sufCheckO A` | `lazyRun_msgOpenWV_sufCheck` | `msgOpenWV_suf_hashes` | same | same |
| `Lazy.bItsrL A` | `Lazy.itsrOpen A` | `rfl` (`.main = lazyRun …`) | `Open.itsrOpen_hashes` | `kgH + qs·sH` | `269824 + qs·2007385` |
| `toDspr`/`toTcr (Lazy.bOpenPreS A)` | `forsFindOpen optRand A.main pk ys` | `forsDspr/forsTcr_phase2_open_eq` | `forsTcr_phase2_open_hashes` | `kgH + qs·forsSignHashes + (1+qs+k)` | `269839 + qs·1950028` |
| `bTcrArM n A` (∀ n) | `tcrMOpen optRand gspec A.main L pk` | `tcrM_phase2_open_eq` | `tcrM_phase2_open_hashes` | `kgH + qs·sH + (1+2·vH)` | `269824 + qs·2007385 + 7857` |
| `rUd … (Lazy.bWotsS A)` | `wotsUdOpenAll A hist hist2 root pk` | `wotsUd_phase2_open_eq` | `wotsUd_phase2_open_hashes` | `qs·wotsSignHistHashes + (wotsAnswerHashes + wotsWinHashes)` | `qs·121857 + 130239` |
| `rPre …` | `wotsPreOpenAll …` | `wotsPre_phase2_open_eq` | `wotsPre_phase2_open_hashes` | `… + wotsPreHashes` | `qs·121857 + 130274` |
| `rTcrT …` | `wotsTcrOpenAll …` | `wotsTcrT_phase2_open_eq` | `wotsTcrT_phase2_open_hashes` | `… + wotsTcrHashes` | `qs·121857 + 146514` |
(`kgH = Lazy.keygenHashes vp`, `sH = Lazy.signHashes vp`, `vH = Resources2.verifyHashes vp` = 3928 at 128s.)
Further fields: `*_uniform`/`*_open_hashfree` (same program for all `T`, `H`: msg, ITSR, FORS, TCR, WOTS); `*_phase1`
(R4, `withTH` form: FORS, TCR ∀ n, WOTS); game/secret counts (PRF, msg, ITSR). Left out, and why: no `withTH`
statement for the PRF programs (none delivered); `withHash` first-phase forms and R5 (other forger types; cited,
not fields); O6 counts (predicates on game runs, no `qs`); store variant (`Structural`, pinned program).

## 3. Deviations from the wording of `quantum/STATUS.md`
1. Verification term is `1 + verifyHashes`, not `verifyHashes` (R1, R2): `verifyHashes` excludes the forgery's `H_msg`.
2. Open checks: an arbitrary `WinCheck` (a Bool function) cannot be opened; `bPrfWOpen` takes `wO : OpenCheck`,
   `msgOpenWV` takes `wO : WinCheckO` (two definitions of the same type, O1/O2), with hypothesis `hw`, discharged
   for `sufCheck` (`sufCheckOpen`, `sufCheckO`). `eufCheckW` is new (no EUF `WinCheck` existed).
3. R1 counts use an own kind `HKind`/`hkind` on `PSpec` (`Lazy.Kind` has no `prfmsg`); C forms = `restrictO` applied.
4. R3/R4 "no hashing" is stated as invariance under `withTH prims T H` + `castForger` (`Thash`, `H_msg`) and, for
   first phases, under `withHash prims f` with an arbitrary forger. `PRF`/`PRFmsg` independence of second phases
   and wrappers is by inspection only (they are fields of `prims.core`; types change, transports not built).
5. R4 class TCR / WOTS: the first phases query the game's COLLECTION (and challenge) oracle; those `Thash`
   evaluations are the game's (part of the SM-TCR/UD/PRE-with-collection assumption), not the adversary's. FORS:
   empty collection. "q₁ = 0" is a program-level statement (the selection-phase spec has no hash oracle), not an
   `IsQueryBoundP` count.
6. `Tcr.lean` (and `TcrStoreCount.lean`): tactic `tcr_kernel_rfl` / `o9_kernel_rfl` assigns `Eq.refl` and leaves the
   definitional check to the kernel (elaborator does not unfold stuck matchers with differing `prims`). No axiom.
7. R3 TCR / WOTS equations live in `OracleComp (unifSpec + gspec)` with `liftM` on the closed side (every `gspec`).
8. R7: adversaries not redefined; generic-in-program lemmas plus defined phases (§1). `wotsAnswerOpen` is memoised
   (129714 hash queries at 128s, literal 182144); the equality is to the literal `wotsAnswer`. R6: see §0.
## 4. Newly formalised counts (previously argued)
- O1: hash / `PRF_msg` / game counts of the PRF distinguishers (table above; `.prfmsg ≤ qs`).
- O5: `wotsAnswer` tail: `wotsAnswerOpen_hashes`, `wotsAnswerHashes_128s : wotsAnswerHashes Link.vp = 129714`.
- O6 (`WotsCounts.lean`, `WotsCountsSM.lean`, `WotsCountsSamples.lean`), phase 1 at `Lazy.bWotsS A`:
  collection queries `rUd_collection_le`, `rPre_collection_le` (`wotsQc vp + #inst·len·(w-1)`), `rTcr_collection_le`,
  `rTcrT_collection_le` (`wotsQc vp + #inst·len`); `bWotsS_collection_le` (`wotsQc vp`), `wotsQc_closed`
  (`qc = 2^h·forsC + #trees·treeC`); wrapper samples `rUd/rPre/rTcr/rTcrT_wrapper_samples_le` (`≤ #inst·len`, for
  every `W`; programs `rUdPickS`, `rPreChooseS`, `rTcrChooseS`, `*_interp`).
  128s: `wotsQc_128s = 1057708653120046860861951`; UD/PRE `1062560399506556770327551` (= `tcrTargets`);
  TCR `1058032102879147521492991`; samples `323449759100660631040`.
  CORRECTION: each of the three collection numerals is 1023 (= 2^(h'+1) − 1) SMALLER than the argued values in
  FINAL3/W3 (`…862974`, `…328574`, `…494014`): the top tree is evaluated once (`#trees·T`, not `(#trees+1)·T`).
## 5. Answer-storing variant (O9; `TcrStore.lean`, `TcrStoreHeadline.lean`, `TcrStoreCount.lean`, `TcrStoreCover.lean`)
`bTcrArA n A` (phase 1 of `bTcrArM` through `routeA`, state also keeps the answers; phase 2 = `memoForge` over
`withTH prims (lkT pk S) prims.Hmsg`). `bTcrArA_experiment_eq hS`, `bTcrArA_advantage_eq`, `_eq_tight`,
`bTcrArA_phase1`; headline restated: `boundFinalStore_eq`, `slhdsa_{suf,euf}_cma_final_store` (+ pure, bytes,
128s). Open program `storeForgeOpen A L S pk := simulateQ (memoImpl pk S) (memoForgeOpen A L pk)`,
`bTcrArA_forge_open`; count `storeForgeOpen_hashes`: `≤ qs + (1 + verifyHashes)` (128s: `qs + 3929`, vs
`269824 + qs·2007385 + 7857` for `bTcrArM`), `bTcrArA_phase2_hashes`.
DEVIATION ("pinned program"): the count is for `simulateQ (pinImpl tbl) (storeForgeOpen …)` (secrets from `tbl`,
hash answers the real ones, every hash query still issued and counted; `pinImpl_tbl`: same adversary), not for
`storeForgeOpen` under arbitrary answers — there no better bound is true. Hypothesis `Structural vp prims`
(experiment equality). Lookups in the store (linear scans) and memory (`tcrTargets` extra `Y` values) not counted.
## 6. Not done, and the obstacle
- `PRF`/`PRFmsg` independence (`withHash`) of second phases, PRF programs, wrappers: types indexed by `prims.core`
  change (needs transports of `PublicKeyCore`/`SignatureCore`/codec); "never applies `prims.PRF`" is by inspection.
- First phases in the `Lazy.OSpec` counting model (0 `.hash` queries); exact sample count for `rTcr`; `Reduction/Gen`
  versions of the `withTH` statements; store variant: linear-form/E2E restatements, EUF byte-level 128s. No time model.
## 7. Checks
`#print axioms`: every line of the 18 package files (O-reports) and of `Bundle.lean` (5 lines, shadow build) ⊆
`[propext, Classical.choice, Quot.sound]`. `grep` of `Reduction/Open/*.lean` for `sorry`, `axiom `, `native_decide`,
`bv_decide`: two comment lines only ("No axiom is involved": `Tcr.lean:34`, `TcrStoreCount.lean:35`). All names
cited here were checked against the constants of the compiled modules.
## 8. New files
`Reduction/Open/`: `WithHash`, `HSpec`, `Prf` (O1), `MsgV` (O2), `Fors` (O3), `Tcr` (O4), `Wots` (O5), `WotsCounts`,
`WotsCountsSM`, `WotsCountsSamples` (O6), `Phase1Fors`, `Phase1Tcr` (O7a), `Phase1Wots` (O7b), `Wrappers` (O8),
`TcrStore`, `TcrStoreHeadline`, `TcrStoreCount`, `TcrStoreCover` (O9), `Bundle` (O10).
`status/`: `OPEN-BRIEF.md`, `OPEN-O1.md` … `OPEN-O9.md`, `OPEN.md`, `OPEN-rename.patch`.

