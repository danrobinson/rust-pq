# HANDOFF — composed QROM theorem for SLH-DSA-SHA2-128s (bridge work)

> **Superseded (2026-11-21).** The remaining chain described here has been carried out: `hInd`
> and every `BridgesRest` field are proved, and the closed headline is in
> `Integration/SlhDsaComposedClosed.lean`. Current state: `../HANDOFF.md`. This file is kept as
> the record of the plan that was followed.


For someone picking this up cold. Read with `quantum/STATUS.md` (top notes + §A) and
`security/status/OPEN.md`. Everything below is factual as of the last session; "not verified"
means exactly that.

## 0. Build / check

```
cd quantum && PATH=$HOME/.elan/bin:$PATH lake build                       # default target PQ
cd quantum && PATH=$HOME/.elan/bin:$PATH SKIP_DEFAULT_BUILD=1 scripts/check-integration.sh
```
Last outputs: see §7. Lean 4.36.0; VCVio by path (`../.tools/VCVio-upstream`, commit a10530a).
This session additionally built the VCVio module `VCVio.Quantum.Oracle.ClassicalCalls` (it is in
the checkout but was not previously compiled; it is now imported by
`PQ/Interactive/QromBridgeCall.lean`; `lake build` builds it on demand, 1.9 s).

Rules in force: no `sorry` / `axiom` / `native_decide` / `bv_decide`; headlines must print
`[propext, Classical.choice, Quot.sound]`; never hide a hypothesis in a definition; new files in
`quantum/` only; do not touch `security/` (another worker builds `security/Ideal/Transport/`).

## 1. Current headlines (unchanged this session)

`quantum/Integration/SlhDsaComposedEnc.lean:85` (SUF) and `:122` (EUF, identical except
`prfMachEuf`, `qbPrfMsgL`, `qUnforgeableAdvantage`). Verbatim (SUF):

```lean
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc
    (F : PortForger (EncX c) EncY E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (_htl : 35 ≤ c.tl)
    (hInd : ∀ (ω : Ω128 c) g H, prfMachSuf c optRand₀ pkSeedDist₀ F (ω.withPrf g) H =
      prfMachSuf c optRand₀ pkSeedDist₀ F ω H)
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesRest c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F)
        (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω))
          (qbPrfMsgWL sufCheck (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
          (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀)
        (fun ω ↦ qPrfIdealPr (qbPrfMsgWL sufCheck (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
          (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) q qs r) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs r.noPrf
```
(section variables: `E` finite with decidable equality, `c : Caps`,
`optRand₀ : Bytes n → Bytes n → ProbComp (Bytes n)`, `pkSeedDist₀ : ProbComp (Bytes n)`.)

Hypotheses in plain words:
* `hq`, `hqs`, `hcap`: the forger is one port program over the fixed encoding `encΩ` with at most
  `q` quantum port calls and `qs` signing queries per path, and respects the message-length caps.
  (Assumptions on the forger, not open proof obligations.)
* `_htl : 35 ≤ c.tl`: Thash list cap covers the largest arity. Unused by the current proof;
  needed by step 4 below (row embedding of arity-`n` lists into `BList _ c.tl`).
* `hInd` (UNPROVED): the PRF distinguisher machine built by the reduction does not depend on the
  `PRF` component of the world. Not `rfl` (types `PublicKeyCore core`, `SignatureCore core` are
  indexed by the whole `core`, which contains `PRF`). Waits on the transport library
  `security/Ideal/Transport/` (other worker).
* `hB : … → BridgesRest …` (UNPROVED, eleven fields, `SlhDsaComposedEnc.lean:41`): for each of
  `msg, itsr, dspr, tcrFv, tcr1, tcr2, tcrLen, tcrK, ud, pre, tcrT`, the `ω`-averaged Part-1 game
  of the reduction machine around the forger is at most a sub-convex mix (`MixLE` / `MixPair`,
  `SlhDsaComposedFinal.lean:92/98`) of Part-2 exact-game values (`TcrValue`, `PrfValue`, …:
  adversaries with zero first-phase quantum queries, at most `q + r.<term>` second-phase
  queries, sizes `2^128`).
* `r : RedCounts` is a free parameter; intended instance `openCounts128s qs`
  (`SlhDsaComposedFinal.lean:359`), tied to `security/` by `openCounts128s_sound`
  (`Integration/SlhDsaOpenCounts.lean`).

Bound: `composedBoundFinal` (`SlhDsaComposedFinal.lean:375`) =
`epsPrf(q+r.prf) + epsPrf(q+r.msg) + epsItsr(q+r.itsr, qs) + (epsDsprTight(q+r.dspr) +
3·epsTcr0(q+r.tcrFv)) + Σ_{1,2,len,k} epsTcr0(q+r.tcr·) + (w−2)·epsUdTight(q+r.ud) +
epsPre0(q+r.pre) + epsTcr0(q+r.tcrT)`, with `r.noPrf` (PRF term charged `q` only).

## 2. Proved vs. assumed, per term

| term | Part-2 bound (proved) | bridge Part-1 → Part-2 |
|---|---|---|
| PRF (sk) | `prfExact_tight_abs_le`, `prfStruct_real_le_ideal_add` | PROVED modulo `hInd`: `prf_term_suf` (`SlhDsaBridgePrf.lean:305`), `prf_term_euf` |
| PRF_msg | same | ASSUMED (`BridgesRest.msg`); same type obstacle as `hInd` plus lazy/H_msg handling |
| ITSR | `itsr4_adaptive_fors_le` | ASSUMED (`.itsr`); also needs uniform pushforward of the digest through `splitDigest` (not proved) |
| DSPR | `dspr_exact_tight_zeroPre_of_card` | ASSUMED (`.dspr`) |
| TCR-FV (FORS) | `tcr_fv_exact_le_zeroPre` | ASSUMED (`.tcrFv`) |
| TCR arity 1, 2, len, k | `tcr_exact_le_zeroPre`, core `spr_embedded_obs_weighted_le` (`PQ/QROM/SprGiven.lean:362`) | ASSUMED (`.tcr1/.tcr2/.tcrLen/.tcrK`); infrastructure of this session targets these |
| UD (WOTS) | `gen_ud_exact_tight_real_le_ideal_add` | ASSUMED (`.ud`) |
| PRE (WOTS) | `gen_pre_sub_exact_le` zeroPre form | ASSUMED (`.pre`) |
| TCR (WOTS) | as TCR | ASSUMED (`.tcrT`) |

The standard-model reduction itself (`…_linear_quantum_uniform`, Part 1) and all Part-2 bounds are
proved (STATUS §B, §C). No `BridgesRest` field is discharged.

## 3. Done this session (all `[propext, Classical.choice, Quot.sound]`, in the default target)

**Step 1 — PROVED.** `PQ/Interactive/QromBridgeCall.lean`:
* `run₂_callBasis_branch` (`:58`), exactly the requested statement:
  ```lean
  theorem run₂_callBasis_branch (B : QReg) (H : X → Y) (x : X) (y : Y)
      (M : Matrix (B × Unit) (B × Unit) ℂ) :
      ((oracleRt H).run₂ .instruments
        (QComp.callBasis (spec := qromSpec X Y) () B (x, (0 : Y)) (fun o _ ↦ o.2))).branch y M =
        if H x = y then M else 0
  ```
  Route: `addEmu H : EmulatedOracle Unit (fun _ ↦ QReg.of (X × Y))` (`@[reducible]`, private
  register `Unit`, `U = oracleUnitary H ⊗ₖ 1`), `addEmu_step` (its runtime steps = those of
  `oracleRt H`, via `dsub_ext`), `addEmu_block`, then VCVio's
  `EmulatedOracle.branch_run₂_callBasis` (`VCVio/Quantum/Oracle/ClassicalCalls.lean:333`).
  Pitfalls met: `addEmu` must be `@[reducible]` (instance-transparency failures otherwise); a
  `rw` with the runtime equality fails ("motive is not type correct", the register type depends on
  the runtime) — the proof instead transports along equality of the `step` field only (`aux`).

**Step 2 — PARTIAL.** `PQ/Interactive/QromBridgeEval.lean`:
* `WCount w P n` (`:40`): weighted query count of a classical program.
* `PUE cnt Mach q` (`:65`): `PU` plus constructor
  `eval (x) (k : Y → (X → Y) → QOC …) (q) : (∀ y, PUE cnt (k y) q) → PUE cnt (fun H ↦ k (H x) H) (q+1)`
  and a weight `cnt t` charged at each classical-interface query `t` (budget for the evaluations
  its implementation will make): `query … : PUE cnt (…) (q + cnt t)`.
* proved closure: `PUE.mono`, `.bind`, `.liftQ_bind` (needs `WCount cnt ob n`), `.map`, `.wrap`,
  `.wrap0` (hypothesis: the wrapper's code for `t` has `WCount cnt' … (cnt t)`).
* `EvalCost f n` (`:202`) for `f : (X → Y) → ProbComp γ` (continuation-style: `f H` can be run in
  front of any closed `PUE` machine at price `n`); `EvalCost.const` (H-independent: 0), `.eval`
  (`fun H ↦ pure (d (H x))`: 1), `.bind`, `.map`, `.mono`, `.simulateQ` (interpretation of an
  open program whose queries have costs `w t`, program of `WCount w P n`: cost `n`).
* `PUE.close` (`:273`): closing with an implementation `impl H` that depends on the port
  function, `∀ t s, EvalCost (fun H ↦ (impl H t).run s) (cnt t)`, gives a closed
  `PUE (spec := unifSpec) cnt0` machine with the same bound. `PUE.liftU_bind`.
* NOT done in step 2: `PUE.compileQ`, `PUE.exists_prog(_qprob)`, the `HybridModel` (statements
  and routes in §4, steps 2a–2c).

Steps 3–5: not started (analysis only; see §4).

## 4. Remaining chain (ordered), with statements and routes

Goal re-stated: because the Part-2 value classes (`TcrValue`, …) demand a `QuantumComp` over the
two-port spec of the Thash table ALONE and a uniform seed, while the Part-1 game has the port
function `encΩ ω` (four components) and an arbitrary `pkSeedDist₀`, the intended route does NOT
go through `MixLE … TcrValue`. Prove the term inequality directly, e.g.
`avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM n (B ω))) ≤ epsTcr0 (q + r.tcr·)`, and restate the
headline taking `composed_of_linear_eps`'s argument directly (drop the field from `BridgesRest`).

### 2a. `PUE.exists_prog` (in `QromBridgeEval.lean`)
```lean
theorem PUE.exists_prog {Mach : (X → Y) → Closed (WS X Y E) α} {q : ℕ}
    (h : PUE (spec := unifSpec) cnt0 Mach q) :
    ∃ x : QuantumComp LocalSig.instruments.{0} (qromSpec X Y) (fun _ ↦ α) (progReg X Y E),
      x.IsQueryBound (fun _ ↦ q) ∧
      ∀ (Ev : α → Prop) [DecidablePred Ev] (H : X → Y) (M : Matrix (WS X Y E) (WS X Y E) ℂ),
        M.PosSemidef →
        leafW (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments x M Ev =
          qWeight Ev (Mach H) M
```
Route: copy `PU.exists_prog` (`QromBridgeUnif.lean:323`) for `pure/instr/port/query` (in the
`query` case the index is `q + cnt0 t`, defeq `q`). New `eval x k` case: program
`PQ.QROM.fidBind (QComp.callBasis (spec := qromSpec X Y) () (progReg X Y E) (x, 0) (fun o _ ↦ o.2))
(fun y ↦ xk y)` (`PQ/QROM/Fidelity.lean:106`; needs `L : LocalSig.{1,0}`, which
`LocalSig.instruments.{0}` is); query bound from `fidBind_isQueryBound` (`:127`) +
`QComp.isQueryBound_callBasis` (`VCVio/Quantum/Oracle/Classical.lean`), then rewrite
`Pi.single`-style budget to `fun _ ↦ q + 1`; semantics: unfold `leafW`, per leaf use
`fid_run_fidBind_det` (`Fidelity.lean:120`) with `a₀ := H x`, `σ' := M`, both hypotheses from
`run₂_callBasis_branch`. `PUE.exists_prog_qprob`: copy `PU.exists_prog_qprob` (`:390`). Not
attempted; no known obstacle.

### 2b. `PUE.compileQ`
```lean
theorem PUE.compileQ (cnt : ι → ℕ) (P : QOC ((X × Y) × E) (portSpec + spec) α) (n : ℕ)
    (hP : WCount (Sum.elim (fun _ ↦ 0) (Sum.elim (fun _ ↦ 1) cnt)) P n) :
    PUE cnt (fun H ↦ PQ.Interactive.compileQ H P) n
```
(copy `PU.compileQ`, `QromBridgeUnif.lean:292`), plus a lemma turning
`CountBound isPort P q ∧ CountBound isSign P qs` into that `WCount` with `n = q + qs * c`
(`cnt` = `c` on signing queries, 0 elsewhere).

### 2c. Hybrid model of a closed `PUE` machine
```lean
theorem PUE.exists_model {Mach : (X → Y) → Closed (WS X Y E) α} {q : ℕ}
    (h : PUE (spec := unifSpec) cnt0 Mach q) (ρ : SubState ((X × Y) × E)) :
    ∃ Mo : PQ.QROM.HybridModel X Y α q, ∀ (H : X → Y) (Ev : α → Prop) [DecidablePred Ev],
      Mo.prob H Ev = qWeight Ev (Mach H) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
```
Route: `HybridModel.ofProgram` (`PQ/QROM/Hybrid.lean:355`, `dec := Sigma.snd`) on the program of
2a + `exists_prog_qprob`. The forger's `ρ₀` is of the form `ρ.matrix ⊗ₖ basis` by
`exists_subState` (`SlhDsaBridgePrf.lean:127`).

### 3. Reduction machines as `PUE` families in the port function
Needed statement (per term; TCR shown), for a fixed world `ω₀`, state `st`, seed `pk`:
there is `Mach : (EncX c → EncY) → Closed (WS (EncX c) EncY E) _` with
`PUE cnt0 Mach (q + r.tcr·)` and, for every Thash table `T`,
`Mach (encΩ (ω₀ with thash := T)) = (qbTcrArM n (internalΩ … encΩ F (ω₀ with thash := T))).forge st pk`.
(No type obstacle expected: `Thash`/`H_msg` are not in `core`. Not verified by compiling.)
Ingredients:
* forger: `intF`/`pu_intF` (`SlhDsaBridgePrf.lean:199/204`) redone with `PUE.compileQ`, `.wrap0`,
  `.map` (signing queries weighted by the per-signature hash count).
* `qMemoForge` (`Integration/SlhDsaQuantumLinear.lean`, def above `qbTcrArM` at `:66`) is
  `close (unif-lift + g2SignOracle optRand (idealPk …) (idealSign …)) (Q.main (idealPk …)) [] >>=
  liftU (pure (classOut … (findCollisionM … (verifyCalls …))))`. Use `PUE.close` + `PUE.liftU_bind`;
  the `EvalCost` hypotheses must come from the open programs of `security/`:
  `Reduction.Open.tcrMOpen` (`security/Reduction/Open/Tcr.lean:67`: `Lazy.openKeygen`,
  `logSignOracle … Lazy.openSign`, `PublicHash.hmsg`, `Resources2.collO`/`verifyFree`),
  interpretation `Lazy.tblImpl (PublicHash.impl prims) tbl` (`security/Reduction/Lazy/Core.lean:127`),
  equation `Resources2.bTcrArM_forge_open` (`security/Reduction/TcrMemo.lean:610`), counts
  `tcrM_phase2_open_hashes`.
  GAP: those equations are for a CLASSICAL forger program (`simulateQ … (main pk)`); the quantum
  machine needs the PER-QUERY statements (`idealPk = interp openKeygen`,
  `g2SignOracle … idealSign` query-by-query `= interp (logSignOracle … openSign)`, final
  verification/collision search `= interp (hmsg; collO verifyFree)`). They should be the
  ingredients of the proof of `bTcrArM_forge_open`; not located/extracted this session.
* each `PublicHash.impl (primsΩ ω) t` as ONE port evaluation: `encΩ_thash/_hmsg/_prf/_prfMsg`
  (`SlhDsaBridgePrf.lean:91–97`) for in-cap inputs; out-of-cap inputs of `primsΩ` are constants
  (`EvalCost.const`). Then `EvalCost.simulateQ`. The security-side counts are `IsQueryBoundP` /
  `kindBound` predicates; a conversion to `WCount` is needed (not written).

### 4. Abstract Part-1 TCR theorem (two ports/phases avoided by pullback)
Suggested new file `PQ/Interactive/QromBridgeTcr.lean`. Shape of the argument (mirrors
`twoPhaseHyb_tcr_le`, `PQ/QROM/ExactTcr.lean:283`, at `q₁ = 0`):
1. Unfold `qSM_DT_TCR_Experiment` (`PQ/Interactive/Games.lean:231`):
   `liftU seedGen >>= liftU (first phase run) >>= forge >>= check`. Needs a `tsum` version of
   `qWeight_liftU_bind_sum` (`QromBridgeUnif.lean:60` requires `Fintype γ`; first-phase outputs
   contain lists): `qWeight p (liftU oa >>= f) ρ = ∑' x, prob oa (· = x) * qWeight p (f x) ρ`.
2. Resample the Thash row at `(pk, arity n)`: analogue of `avΩ_resample_prf`
   (`SlhDsaBridgePrf.lean:241`) for `thash` (row `R : Tw × Msg → Y'`, `Msg` = lists of length `n`,
   embedded in `BList _ c.tl` using `n ≤ 35 ≤ c.tl`).
3. Per seed `pk` and first-phase output `r`: model `Mo` of the forge machine (2c) over
   `EncX c → EncY`, pulled back with `HybridModel.pullback` (`PQ/QROM/HybridPullback.lean:33`)
   along `φ T := encΩ (ω₀ with thash := T)`, `ι := Sum.inl`; then
   `spr_embedded_obs_weighted_le` (`SprGiven.lean:362`) with `A := ℝ≥0∞`,
   `obs R := Pr[first phase with row R outputs r]`, `w := id`, `M` constant, `c := cOf r`
   (target of each target tweak), `out l := (tweak of the l.1-th target, l.2)`.
4. `hobs`: the probability that the classical first phase (`simulateQ (SM_DT_TCR_oracles P pk)
   choose` from `([], [])`) outputs `r` is unchanged when the row is modified at a non-target point
   of a target tweak of `r`. To prove by induction on `choose` (a ProbComp/StateT analogue of
   `flat_branch_congr` / `tcrCh_loc`, `ExactTcr.lean`): challenge queries only read target
   points; collection queries on a tweak in the challenge history are rejected, and challenge
   queries on a spent collection tweak are rejected, so needs the reachable-state invariant
   "challenge tweaks distinct and disjoint from collection tweaks" (VCVio's state records
   collection TWEAKS only). The collection family of `thashArityProblemT`
   (`security/Reduction/TightCaps.lean:261`) was NOT inspected: check that its members read the
   same row only at other tweaks, or lie outside the row (then they are part of the background
   `F`).
5. First phase independent of the forger and of the hash except through the game oracles:
   `bTcrArM_choose_eq`, `tcrM_phase1_withHash` (`security/Reduction/Open/Phase1Tcr.lean:162/227`).
6. Sum up: `Σ_pk Pr[pk] Σ'_r avg_R (w_r(R)·prob) ≤ (2q'+1)²/2^128 · Σ_pk Pr[pk] avg_R Σ'_r w_r(R) ≤
   (2q'+1)²/2^128` (`card_bytes_n`, `SlhDsaBridgePrf.lean:177`). Arbitrary `pkSeedDist₀` is fine
   here (it would not be through `TcrValue`, whose seed is uniform).

### 5. Discharge and restate
`tcr1, tcr2, tcrLen, tcrK` (one proof, parameter `n`), `tcrT` (`qrTcrT`, WOTS open programs
`wotsTcrOpenAll`, `security/Reduction/Open/Wots.lean`), then `tcrFv`, `dspr` (FORS:
`forsFindOpen`, `forsTcr/forsDspr_phase2_open_eq`), `pre`, `ud`, then `itsr` (also needs: uniform
`Bytes m` digest pushes forward uniformly through `splitDigest`; not proved), `msg` (waits on the
transport, like `hInd`). Restate `…_qrom_enc` with only the undischarged fields.

### Tried and rejected
* Going through `TcrValue`/`MixLE` for the TCR family: needs (a) simulating the four-component
  port unitary by the Thash-table oracle (ancilla simulation), (b) a uniform seed vs. arbitrary
  `pkSeedDist₀` (row-swap relabelling of queries), (c) fidelity for first phases with adaptive
  coins (`fid_tcrExp_eq` covers coin-free / one up-front coin). The direct route above avoids all
  three.
* Extending `PU` itself with an `eval` constructor: breaks every `induction … with` over `PU`
  (`QromBridgeUnif.lean`, `QromBridgePrfStruct.lean`); hence the separate `PUE`.

## 5. Known limitations (accepted)
* The reduction's classical hash evaluations become `eval` nodes = Part-2 oracle calls, charged
  quadratically: at `r = openCounts128s qs` the bound is vacuous for `qs ≳ 2^28` (ITSR) / `2^39`
  (other terms). No cheap way to avoid the charge was found for any term.
* ITSR keeps the reprogramming loss `2q'√(qs/2^128)` (general regime; STATUS §A.3).
* `hInd` (and the `msg` field) wait on `security/Ideal/Transport/`.
* Pure-bytes interface only; `r` is a free parameter; everything vacuous at `q = 2^64`.

## 6. Unverified / unaudited
* `PUE`/`EvalCost` have not been instantiated on any SLH-DSA machine; the design (weights on
  interface queries, continuation-style `EvalCost`) is untested against step 3.
* Steps 3–5 are analysis from reading definitions, not compiled statements; in particular the
  claims "no type obstacle for Thash", the shape of `thashArityProblemT`'s collection, and the
  availability of per-query open-form lemmas in `security/` are unchecked.
* Nothing here was independently audited. `STATUS.md` body (§A–§D) was not re-validated.

## 7. Last build / check output
`lake build` (default target, after adding the two new modules to `PQ.lean`):
```
✔ [7224/7226] Built PQ (1.4s)
Build completed successfully (7226 jobs).
```
`#print axioms` lines of the new files: `run₂_callBasis_branch`, `PUE.bind`, `PUE.wrap`,
`PUE.wrap0`, `EvalCost.simulateQ`, `PUE.close` — all `[propext, Classical.choice, Quot.sound]`.

`SKIP_DEFAULT_BUILD=1 scripts/check-integration.sh`:
```
204 theorems checked, 0 with non-standard axioms

PASS: default target built, security oleans up to date, all Integration files compiled, only standard axioms.
```
