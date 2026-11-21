# HANDOFF — agent `qtcr` (game side of the class-TCR bridge)

Status: DONE (definition of done met), plus the WOTS TCR term (game side) and, combined with agent
`qmach`'s `tcr_hModel`, the four class-TCR terms CLOSED and the `_qrom_enc` headlines restated
without the four class-TCR bridge fields. Everything compiled; every `#print axioms` line is
`[propext, Classical.choice, Quot.sound]` (two lemmas: `[propext, Quot.sound]`). No `sorry`,
`axiom`, `native_decide`, `bv_decide`. Nothing committed. No existing file edited.

## New modules (coordinator: add to the build)
* `quantum/PQ/Interactive/QromBridgeTcr.lean` — lake module `PQ.Interactive.QromBridgeTcr`
  (add `import PQ.Interactive.QromBridgeTcr` to `PQ.lean`). Generic, no SLH-DSA.
* `quantum/Integration/SlhDsaBridgeTcr.lean` (imports `Integration.SlhDsaComposedEnc`,
  `Reduction.Open.Phase1Tcr`, `PQ.Interactive.QromBridgeTcr`, `PQ.QROM.HybridPullback`).
* `quantum/Integration/SlhDsaBridgeTcrT.lean` (imports the above + `Reduction.Open.Phase1Wots`).
* `quantum/Integration/SlhDsaBridgeTcrClosed.lean` (imports `SlhDsaBridgeTcr`,
  `SlhDsaBridgeMach` (qmach), `SlhDsaComposedEnc`).
No `security/` file was created.

## Headlines (verbatim statements)

Section variables of the Integration files: `{E} [Fintype E] [DecidableEq E] (c : Caps)
(optRand₀ : Bytes n → Bytes n → ProbComp (Bytes n)) (pkSeedDist₀ : ProbComp (Bytes n))
(F : PortForger (EncX c) EncY E)` (as `SlhDsaBridgePrf.lean`). `pkSeedDist₀` arbitrary.

`Integration/SlhDsaBridgeTcr.lean:288`
```lean
theorem tcr_term (n : ℕ) (hn : n ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : Ω128 c) (st : Open.TcrP1State Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY
          (ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = n}) q',
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = n} → Prop)
          [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
      (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsTcr0 q'
```
`:341` `tcr_terms_four (q) (r : RedCounts) (htl : 35 ≤ c.tl) (hModel : ∀ nq ∈ [(1, q + r.tcr1),
(2, q + r.tcr2), (Link.vp.params.len, q + r.tcrLen), (Link.vp.params.k, q + r.tcrK)], <hModel above
with n := nq.1, q' := nq.2>)` : the conjunction of the four inequalities
`avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM N (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
epsTcr0 (q + r.tcr·)` for `N = 1, 2, len, k` — exactly `h1 h2 hLen hK` of `composed_of_linear_eps`.

`Integration/SlhDsaBridgeTcrClosed.lean`
* `:32` `tcr_term_closed (n) (hn : n ≤ c.tl) (q qs) (hq : ∀ pk, CountBound isPort (F.main pk) q)
  (hqs : ∀ pk, CountBound isSign (F.main pk) qs) : avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM n
  (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsTcr0 (q + tcrMHashes Link.vp qs)`
  (= `tcr_term` + qmach's `tcr_hModel`).
* `:44` `tcr_terms_closed_128s (q qs) (htl : 35 ≤ c.tl) (hq) (hqs)` : the four inequalities with
  `epsTcr0 (q + (openCounts128s qs).tcr1/.tcr2/.tcrLen/.tcrK)`. No model hypothesis.
* `:106` / `:144` `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_tcr`: the `_qrom_enc` headlines
  with `r := openCounts128s qs`, the hypothesis `hB` now `… → BridgesRestNoTcr …` (`:76`, the
  seven fields `msg itsr dspr tcrFv ud pre tcrT`, verbatim copies of the `BridgesRest` fields),
  `htl` now USED; conclusion `≤ composedBoundFinal q qs (openCounts128s qs).noPrf`. `hInd` unchanged.

`Integration/SlhDsaBridgeTcrT.lean:191` (WOTS-chain TCR, game side)
```lean
theorem tcrT_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : Ω128 c) (st : Open.RState Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n) q',
        ∀ (T : …same…) (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
      (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsTcr0 q'
```
Its `hModel` is NOT discharged (needs qmach's recipe for the WOTS open programs `wotsTcrOpenAll`).

`PQ/Interactive/QromBridgeTcr.lean` (generic)
* `:62` `qWeight_liftU_bind_tsum`: `qWeight p (liftU oa >>= f) ρ = ∑' x, prob oa (· = x) * qWeight p (f x) ρ`.
* `:215` `tcr_run_prob_congr` (the `hobs` fact, proved by induction on the program; invariant via
  `TcrExt`/`tcr_run_ext`/`tcr_run_nodup`).
* `:399` `tcr_row_avg_le`: abstract theorem over an arbitrary problem `P`, hash/collection
  families `thR`, `ceR` (row hash at `pk`; collection reads `R (t, ·)` only at its tweak), fixed
  selection program, and a model family `∀ s, ∃ Mo : HybridModel (Tw × M) Y (ℕ × M) q, …`;
  conclusion: row average of the per-seed game weight `≤ (2q+1)²/|Y|`.
* `:547` `qSM_DT_TCR_Advantage_eq_tsum` (seed average of `tcrInner`).

## Findings
* Step 4 check (handoff flagged UNCHECKED): `thashArityProblemT`'s collection is `thashColl` =
  the whole `Thash`, one member, message `List Y` (`security/Reduction/Basic.lean:84`). Its
  queries at tweak `t` read the row only at `(t, ·)`, and VCVio rejects collection queries at
  reserved tweaks and challenge queries at spent collection tweaks — so the planned route works
  unchanged (no change of route was needed). Same for `wotsTcrProblemT`.
* `tcrPhase1` / `wotsTcrPhase1` at `{ω with thash := T}` vs `ω`: elaborator `rfl` hits max
  recursion; a kernel-only `rfl` (`qtcr_kernel_rfl`, `SlhDsaBridgeTcr.lean:142`, same idea as
  `security`'s `tcr_kernel_rfl`) is fast. `attribute [local irreducible] arityTargets tcrTargets
  wotsStepTargetsT wotsStepTargets` is needed to avoid evaluation of the caps.

## Not done
* `tcrT` closed: needs a `qmach`-style `hModel` for `qrTcrT` (then exactly `tcrT_term`).
* Not audited: qmach's `SlhDsaBridgeMach.lean` (consumed via its compiled olean of 23:16; if it
  changes, recompile `SlhDsaBridgeTcrClosed.lean`).
* The full `scripts/check-integration.sh` was not run (coordinator's job).

---

# Assignment 2 — FORS-leaf machine models (`tcrFv`, `dspr`)

Status: `tcrFv` DONE and CLOSED; `dspr` model delivered with ONE named hypothesis `hRows`.
All `#print axioms` lines `[propext, Classical.choice, Quot.sound]` (`forsMHashes_openCounts128s`:
`[propext]`). No existing file edited.

## New Integration files (not lake modules; compiled by hand, oleans in `.lake/build/integration`)
* `Integration/SlhDsaBridgeMachFors.lean` (imports `Integration.SlhDsaBridgeMach`,
  `Reduction.Open.Fors`, `Reduction.Open.Phase1Fors`, `PQ.Interactive.GamesGeneral`,
  `PQ.QROM.ExactDsprTightGame`).
* `Integration/SlhDsaBridgeForsClosed.lean` (imports qfors's `SlhDsaBridgeFors` + the above).

## Statements (`SlhDsaBridgeMachFors.lean`; section variables `c optRand₀ pkSeedDist₀ F`)
* `qFindRun_eq_fRun` (Part A, generic in `prims`): `qFindRun Q st pk = fRun optRand (PublicHash.impl prims) Q.main st pk`.
* `forsMach_encΩ`: `forsMach c optRand₀ F ω₀ st pk (encΩ {ω₀ with thash := T}) = qFindRun (internalΩ … {ω₀ with thash := T}) st pk`.
* `pue_forsMach … : PUE cnt0 (forsMach …) (q + forsMHashes Link.vp qs)`.
* `fors_tcr_mach_exists` / `fors_dspr_mach_exists`: `∃ Mach, PUE cnt0 Mach (q + forsMHashes Link.vp qs) ∧ ∀ T, Mach (encΩ {ω₀ with thash := T}) = (qToTcr (internalΩ … {ω₀ with thash := T})).forge st pk` (resp. `(qToDspr …).guess st pk`).
* `forsTcr_hModel (q qs) (hq) (hqs)`: EXACTLY qfors's `tcrFv` hypothesis with `q' = q + forsMHashes Link.vp qs`.
* `forsDspr_hModel (q qs) (hq) (hqs) (hRows)`: EXACTLY qfors's `dspr` hypothesis (`Mo.Additive ∧ RowsBound … ∧ ∀ T Ev, …`), `Additive` PROVED (`ofProgram_additive`), `RowsBound` from
  ```lean
  (hRows : ∀ (x : QuantumComp LocalSig.instruments.{0} (qromSpec (EncX c) EncY)
      (fun _ ↦ ℕ × Bool) (progReg (EncX c) EncY E)) (ρ : SubState ((EncX c × EncY) × E))
      (hx : x.IsQueryBound (fun _ ↦ q + forsMHashes Link.vp qs)),
    PQ.QROM.Rows.RowsBound (fun H Ev ↦ ((PQ.QROM.HybridModel.ofProgram
      LocalSig.Interp.instruments x ρ (q + forsMHashes Link.vp qs) hx Sigma.snd).prob H Ev).toReal)
      (q + forsMHashes Link.vp qs))
  ```
  i.e. "the rows bound holds for `ofProgram` models of one-port programs" — NOT proved (only
  `ofSecondPort_rowsBound` exists). Next step: relabel a `qromSpec` program as a `qrom2Spec`
  program calling only port `true` (`secondBudget q`), show `leafProb (twoRuntime (ports F H))` of
  the relabelled program = `qprob H` of the original, then `ofSecondPort_rowsBound`.
* `forsMHashes vp qs := keygenHashes vp + qs * (forsSignHashes vp + 1) + (1 + k)`;
  `forsMHashes_128s : … = 269839 + qs * 1950028`; `forsMHashes_openCounts128s : … = (openCounts128s qs).tcrFv ∧ … = (openCounts128s qs).dspr`.

## Closed (`SlhDsaBridgeForsClosed.lean`)
* `tcrFv_term_closed_128s (hn : 1 ≤ c.tl) (q qs) (hq) (hqs) : avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsTcr0 (q + (openCounts128s qs).tcrFv)` (= `hfv` of `composed_of_linear_eps`).
* `dspr`: not closed (no qfors `dspr` term theorem yet; `hRows` open).

## Design note
The machine records the opened FORS leaves in the closing state during signing (one extra
`H_msg` per signature), so the answer costs `1 + k` regardless of the transcript (a `PUE` budget
must hold for every state, also unreachable ones); the total equals `forsFindOpen`'s count.
Glue: `close_wrap_eq` (close ∘ wrap = close with the composite implementation), `close_map_state`.

## Name clash to note
qfors's `SlhDsaBridgeFors.lean` and my `SlhDsaBridgeTcrT.lean` both declare
`Reduction.avΩ_resample_frow` and `Reduction.encΩ_frow_local`: no file may import both.

---

# Assignment 3 — name clash, `hRows`, closed `dspr`

* Clash: in `SlhDsaBridgeTcrT.lean` the lemmas are now `tcrT_avΩ_resample_frow`,
  `tcrT_encΩ_frow_local`; the old names are kept as `alias`es because qwots's
  `SlhDsaBridgeWotsPre.lean` uses them (qfors's are now `fors_*`, so no clash). Checked: a file
  importing `SlhDsaBridgeTcrT`, `SlhDsaBridgeFors`, `SlhDsaBridgeForsClosed(2)`,
  `SlhDsaBridgeTcrClosed` elaborates; `SlhDsaBridgeWotsPre.lean` and qmach's
  `SlhDsaBridgeMachWots.lean` compile (the latter does not import `TcrT`; no recompile needed).
* `hRows` PROVED: `PQ/QROM/HybridRows.lean` (lake module `PQ.QROM.HybridRows`):
  `toSecond` (one-port program as a two-port program on port `true`), `toSecond_isQueryBound`
  (`secondBudget q`), `run_toSecond` (`twoRuntime (ports F H)` run of `toSecond x` = 
  `additiveOracleRuntime H` run of `x`), `ofProgram_rowsBound (I) (x) (ρ) (q) (hx) (dec) :
  RowsBound (fun H E ↦ ((HybridModel.ofProgram I x ρ q hx dec).prob H E).toReal) q`.
* `Integration/SlhDsaBridgeMachFors2.lean`: `forsDspr_hModel' (q qs) (hq) (hqs)` = qfors's `dspr`
  hypothesis with no further hypothesis.
* `Integration/SlhDsaBridgeForsClosed2.lean`: `dspr_term_closed_128s (hn : 1 ≤ c.tl) (q qs) (hq)
  (hqs) : avΩ c (qDsprFV_Success (qToDspr (B ω))) ≤ avΩ c (qDsprFV_SPProbability (qToDspr (B ω)))
  + epsDsprTight (q + (openCounts128s qs).dspr)` (= `hdspr` of `composed_of_linear_eps`).
