# HANDOFF — agent `qwots` (WOTS-chain UD and PRE terms)

Status: DONE, both terms, open and closed forms. All results `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`axiom`/`native_decide`. Nothing committed. No existing file edited.

## Deliverables (feed `composed_of_linear_eps` directly; do not need `BridgesRest10.ud/.pre`)

Closed (only `hq`, `hqs`, `35 ≤ c.tl` remain), `Integration/SlhDsaBridgeWotsClosed.lean`:
```lean
theorem pre_closed (q qs : ℕ) (htl : 35 ≤ c.tl)                       -- :36
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avΩ c (fun ω ↦ qSM_DT_PRE_Advantage (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      epsPre0 (q + (openCounts128s qs).pre)
theorem ud_closed (q qs : ℕ) (htl : 35 ≤ c.tl) (hq …) (hqs …) :         -- :67
    avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) +
        epsUdTight (q + (openCounts128s qs).ud)
```
Use: `composed_of_linear_eps … (hud := ud_closed c optRand₀ pkSeedDist₀ F q qs htl hq hqs)
(hpre := pre_closed c optRand₀ pkSeedDist₀ F q qs htl hq hqs)` with `eUd`, `ePre` as above
(type-checked in `scratch/qwots/PlugTest.lean`).

Open forms (machine model as the only non-forger hypothesis):
* `Integration/SlhDsaBridgeWotsPre.lean:143` `pre_term (hn : 1 ≤ c.tl) q' hModel : … ≤ epsPre0 q'`;
  `:190` `pre_term_hpre q r htl hModel : … ≤ epsPre0 (q + r.pre)`.
* `Integration/SlhDsaBridgeWotsUd.lean:121` `ud_term hn q' hTight`; `:184` `ud_term_hud q r htl hTight`
  (`… ≤ … + epsUdTight (q + r.ud)`).

## Hypotheses consumed
* PRE `hModel`: exactly the shape of `wotsPre_hModel` (`SlhDsaBridgeMachWots.lean:370`): `∀ ω₀ st pk,
  ∃ Mo : HybridModel (EncX c) EncY (ℕ × Bytes n) q', ∀ T Ev, Mo.prob (encΩ {ω₀ with thash := T}) Ev =
  qWeight Ev ((qrPre (internalΩ … {ω₀ with thash := T})).invert st pk) F.ρ₀`.
* UD `hTight` (NOT a `HybridModel`: that only yields `4q'/2^64`, not `epsUdTight`):
  `∀ ω₀ st pk, ∃ f : (EncX c → EncY) → ℝ≥0∞, PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) q' ∧
  ∀ T, f (encΩ {ω₀ with thash := T}) = qWeight (· = true) ((qrUd (…)).distinguish st pk) F.ρ₀`.
  Discharged in `SlhDsaBridgeWotsClosed.lean:46` (`wotsUd_hTight`) from `wotsUd_mach_exists`,
  `PUE.exists_prog_qprob`, `Tight.qprob_tightAvgBound`.

## New modules
* lake: `PQ.Interactive.QromBridgeWotsPre` (lazy sampling `pre_run_plant` :531, relabelling, generic
  `pre_row_avg_le` :688), `PQ.Interactive.QromBridgeWotsUd` (`ud_run_plant` :315, `udPlant_congr`,
  `ud_row_avg_le` :375), `PQ.QROM.WotsPullbackUdTight` (`ud_tight_obs_real_le_ideal_add` :38, tight UD
  with observations/weights via `tight_view_of`; `wq_tightAvgBound_pullback` :145). Built with
  `lake build <target>`; to add to `PQ.lean`.
* Integration (compile in this order): `SlhDsaBridgeWotsRow` (own copies, `wq`-prefixed, of the F-row
  machinery; no dependence on `qtcr`'s files), `SlhDsaBridgeWotsPre`, `SlhDsaBridgeWotsUd`,
  `SlhDsaBridgeWotsClosed` (imports `SlhDsaBridgeMachWots`).

## Notes
* Arbitrary `pkSeedDist₀`; first phases via `Open.prePhase1`/`Open.udPhase1` (kernel `rfl`).
* The collection oracle (whole `Thash`) is handled: queries at requested tweaks have probability 0
  of reaching the output (reachable-state extension lemmas), others read other rows / are background.
* Not independently audited; full `check-integration.sh` not run.
