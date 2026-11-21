# HANDOFF — agent `qfors` (game side of the two FORS-leaf terms `tcrFv`, `dspr`)

Status: DONE (game side). Both term inequalities compiled, `[propext, Classical.choice, Quot.sound]`,
each with ONE non-forger hypothesis `hModel` (the machine model). Nothing committed; no existing
file edited.

## New modules (coordinator: add to the build)
| file | kind | build |
|---|---|---|
| `PQ/QROM/ForsPullback.lean` | lake module `PQ.QROM.ForsPullback` (add to `PQ.lean`) | `lake build PQ.QROM.ForsPullback` OK |
| `PQ/Interactive/QromBridgeFors.lean` | lake module `PQ.Interactive.QromBridgeFors` (add to `PQ.lean`) | `lake build PQ.Interactive.QromBridgeFors` OK |
| `Integration/SlhDsaBridgeFors.lean` | Integration (imports `Integration.SlhDsaBridgeTcr` of `qtcr`, `Reduction.Open.Phase1Fors`, `PQ.Interactive.QromBridgeFors`) | olean written |
| `Integration/SlhDsaBridgeForsDspr.lean` | Integration (imports the above, `PQ.QROM.ForsPullback`) | olean written |

Compile order: `SlhDsaBridgeTcr` → `SlhDsaBridgeFors` → `SlhDsaBridgeForsDspr`.
(`Integration/SlhDsaBridgeForsClosed.lean` is NOT mine — written by another agent; it closes
`tcrFv` with `forsTcr_hModel`. I recompiled `SlhDsaBridgeFors.olean` after it was written, so
recompile `SlhDsaBridgeForsClosed` too.)

## Headlines (section variables `c optRand₀ pkSeedDist₀ F` as in `SlhDsaBridgePrf.lean`)

`Integration/SlhDsaBridgeFors.lean:185`
```lean
theorem tcrFv_term (hn : 1 ≤ c.tl) (q' : ℕ) (hModel : <tcrFv hypothesis below>) :
    avΩ c (fun ω ↦ qTcrFV_Advantage (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      epsTcr0 q'
```
`Integration/SlhDsaBridgeForsDspr.lean:210`
```lean
theorem dspr_term (hn : 1 ≤ c.tl) (q' : ℕ) (hModel : <dspr hypothesis below>) :
    avΩ c (fun ω ↦ qDsprFV_Success (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      avΩ c (fun ω ↦ qDsprFV_SPProbability
        (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) + epsDsprTight q'
```
These are exactly `hfv` / `hdspr` of `composed_of_linear_eps` at `q' = q + r.tcrFv` / `q + r.dspr`:
checked by compiling `scratch/qfors/Plug.lean` (the `…_qrom_enc2msg` proof with
`(dspr_term c optRand₀ pkSeedDist₀ F (by omega) _ hMd)` and
`(tcrFv_term c optRand₀ pkSeedDist₀ F (by omega) _ hMfv)` in place of `hb.dspr.le …`,
`hb.tcrFv.le …`; `1 ≤ c.tl` from `35 ≤ c.tl`). `scratch/qfors/Plug2.lean` checks
`dspr_term … (forsDspr_hModel … hRows)` (`Integration/SlhDsaBridgeMachFors.lean`), i.e. the dspr
term closed except for `hRows`.

## Hypothesis consumed

`Open.ForsP1State Link.vp (primsΩ ω₀)` (`security/Reduction/Open/Phase1Fors.lean`) is the `State`
of `qToTcr`/`qToDspr` (`rfl`), independent of `thash`.

### `tcrFv` (shape of `tcr_hModel`; output type `ℕ × Bytes n`)
```lean
(hModel : ∀ (ω₀ : Ω128 c) (st : Open.ForsP1State Link.vp (primsΩ ω₀))
    (pk : Bytes Link.vp.params.n),
    ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n) q',
      ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
          Bytes Link.vp.params.n)
        (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
        Mo.prob (encΩ { ω₀ with thash := T }) Ev =
          qWeight Ev ((qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
            { ω₀ with thash := T })).forge st pk) F.ρ₀)
```
Discharged by `forsTcr_hModel` (`Integration/SlhDsaBridgeMachFors.lean:562`, not mine) at
`q' = q + forsMHashes Link.vp qs = q + (openCounts128s qs).tcrFv`.

### `dspr` (output type `ℕ × Bool`; the TIGHT bound needs two more properties of the model)
```lean
(hModel : ∀ (ω₀ : Ω128 c) (st : Open.ForsP1State Link.vp (primsΩ ω₀))
    (pk : Bytes Link.vp.params.n),
    ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bool) q',
      Mo.Additive ∧
      PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) q' ∧
      ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
          Bytes Link.vp.params.n)
        (Ev : ℕ × Bool → Prop) [DecidablePred Ev],
        Mo.prob (encΩ { ω₀ with thash := T }) Ev =
          qWeight Ev ((qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
            { ω₀ with thash := T })).guess st pk) F.ρ₀)
```
* `Mo.Additive` (`PQ/QROM/DsprGiven.lean:158`) holds for `ofProgram` models
  (`HybridModel.ofProgram_additive`).
* `RowsBound` (`PQ/QROM/ExactDsprTightGame.lean:42`) is PROVED only for `ofSecondPort` models of
  two-port programs (`ofSecondPort_rowsBound`, same file `:52`), NOT for `ofProgram` models of
  one-port programs (what `PUE.exists_prog_qprob` gives). `forsDspr_hModel` therefore takes the
  named hypothesis `hRows` ("`RowsBound` for every `HybridModel.ofProgram` model of a one-port
  program with `q'` queries").

## How (short)
* Generic (`PQ/Interactive/QromBridgeFors.lean`): source-final-validity game at the empty
  collection. `fv_run_ext` (`:111`: challenge history only grows; a valid final state comes from a
  valid state through fresh distinct tweaks), `fv_run_prob_congr` (`:139`: probability of ending
  in a VALID state containing `(t₀, m₀)` unchanged when the hash changes at `(t₀, m)`, `m ≠ m₀`:
  a second challenge at `t₀` poisons validity). `tcrFv_row_avg_le` (`:225`):
  `spr_embedded_obs_weighted_le` per first-phase output; invalid outputs weigh 0.
  `dsprFv_row_avg_le` (`:434`): `markLaw_of_obs` + `dspr_embedded_tight` per output, `g = 0` from
  `Tight.pow_noSP_le_half'` (`2 ≤ |Y| ≤ |M|`, here `|Y| = |M| = 2^128`); real-to-`ℝ≥0∞` via
  `ennreal_le_add_of_toReal`. Seed decompositions `qTcrFV_Advantage_eq_tsum`,
  `qDsprFV_Success_eq_tsum`, `qDsprFV_SPProbability_eq_tsum` (any seed distribution).
* `PQ/QROM/ForsPullback.lean`: `HybridModel.Additive.pullback` (`:33`), `RowsBound.pullback`
  (`:166`): the rows bound survives `HybridModel.pullback` along a local map of oracles (mark
  probabilities extended by `0`, rows by a constant; patterns of positive weight vanish off the
  range).
* Integration: row of `F` = arity-one `Thash` row at `pk`, indexed by `Bytes 22 × BN`
  (`frowEquiv`, reuses `qtcr`'s `thRowT`, `avΩ_resample_row`, `thRowEmb`, `encΩ_row_local`);
  first phase = `Open.forsPhase1` (`Open.toTcr_choose_eq`/`toDspr_choose_eq` + kernel `rfl`,
  `qtcr_kernel_rfl`); the game oracles at the resampled world are kernel-`rfl` equal to those of
  `fvWithEval (forsTcrProblem … ω) (row)` (the DSPR-FV oracles are the TCR-FV ones).

## Not done / next
* `hRows` (for `dspr`): prove `RowsBound` for `HybridModel.ofProgram` models. Route: relabel a
  `qromSpec X Y` program as a `qrom2Spec X Y` program querying only port `true` (structural map of
  VCVio's `IFreeM`, as `liftTraversal` in `VCVio/Quantum/Comp/Lift.lean`), show
  `IsQueryBound (secondBudget q)`, `leafProb (twoRuntime (ports F H)) I x₂ (ρ ⊗ |()⟩⟨()|) E =
  qprob I H x ρ E` (both runtimes apply `oracleQuery H` framed by `Unit`), then
  `ofSecondPort_rowsBound`. No VCVio relabelling combinator exists. Not attempted.
* Not independently audited. Full `scripts/check-integration.sh` not run.

---

# Assignment 2 — the closed composed headline (DONE)

## Headlines (`Integration/SlhDsaComposedClosed.lean`), hypotheses on the forger only
```lean
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed
    (F : PortForger (EncX c) EncY E) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (htl : 35 ≤ c.tl) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs (openCounts128s qs).noPrfMsg
```
EUF: `slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc_closed`, identical with `qUnforgeableAdvantage`.
Count record `(openCounts128s qs).noPrfMsg`: forced by `prf_term_*`/`msg_term_*` (charged `q`,
i.e. `prf = msg = 0`); every other field is `openCounts128s qs`'s, which is what the closed term
theorems state (`q + (openCounts128s qs).<term>`; `.noPrfMsg.<term>` reduces to it by `rfl`).
Name: `…_qrom_closed` is TAKEN by the old bridge-conditional theorems in
`Integration/SlhDsaComposedFinal.lean:697/:712` (imported transitively) → `…_qrom_enc_closed`.

Terms used: `prf_term_suf/euf` + `QInd.prf…_withPrf`, `QMsg.msg_term_suf/euf`, `itsr_closed`,
`dspr_term_closed_128s`, `tcrFv_term_closed_128s`, `tcr_terms_closed_128s`, `ud_closed`,
`pre_term_closed_128s` (mine: `pre_term` + `wotsPre_hModel`; `pre_closed` is equivalent),
`tcrT_term_closed_128s` (mine, `Integration/SlhDsaBridgeTcrTClosed.lean`).

## Numeric (`Integration/SlhDsaComposedClosedNum.lean`)
* `Num.composedBoundFinal_num : composedBoundFinal (2^40) (2^20) (openCounts128s (2^20)).noPrfMsg ≤ (2^22)⁻¹`.
* `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc_closed_num`: forgery probability `≤ 2^-22`
  for every port forger with `≤ 2^40` port calls and `≤ 2^20` signing queries (+ `hcap`, `htl`).
* Bounds: ITSR `≤ (2^-40 + 6·2^-14)²` (cover sum `≤ 2·2^-168`: `cover_sum_le`), each of the 27
  weighted other terms `≤ 2^-37`. The true value is ≈ `2^-22.9` (ITSR reprogramming term), so
  `k = 22` is the best integer exponent.

## Compile order (Integration, all oleans present and not stale by mtime)
`SlhDsaBridgeTcr → SlhDsaBridgeMach → SlhDsaBridgeTcrClosed → SlhDsaBridgeFors → SlhDsaBridgeMachFors
→ SlhDsaBridgeForsClosed → SlhDsaBridgeForsDspr → SlhDsaBridgeMachFors2 → SlhDsaBridgeForsClosed2
→ SlhDsaBridgeTcrT → SlhDsaBridgeMachWots → SlhDsaBridgeTcrTClosed → SlhDsaBridgeWotsRow
→ SlhDsaBridgeWotsPre → SlhDsaBridgeWotsUd → SlhDsaBridgeWotsClosed → SlhDsaBridgeMachItsr
→ SlhDsaBridgeItsr → SlhDsaBridgeItsrD → SlhDsaBridgeMachItsr2 → SlhDsaComposedClosed
→ SlhDsaComposedClosedNum` (after the existing chain up to `SlhDsaComposedEnc2Msg`).
PQ lake modules imported by this chain and NOT in `PQ.lean`: `PQ.Interactive.QromBridgeEvalIAdv`,
`QromBridgeEvalProg`, `QromBridgeEvalQ`, `QromBridgeFors`, `QromBridgeTcr`, `QromBridgeWotsPre`,
`QromBridgeWotsUd`, `PQ.QROM.ForsPullback`, `PQ.QROM.HybridRows`, `PQ.QROM.ItsrPullback`.
