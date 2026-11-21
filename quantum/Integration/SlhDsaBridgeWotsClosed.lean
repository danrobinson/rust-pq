import Integration.SlhDsaBridgeWotsPre
import Integration.SlhDsaBridgeWotsUd
import Integration.SlhDsaBridgeMachWots

/-!
# The WOTS-chain PRE and UD terms, closed (machine models plugged in)

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

* `pre_closed`: `hpre` of `composed_of_linear_eps` at `ePre = epsPre0 (q + (openCounts128s qs).pre)`,
  from `pre_term_hpre` (game side) and `wotsPre_hModel` + `qmWotsPreHashes_openCounts128s`
  (machine side, `Integration/SlhDsaBridgeMachWots.lean`).
* `ud_closed`: `hud` at `eUd = epsUdTight (q + (openCounts128s qs).ud)`, from `ud_term_hud` and
  the tight bound of the distinguisher machine: `wotsUd_mach_exists` (the `PUE` family),
  `PUE.exists_prog_qprob` (one VCVio program for all port functions) and
  `PQ.QROM.Tight.qprob_tightAvgBound` (every VCVio program has the tight hidden-set bound).

Only the forger hypotheses `hq`, `hqs` and the cap `35 ≤ c.tl` remain.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

set_option linter.unusedSectionVars false

namespace Reduction

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- **PRE term, closed.** -/
theorem pre_closed (q qs : ℕ) (htl : 35 ≤ c.tl)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avΩ c (fun ω ↦ qSM_DT_PRE_Advantage
      (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      epsPre0 (q + (openCounts128s qs).pre) := by
  have h := wotsPre_hModel c optRand₀ pkSeedDist₀ F q qs hq hqs
  rw [qmWotsPreHashes_openCounts128s] at h
  exact pre_term_hpre c optRand₀ pkSeedDist₀ F q (openCounts128s qs) htl h

/-- The tight hidden-set bound of the UD distinguisher (machine side, from the `PUE` family). -/
theorem wotsUd_hTight (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : Ω128 c) (st : Open.RState Link.vp (primsΩ ω₀)) (pk : Bytes Link.vp.params.n),
      ∃ f : (EncX c → EncY) → ℝ≥0∞,
        PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) (q + (openCounts128s qs).ud) ∧
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n),
          f (encΩ { ω₀ with thash := T }) =
            qWeight (· = true) ((qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).distinguish st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mach, hP, hE⟩ := wotsUd_mach_exists c optRand₀ pkSeedDist₀ F ω₀ st pk q qs hq hqs
  rw [qmWotsUdHashes_openCounts128s] at hP
  obtain ⟨x, hx, hxe⟩ := hP.exists_prog_qprob
  refine ⟨fun H ↦ PQ.QROM.qprob LocalSig.Interp.instruments H x ρ (fun p ↦ p.2 = true),
    PQ.QROM.Tight.qprob_tightAvgBound LocalSig.Interp.instruments x ρ _ hx _, fun T ↦ ?_⟩
  show PQ.QROM.qprob LocalSig.Interp.instruments _ x ρ (fun p ↦ p.2 = true) = _
  rw [hxe (· = true) _ ρ, hE, hρ]

/-- **UD term, closed.** -/
theorem ud_closed (q qs : ℕ) (htl : 35 ≤ c.tl)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avΩ c (fun ω ↦ qSM_DT_UD_RealSuccess
      (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      avΩ c (fun ω ↦ qSM_DT_UD_IdealSuccess
        (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) +
        epsUdTight (q + (openCounts128s qs).ud) :=
  ud_term_hud c optRand₀ pkSeedDist₀ F q (openCounts128s qs) htl
    (wotsUd_hTight c optRand₀ pkSeedDist₀ F q qs hq hqs)

end inst

end Reduction

#print axioms Reduction.pre_closed
#print axioms Reduction.wotsUd_hTight
#print axioms Reduction.ud_closed
