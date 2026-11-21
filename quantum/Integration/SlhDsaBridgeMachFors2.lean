import Integration.SlhDsaBridgeMachFors
import PQ.QROM.HybridRows

/-!
# The `dspr` machine model without the hypothesis `hRows`

NOT part of the default target; compiled like `scripts/check-integration.sh` step 3.

`forsDspr_hModel'`: the `dspr` hypothesis of `quantum/HANDOFF-qfors.md`, discharged with
`q' = q + forsMHashes Link.vp qs`, with NO further hypothesis: the named hypothesis `hRows` of
`forsDspr_hModel` (`Integration/SlhDsaBridgeMachFors.lean`) is `PQ.QROM.Rows.ofProgram_rowsBound`
(`PQ/QROM/HybridRows.lean`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum

set_option linter.unusedSectionVars false

namespace Reduction

section deliver2

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- **`hModel` of `qfors`, `dspr`**, discharged with `q' = q + forsMHashes Link.vp qs`. -/
theorem forsDspr_hModel' (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : Ω128 c) (st : Open.ForsP1State Link.vp (primsΩ ω₀))
      (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bool) (q + forsMHashes Link.vp qs),
        Mo.Additive ∧
        PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) (q + forsMHashes Link.vp qs) ∧
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bool → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).guess st pk) F.ρ₀ :=
  forsDspr_hModel c optRand₀ pkSeedDist₀ F q qs hq hqs
    (fun x ρ hx ↦ PQ.QROM.Rows.ofProgram_rowsBound _ x ρ _ hx Sigma.snd)

end deliver2

end Reduction

#print axioms Reduction.forsDspr_hModel'
