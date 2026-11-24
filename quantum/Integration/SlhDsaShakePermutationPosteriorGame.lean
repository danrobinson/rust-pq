import Integration.SlhDsaShakePermutationMsgPosterior
import Integration.SlhDsaShakePermutationColumnGame

namespace Reduction.ShakePermutation.Program
open Classical Quantum PQ.Interactive PQ.QROM ENNReal SetOracle
open scoped Kronecker ComplexOrder
noncomputable section
variable {I X Y E : Type} [Fintype I] [Nonempty I] [DecidableEq I]
  [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E]

/-- Tight query comparison from a bound on the conditional probability
that a public address is affected, uniformly over coherent addresses. -/
theorem average_game (base : X → Y) (g : I → X → Y) (bad : I → X → Prop) [DecidableRel bad]
    (ε : ℝ≥0∞) (finite : ε ≠ ⊤)
    (risk : ∀ p, uniformMean (fun i => if bad i p then (1:ℝ≥0∞) else 0) ≤ ε)
    (keep : ∀ i p, ¬bad i p → g i p = base p)
    (M : (X → Y) → Closed (WS X Y E) Bool) (q : ℕ)
    (hq : PUE (spec:=unifSpec) cnt0 M q) (ρ : SubState ((X × Y) × E)) :
    let w := fun H => qWeight (· = true) (M H) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
    uniformMean (fun i => w (g i)) ≤ w base + ENNReal.ofReal (8*(q:ℝ)^2*ε.toReal) := by
  classical
  let keys (p : X) := Finset.univ.filter fun i => bad i p
  obtain ⟨p,_,eq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset X) Finset.univ_nonempty (fun p => (keys p).card)
  have count (x : X) : (keys x).card ≤ (keys p).card :=
    eq ▸ Finset.le_sup (f:=fun v => (keys v).card) (Finset.mem_univ x)
  have clean (i) (x) (miss : i ∉ keys x) := keep i x (fun h => miss (by simp [keys,h]))
  have h := bounded_overlap_game base g keys _ count clean M q hq ρ
  have mass : ((keys p).card : ℝ≥0∞)/Fintype.card I ≤ ε := by
    convert! risk p using 1
    simp [keys,uniformMean,unifW,mul_ite,Finset.sum_ite_irrel,div_eq_mul_inv,nsmul_eq_mul]
  apply h.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [ENNReal.toReal_div,ENNReal.toReal_natCast] using ENNReal.toReal_mono finite mass

end
end Reduction.ShakePermutation.Program
#print axioms Reduction.ShakePermutation.Program.average_game
