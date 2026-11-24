import Integration.SlhDsaCompressionCompileRegisters

namespace Reduction.Compression.Recording.Compile
open PQ.QROM Quantum Database MLink Ideal Classical
variable {L : LocalSig.{1,0}} (I : L.Interp) {A : QReg} (o : L.Op A)
abbrev Cells := DB Input Chain512
abbrev State (A : QReg) := Cells → Vec A

noncomputable def kraus (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit)) (v : State A) : State (L.next o b) :=
  fun d => Purify.primKraus I o b c (v d)

def sparse (t : ℕ) {A : QReg} (v : State A) := ∀ d, t < (occupied d).card → v d = 0

theorem kraus_sparse (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit)) (v : State A)
    (t : ℕ) (h : sparse t v) : sparse t (kraus I o b c v) := by
  intro d hd
  simp only [kraus,h d hd,map_zero]

set_option linter.constructorNameAsVariable false in
theorem tensor_kraus (b : L.Outcome o) (c : (L.next o b × Unit) × (A × Unit)) (v : State A) (d : Cells) :
    tensor (kraus I o b c v) d = Purify.primKraus I o b c (tensor v d) := by
  unfold tensor kraus
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact (((Purify.primKraus I o b c).restrictScalars ℝ).map_smul (coeffDB d e) (v e)).symm

/-- A finite selection of an instrument's outcomes can only lose weight.
The selection and all Kraus operators are independent of the sampled table. -/
theorem kraus_weight (v : State A) (s : Finset (L.Outcome o)) (P : Cells → Prop) :
    (∑ b ∈ s, ∑ c, sumWeight P (kraus I o b c v)) ≤ sumWeight P v := by
  classical
  unfold sumWeight
  simp only [kraus]
  have h (b : L.Outcome o) :
      (∑ c : (L.next o b × Unit) × (A × Unit), ∑ d, if P d then ‖Purify.primKraus I o b c (v d)‖^2 else 0) =
        ∑ d, if P d then ∑ c, ‖Purify.primKraus I o b c (v d)‖^2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : P d <;> simp [hd]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro d _
  by_cases hd : P d
  · simpa [hd] using Purify.prim_kraus_sum_le I o s (v d)
  · simp [hd]

end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.kraus_weight
#print axioms Reduction.Compression.Recording.Compile.tensor_kraus
