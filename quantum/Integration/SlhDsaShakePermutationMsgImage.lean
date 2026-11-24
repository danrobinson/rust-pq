import Integration.SlhDsaShakePermutationTrajectoryRisk
import Integration.SlhDsaShakeXofTcr

namespace Reduction.ShakePermutation.MsgTrajectory.Risk
open Classical SetOracle ENNReal OracleComp OracleComp.PermutationConditioning Classic
noncomputable section
variable {A : Type} [Fintype A] [DecidableEq A]

private def first_ext : (Extensions ([] : EdgeTrace A)) ≃ Equiv.Perm A :=
  ⟨Subtype.val,fun p => ⟨p,by simp⟩,fun _ => rfl,fun _ => rfl⟩

/-- The queried output may be selected after observing the image of x.
Every other specified preimage still has probability at most 1/(N-1). -/
theorem second_image (x z : A) (ne : z ≠ x) (value : A → A) :
    uniformMean (fun σ : Equiv.Perm A => if σ z = value (σ x) then (1:ℝ≥0∞) else 0) ≤
      1/((Fintype.card A-1 : ℕ):ℝ≥0∞) := by
  classical
  let test := fun (σ : Equiv.Perm A) => if σ z = value (σ x) then (1:ℝ≥0∞) else 0
  have ex : Nonempty (Extensions ([] : EdgeTrace A)) := ⟨first_ext.symm (Equiv.refl _)⟩
  let start : UnusedInputs ([] : EdgeTrace A) := ⟨x,by simp⟩
  change uniformMean test ≤ _
  rw [← Classic.mean_equiv first_ext test]
  change uniformMean (fun p : Extensions ([] : EdgeTrace A) => if p.val z = value (p.val start.val) then (1:ℝ≥0∞) else 0) ≤ _
  rw [fresh_forward [] start ex (fun y p => if p z = value y then (1:ℝ≥0∞) else 0)]
  let _ : Nonempty (UnusedOutputs ([] : EdgeTrace A)) := ⟨x,by simp⟩
  apply ShakeXof.mean_le_const
  intro y
  let t : EdgeTrace A := [(x,y.val)]
  let second : UnusedInputs t := ⟨z,by simpa [t] using ne⟩
  have ok : Nonempty (Extensions t) := extensions_cons_nonempty [] start y ex
  change uniformMean (fun p : Extensions t => if p.val second.val = value y.val then (1:ℝ≥0∞) else 0) ≤ _
  rw [fresh_forward t second ok (fun w _ => if w = value y.val then (1:ℝ≥0∞) else 0)]
  have const (w : UnusedOutputs t) :
      uniformMean (fun _ : Extensions ((second.val,w.val)::t) => if w.val = value y.val then (1:ℝ≥0∞) else 0) =
        (if w.val = value y.val then (1:ℝ≥0∞) else 0) := by
    let _ := extensions_cons_nonempty t second w ok
    simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]
  simp_rw [const]
  have r := rare (Function.Embedding.subtype (fun v : A => ∀ e ∈ t, v ≠ e.2)) {value y.val}
    (fun w => if w.val = value y.val then (1:ℝ≥0∞) else 0) 1 0
    (fun w miss => by simp [show w.val ≠ value y.val by simpa using miss]) (fun w => by split <;> simp)
  have den : Fintype.card A-1 ≤ Fintype.card (UnusedOutputs t) := by
    have h := unused_card t; have len : t.length = 1 := rfl; omega
  apply r.trans
  simp only [zero_add,Finset.card_singleton,Nat.cast_one,mul_one,one_div]
  exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr den)

end
end Reduction.ShakePermutation.MsgTrajectory.Risk
#print axioms Reduction.ShakePermutation.MsgTrajectory.Risk.second_image
