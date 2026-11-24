import Integration.SlhDsaShakePermutationMsgHonest

namespace Reduction.ShakePermutation.MsgTrajectory
open Classical MLink SLHDSA SetOracle ENNReal OracleComp OracleComp.PermutationConditioning Classic
noncomputable section
set_option maxRecDepth 8192

local instance singletonFintype {B : Type} [Fintype B] [DecidableEq B] (x s : B) : Fintype (Extensions [(x,s)]) := inferInstance
variable {A : Type} [Fintype A] [DecidableEq A]

private def emptyExt : Extensions ([] : EdgeTrace A) ≃ Equiv.Perm A :=
  ⟨Subtype.val,fun p => ⟨p,by simp⟩,fun _ => rfl,fun _ => rfl⟩
private def unusedEmpty : UnusedOutputs ([] : EdgeTrace A) ≃ A :=
  ⟨Subtype.val,fun x => ⟨x,by simp⟩,fun _ => rfl,fun _ => rfl⟩

theorem conditioned_image (x : A) (W : A → Equiv.Perm A → ℝ≥0∞) :
    uniformMean (fun σ : Equiv.Perm A => W (σ x) σ) =
      uniformMean (fun s : A => uniformMean (fun σ : Extensions [(x,s)] => W s σ.val)) := by
  let i : UnusedInputs ([] : EdgeTrace A) := ⟨x,by simp⟩
  let ok : Nonempty (Extensions ([] : EdgeTrace A)) := ⟨emptyExt.symm (Equiv.refl _)⟩
  exact ((mean_equiv emptyExt (fun σ => W (σ x) σ)).symm.trans (fresh_forward [] i ok W)).trans
    (mean_equiv unusedEmpty (fun s => uniformMean (fun σ : Extensions [(x,s)] => W s σ.val)))

/-- Under a fixed first image, any other designated input hits a fixed
output with probability at most 1/(N-1), uniformly in the first image. -/
theorem conditioned_second (x s z y : A) (ne : z ≠ x) :
    uniformMean (fun π : Extensions [(x,s)] => if π.val z = y then (1:ℝ≥0∞) else 0) ≤
      1/((Fintype.card A-1 : ℕ):ℝ≥0∞) := by
  let t : EdgeTrace A := [(x,s)]
  let i : UnusedInputs t := ⟨z,by simpa [t] using ne⟩
  let ok : Nonempty (Extensions t) := ⟨Equiv.swap x s,by simp [t]⟩
  change uniformMean (fun π : Extensions t => if π.val i.val = y then (1:ℝ≥0∞) else 0) ≤ _
  rw [fresh_forward t i ok (fun w _ => if w = y then (1:ℝ≥0∞) else 0)]
  have const (w : UnusedOutputs t) :
      uniformMean (fun _ : Extensions ((i.val,w.val)::t) => if w.val = y then (1:ℝ≥0∞) else 0) =
        (if w.val = y then (1:ℝ≥0∞) else 0) := by
    let _ := extensions_cons_nonempty t i w ok
    simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]
  simp_rw [const]
  have r := Risk.rare (Function.Embedding.subtype (fun v : A => ∀ e ∈ t, v ≠ e.2)) {y}
    (fun w => if w.val = y then (1:ℝ≥0∞) else 0) 1 0
    (fun w miss => by simp [show w.val ≠ y by simpa using miss]) (fun w => by split <;> simp)
  have den : Fintype.card A-1 ≤ Fintype.card (UnusedOutputs t) := by
    have h := unused_card t; have len : t.length = 1 := rfl; omega
  apply r.trans
  simp only [zero_add,Finset.card_singleton,Nat.cast_one,mul_one,one_div]
  exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr den)


variable (S : Sha2Set)

def firstState (π : Permutation) (bs : List Rate) (r : S.Node) (tail : SkFormat.Suffix S) : Words :=
  (suffix π bs).symm ((SkFormat.split S).symm (r,tail))

/-- Exact posterior sampler for the auxiliary permutation, given the
truncated terminal output. The message may be fixed after a public query
phase. The test can inspect the entire auxiliary permutation. -/
theorem conditioned_output (π : Permutation) (bs : List Rate) (x : Words)
    (W : S.Node → Permutation → ℝ≥0∞) :
    uniformMean (fun σ : Permutation => W (SkFormat.split S (suffix π bs (σ x))).1 σ) =
      uniformMean (fun r : S.Node => uniformMean (fun tail : SkFormat.Suffix S =>
        uniformMean (fun σ : Extensions [(x,firstState S π bs r tail)] => W r σ.val))) := by
  let e := (suffix π bs).trans (SkFormat.split S)
  let test := fun s : Words => uniformMean (fun σ : Extensions [(x,s)] => W (e s).1 σ.val)
  apply (conditioned_image x (fun s σ => W (e s).1 σ)).trans
  change uniformMean test = _
  rw [← mean_equiv e.symm test,Classic.mean_prod]
  apply congrArg uniformMean; funext r
  apply congrArg uniformMean; funext tail
  change uniformMean (fun σ : Extensions [(x,e.symm (r,tail))] => W (e (e.symm (r,tail))).1 σ.val) = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem avg_mono {B : Type} [Fintype B] {f g : B → ℝ≥0∞} (h : ∀ b, f b ≤ g b) :
    uniformMean f ≤ uniformMean g := Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (h b)

private theorem avg_const {B : Type} [Fintype B] [Nonempty B] (c : ℝ≥0∞) : uniformMean (fun _ : B => c) = c := by
  simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]

private theorem avg_add {B : Type} [Fintype B] (f g : B → ℝ≥0∞) :
    uniformMean (fun b => f b+g b) = uniformMean f+uniformMean g := by
  simp only [uniformMean,mul_add,Finset.sum_add_distrib]

/-- An inverse address hits a programmed new image with small probability
even after the terminal truncated output has been revealed. -/
theorem posterior_target {J : Type} [Fintype J] (u : J ↪ Words) (π : Permutation)
    (bs : List Rate) (r : S.Node) (x a : Words) :
    uniformMean (fun tail : SkFormat.Suffix S =>
      uniformMean (fun σ : Extensions [(x,firstState S π bs r tail)] =>
        if ∃ j, σ.val (u j) = a then (1:ℝ≥0∞) else 0)) ≤
      1/(Fintype.card (SkFormat.Suffix S):ℝ≥0∞) + Fintype.card J*(1/((Fintype.card Words-1:ℕ):ℝ≥0∞)) := by
  classical
  let e : SkFormat.Suffix S ↪ Words := {
    toFun := firstState S π bs r
    inj' := fun _ _ h => congrArg Prod.snd ((SkFormat.split S).symm.injective ((suffix π bs).symm.injective h)) }
  let D := (Fintype.card J : ℝ≥0∞)*(1/((Fintype.card Words-1:ℕ):ℝ≥0∞))
  let inner (s : Words) := uniformMean (fun σ : Extensions [(x,s)] =>
    if ∃ j, σ.val (u j) = a then (1:ℝ≥0∞) else 0)
  have one (s) : inner s ≤ (if s = a then (1:ℝ≥0∞) else 0)+D := by
    let _ : Nonempty (Extensions [(x,s)]) := ⟨Equiv.swap x s,by simp⟩
    by_cases eq : s = a
    · rw [ite_eq_left eq]
      exact (ShakeXof.mean_le_const (fun _ => by split <;> simp)).trans (le_self_add : (1:ℝ≥0∞) ≤ 1+D)
    · rw [ite_eq_right eq,zero_add]
      apply Risk.union_avg (fun (σ : Extensions [(x,s)]) j => σ.val (u j) = a)
      intro j
      by_cases same : u j = x
      · have miss (σ : Extensions [(x,s)]) : σ.val (u j) ≠ a := by
          rw [same,show σ.val x = s from σ.property (x,s) (by simp)]; exact eq
        simp only [ite_eq_right (miss _),uniformMean,mul_zero,Finset.sum_const_zero,zero_le]
      · exact conditioned_second x s (u j) a same
  have outer := Risk.rare e {a} (fun t => if e t = a then (1:ℝ≥0∞) else 0) 1 0
    (fun t out => by simp [show e t ≠ a by simpa using out]) (fun _ => by split <;> simp)
  have bound : uniformMean (fun t => if e t = a then (1:ℝ≥0∞) else 0) ≤ 1/Fintype.card (SkFormat.Suffix S) := by
    simpa only [zero_add,Finset.card_singleton,Nat.cast_one,mul_one] using outer
  change uniformMean (fun t => inner (e t)) ≤ _
  apply (avg_mono (fun t => one (e t))).trans
  rw [avg_add,avg_const]
  exact add_le_add bound le_rfl

end
end Reduction.ShakePermutation.MsgTrajectory
#print axioms Reduction.ShakePermutation.MsgTrajectory.conditioned_output
#print axioms Reduction.ShakePermutation.MsgTrajectory.posterior_target
