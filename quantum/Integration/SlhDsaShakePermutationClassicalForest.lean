import Integration.SlhDsaShakePermutationClassicalLazy

/-! Fresh-capacity sampling on a classical permutation transcript. The
forest records both directions of a public edge. Every new image or
preimage attaches a previously unused capacity vertex. -/
namespace Reduction.ShakePermutation.Classic
open OracleComp OracleSpec PermutationConditioning Classical
open scoped ENNReal
open SetOracle (uniformMean)
noncomputable section

theorem mean_select {A : Type} [Fintype A] [Nonempty A] (g : A → Prop) [DecidablePred g]
    (f : A → ℝ≥0∞) (bounded : ∀ a, f a ≤ 1) :
    uniformMean f ≤ uniformMean (fun x : {a // g a} => f x.val) +
      (Fintype.card {a // ¬g a} : ℝ≥0∞) / (Fintype.card A : ℝ≥0∞) := by
  have part := Fintype.sum_subtype_add_sum_subtype g (fun a => unifW A a * f a)
  change ∑ a, unifW A a * f a ≤ _
  rw [← part]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro a _
    exact mul_le_mul' (ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Fintype.card_subtype_le g))) le_rfl
  · calc
      _ ≤ ∑ _ : {a // ¬g a}, (Fintype.card A : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum fun x _ => (mul_le_mul' le_rfl (bounded x.val)).trans_eq (mul_one _)
      _ = _ := by simp [div_eq_mul_inv,nsmul_eq_mul]

def usedOut {A : Type} [DecidableEq A] (t : EdgeTrace A) : Finset A := (t.map Prod.snd).toFinset
def unusedEquiv {A : Type} [DecidableEq A] (t : EdgeTrace A) : UnusedOutputs t ≃ {y // y ∉ usedOut t} where
  toFun y := ⟨y.val,by intro h; obtain ⟨a,ha,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp h); exact y.property a ha eq.symm⟩
  invFun y := ⟨y.val,by intro a ha eq; exact y.property (List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,eq.symm⟩))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem unused_card {A : Type} [Fintype A] [DecidableEq A] (t : EdgeTrace A) :
    Fintype.card A ≤ Fintype.card (UnusedOutputs t) + t.length := by
  rw [Fintype.card_congr (unusedEquiv t),Fintype.card_subtype_compl]
  have he : Fintype.card {y // y ∈ usedOut t} = (usedOut t).card := Fintype.card_coe _
  have h := List.toFinset_card_le (t.map Prod.snd)
  simp only [List.length_map] at h
  rw [he]
  change _ ≤ _ + _
  unfold usedOut
  omega

variable {A C R : Type} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] [Fintype R]
variable (split : A ≃ R × C) (root : C)

def forbidden (t : EdgeTrace A) (x : A) : Finset C := insert root (insert (split x).2
    ((t.map (fun e => (split e.1).2)).toFinset ∪ (t.map (fun e => (split e.2).2)).toFinset))

omit [Fintype A] [DecidableEq A] [Fintype C] [Fintype R] in
theorem forbidden_card (t : EdgeTrace A) (x : A) : (forbidden split root t x).card ≤ 2*t.length+2 := by
  unfold forbidden
  calc
    _ ≤ _ := Finset.card_insert_le ..
    _ ≤ _ := Nat.add_le_add_right (Finset.card_insert_le ..) 1
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le ..) 1) 1
    _ ≤ _ := by
      have h := List.toFinset_card_le (t.map (fun e => (split e.1).2))
      have j := List.toFinset_card_le (t.map (fun e => (split e.2).2))
      simp only [List.length_map] at h j
      omega

private theorem bad_card (t : EdgeTrace A) (d : Bool) (x : A) :
    Fintype.card {y : UnusedOutputs (orient d t) // ¬ (split y.val).2 ∉ forbidden split root t x} ≤
      Fintype.card R * (2*t.length+2) := by
  let B := forbidden split root t x
  let f (y : {y : UnusedOutputs (orient d t) // ¬ (split y.val).2 ∉ B}) :
      R × {c // c ∈ B} := ((split y.val.val).1,⟨(split y.val.val).2,Classical.byContradiction y.property⟩)
  have hf : Function.Injective f := by
    intro a b e
    apply Subtype.ext
    apply Subtype.ext
    apply split.injective
    apply Prod.ext
    · exact congrArg (fun z : R × {c // c ∈ B} => z.1) e
    · exact congrArg (fun z : R × {c // c ∈ B} => z.2.val) e
  have small := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod,Fintype.card_coe] at small
  exact small.trans (Nat.mul_le_mul_left _ (forbidden_card split root t x))

/-- Capacity freshness cost per new forward or inverse query, before
using the fact that the current transcript is short. -/
theorem fresh_filter (t : EdgeTrace A) (d : Bool) (x : A) (hx : ¬old t d x)
    (ok : Nonempty (Extensions t)) (f : A → ℝ≥0∞) (hf : ∀ a, f a ≤ 1) :
    uniformMean (fun y : UnusedOutputs (orient d t) => f y.val) ≤
      uniformMean (fun z : {y : UnusedOutputs (orient d t) // (split y.val).2 ∉ forbidden split root t x} => f z.val.val) +
      (Fintype.card R * (2*t.length+2) : ℕ) / (Fintype.card (UnusedOutputs (orient d t)) : ℝ≥0∞) := by
  have t' : Nonempty (Extensions (orient d t)) := by
    cases d
    · exact ok
    · exact ok.map (inverseExtensionsEquiv t)
  let _ := unusedOutputs_nonempty _ (⟨x,by
    rintro ⟨u,v⟩ he rfl
    exact hx ⟨v,he⟩⟩ : UnusedInputs (orient d t)) t'
  apply (mean_select (fun y : UnusedOutputs (orient d t) => (split y.val).2 ∉ forbidden split root t x) _ (fun y => hf y.val)).trans
  apply add_le_add le_rfl
  rw [div_eq_mul_inv,div_eq_mul_inv]
  exact mul_le_mul' (Nat.cast_le.mpr (bad_card split root t d x)) le_rfl

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.fresh_filter
