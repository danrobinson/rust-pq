import Integration.SlhDsaShakePermutationClassicalForest

namespace Reduction.ShakePermutation.Classic
open OracleComp OracleSpec PermutationConditioning Classical PQ.Interactive
open scoped ENNReal
open SetOracle (uniformMean)
noncomputable section
variable {A C R Z : Type} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] [Fintype R]
variable (split : A ≃ R × C) (root : C)

def forestStep (t : EdgeTrace A) (d : Bool) (x : A) (k : A → EdgeTrace A → ℝ≥0∞) : ℝ≥0∞ :=
  if h : old t d x then k h.choose t else
    uniformMean fun y : {z : UnusedOutputs (orient d t) // (split z.val).2 ∉ forbidden split root t x} =>
      k y.val.val (edge d x y.val.val :: t)

def forest (ev : Z → ℝ≥0∞) (P : OracleComp (TwoWay A) Z) : EdgeTrace A → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => EdgeTrace A → ℝ≥0∞) (fun z _ => ev z) (fun i _ k t => match i with
    | .inl _ => uniformMean fun r => k r t
    | .inr (d,x) => forestStep split root t d x k) P

private theorem avg_le {U : Type} [Fintype U] {f : U → ℝ≥0∞} {b : ℝ≥0∞} (h : ∀ x, f x ≤ b) :
    uniformMean f ≤ b := by
  by_cases he : Nonempty U
  · let _ := he
    calc _ ≤ ∑ x, unifW U x * b := Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (h x)
         _ = b := by rw [← Finset.sum_mul,sum_unifW,one_mul]
  · let _ := not_nonempty_iff.mp he
    simp [uniformMean]

private theorem avg_shift {U : Type} [Fintype U] {f g : U → ℝ≥0∞} {b : ℝ≥0∞} (h : ∀ x, f x ≤ g x + b) :
    uniformMean f ≤ uniformMean g + b := by
  calc
    _ ≤ ∑ x, unifW U x * (g x + b) := Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (h x)
    _ = uniformMean g + uniformMean (fun _ : U => b) := by simp only [uniformMean,mul_add,Finset.sum_add_distrib]
    _ ≤ _ := add_le_add le_rfl (avg_le fun _ => le_rfl)

omit [DecidableEq A] in
theorem eager_le_one (ev : Z → ℝ≥0∞) (h : ∀ a, ev a ≤ 1) (p : Equiv.Perm A) (P : OracleComp (TwoWay A) Z) :
    eager p ev P ≤ 1 := by
  induction P using OracleComp.inductionOn with
  | pure z => exact h z
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩
    · exact avg_le ih
    · exact ih _

theorem lazy_le_one (ev : Z → ℝ≥0∞) (h : ∀ a, ev a ≤ 1) (P : OracleComp (TwoWay A) Z)
    (t : EdgeTrace A) : lazyRun ev P t ≤ 1 := by
  induction P using OracleComp.inductionOn generalizing t with
  | pure z => exact h z
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩
    · exact avg_le (fun r => ih r t)
    · change step t d x (fun y t' => lazyRun ev (k y) t') ≤ 1
      unfold step
      split
      · exact ih _ _
      · exact avg_le fun y => ih _ _

def forestPenalty (R A : Type) [Fintype R] [Fintype A] (q : ℕ) : ℝ≥0∞ :=
  ↑(Fintype.card R * (2*q+2)) / ↑(Fintype.card A-q)

omit [Fintype A] [DecidableEq A] in
private theorem compatible (t : EdgeTrace A) (d : Bool) (x : A) (hx : ¬old t d x)
    (ht : Nonempty (Extensions t)) (y : UnusedOutputs (orient d t)) :
    Nonempty (Extensions (edge d x y.val::t)) := by
  let i : UnusedInputs (orient d t) := ⟨x,by
    rintro ⟨u,v⟩ he rfl
    exact hx ⟨v,he⟩⟩
  cases d with
  | false => exact extensions_cons_nonempty t i y ht
  | true =>
    have ext := extensions_cons_nonempty (t.map Prod.swap) i y (ht.map (inverseExtensionsEquiv t))
    refine ext.map (fun p => ⟨p.val.symm,?_⟩)
    intro e he
    rcases List.mem_cons.mp he with rfl|h
    · exact p.val.symm_apply_eq.mpr (p.property _ (List.mem_cons_self ..)).symm
    · exact p.val.symm_apply_eq.mpr (p.property _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e,h,rfl⟩))).symm

private theorem penalty_le (t : EdgeTrace A) (d : Bool) (Q : ℕ) (ht : t.length ≤ Q) :
    (Fintype.card R * (2*t.length+2) : ℕ) / (Fintype.card (UnusedOutputs (orient d t)) : ℝ≥0∞) ≤
      forestPenalty R A Q := by
  have len : (orient d t).length = t.length := by cases d <;> simp [orient]
  have u := unused_card (orient d t)
  rw [len] at u
  unfold forestPenalty
  rw [div_eq_mul_inv,div_eq_mul_inv]
  apply mul_le_mul'
  · exact Nat.cast_le.mpr (Nat.mul_le_mul_left _ (by omega))
  · exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (by omega))

theorem lazy_forest (ev : Z → ℝ≥0∞) (hv : ∀ z, ev z ≤ 1) (P : OracleComp (TwoWay A) Z)
    (Q q : ℕ) (hq : CountBound (fun i => i.isRight = true) P q) (t : EdgeTrace A)
    (ht : t.length+q ≤ Q) (ok : Nonempty (Extensions t)) :
    lazyRun ev P t ≤ forest split root ev P t + q*forestPenalty R A Q := by
  induction P using OracleComp.inductionOn generalizing q t with
  | pure z => exact le_add_right le_rfl
  | query_bind i k ih =>
    rw [countBound_query_bind] at hq
    rcases i with n|⟨d,x⟩
    · exact avg_shift (fun r => ih r q (hq r) t ht ok)
    · have pos : 0 < q := hq.1
      obtain ⟨q,rfl⟩ := Nat.exists_eq_add_one_of_ne_zero pos.ne'
      have rest (y) := hq.2 y
      simp only [Nat.add_sub_cancel] at rest
      change step t d x (fun y t' => lazyRun ev (k y) t') ≤
        forestStep split root t d x (fun y t' => forest split root ev (k y) t') + _
      unfold step forestStep
      split
      · exact (ih _ q (rest _) t (by omega) ok).trans
          (add_le_add le_rfl (mul_le_mul' (by exact_mod_cast Nat.le_succ q) le_rfl))
      · rename_i fresh
        let v (y : A) := lazyRun ev (k y) (edge d x y::t)
        have vf (y : A) : v y ≤ 1 := lazy_le_one ev hv (k y) _
        have bound := fresh_filter split root t d x fresh ok v vf
        have compare := avg_shift (fun y : {z : UnusedOutputs (orient d t) //
            (split z.val).2 ∉ forbidden split root t x} =>
          ih y.val.val q (rest _) _ (by simp only [List.length_cons]; omega)
            (compatible t d x fresh ok y.val))
        refine bound.trans ((add_le_add compare (penalty_le (R := R) t d Q (by omega))).trans ?_)
        rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_assoc]

def wordSplit : Words ≃ Rate × Capacity where
  toFun w := (rateOf w,capOf w)
  invFun z := join z.1 z.2
  left_inv := join_split
  right_inv z := Prod.ext (rate_join z.1 z.2) (cap_join z.1 z.2)

set_option exponentiation.threshold 2048 in
private theorem benchmark_penalty :
    (2^41 : ℝ≥0∞) * forestPenalty Rate Words (2^41) ≤ (2^427 : ℝ≥0∞)⁻¹ := by
  have lanes (n : ℕ) : Fintype.card (Fin n → UInt64) = (2^64)^n := by
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
  have r : Fintype.card Rate = 2^1088 := (lanes 17).trans (by rfl)
  have w : Fintype.card Words = 2^1600 := (lanes 25).trans (by rfl)
  rw [forestPenalty,r,w]
  have nz : 2^1600 - 2^41 ≠ (0:ℕ) := by decide +kernel
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast]
  norm_num

/-- All real public and internal permutation calls count towards this
classical transcript bound. Inverse queries are legal at every point. -/
theorem benchmark_forest (ev : Z → ℝ≥0∞) (hv : ∀ z, ev z ≤ 1)
    (P : OracleComp (TwoWay Words) Z) (hq : CountBound (fun i => i.isRight = true) P (2^41)) :
    uniformMean (fun π : Permutation => eager π ev P) ≤ forest wordSplit 0 ev P [] + (2^427 : ℝ≥0∞)⁻¹ := by
  rw [eager_lazy]
  apply (lazy_forest wordSplit 0 ev hv P (2^41) (2^41) hq [] (by simp) ⟨⟨Equiv.refl _,by simp⟩⟩).trans
  exact add_le_add le_rfl (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using benchmark_penalty)

end
end Reduction.ShakePermutation.Classic

#print axioms Reduction.ShakePermutation.Classic.benchmark_forest
