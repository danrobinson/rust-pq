import Integration.SlhDsaCompressionReadout

namespace Reduction.Compression.Recording.Database
open Finset
set_option linter.unusedSectionVars false
variable {X Y V : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private def hit (c : X × Finset Y) (d : DB X Y) : Prop :=
  ∃ y ∈ c.2, d c.1 = some y

private def good (cs : List (X × Finset Y)) (d : DB X Y) : Prop :=
  ∀ c ∈ cs, hit c d

private theorem marginal (a : X) (P : Option Y → Prop) (v : DB X Y → V) :
    sumWeight (fun d => P (d a)) (tensor v) = sumWeight (fun d => P (d a)) (readCell a v) := by
  classical
  unfold sumWeight
  conv_lhs => rw [split_sum a,Finset.sum_comm]
  conv_rhs => rw [split_sum a,Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h : P u
  · simp only [assemble_at,h,ite_true,tensor_slice,readCell_slice]
    exact tensor_energy _
  · simp [assemble_at,h]

private theorem missed (c : X × Finset Y) (δ : ℝ) (hδ : 0 ≤ δ)
    (frac : (c.2.card : ℝ) / Fintype.card Y ≤ δ)
    (v : DB X Y → V) (absent : ∀ d, hit c d → v d = 0) :
    sumWeight (hit c) (tensor v) ≤ (4*δ) * ∑ d, ‖v d‖^2 := by
  classical
  obtain ⟨a,K⟩ := c
  rw [show sumWeight (hit (a,K)) (tensor v) = sumWeight (hit (a,K)) (readCell a v) from
      marginal a (fun u => ∃ y ∈ K, u = some y) v]
  unfold sumWeight
  rw [split_sum a,split_sum a (fun d => ‖v d‖^2),Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  let f := fun w => v (assemble a r w)
  have at_some (y : Y) : hit (a,K) (assemble a r (some y)) ↔ y ∈ K := by
    simp [hit,assemble_at]
  have at_none : ¬ hit (a,K) (assemble a r none) := by simp [hit,assemble_at]
  have val (y : Y) (hy : y ∈ K) : readCell a v (assemble a r (some y)) =
      coeff Y • (f none - mean f) := by
    rw [readCell_slice]
    change f (some y) + _ = _
    rw [show f (some y) = 0 from absent _ ((at_some y).mpr hy),zero_add]
  rw [Fintype.sum_option]
  simp only [at_none,ite_false,zero_add,at_some,← Finset.sum_filter]
  rw [show Finset.univ.filter (fun y => y ∈ K) = K by ext; simp]
  rw [Finset.sum_congr rfl fun y hy => congrArg (fun w : V => ‖w‖^2) (val y hy),
      Finset.sum_const,nsmul_eq_mul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,coeff,inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have m := mul_le_mul frac (diff_energy f) (sq_nonneg _) hδ
  rw [div_eq_mul_inv] at m
  simp only [Fintype.sum_option]
  change _ ≤ _ * energy f
  convert m using 1 <;> ring

private theorem weight_mono {A : Type} [Fintype A] (P Q : A → Prop) (h : ∀ x, P x → Q x) (v : A → V) :
    sumWeight P v ≤ sumWeight Q v := by
  classical
  unfold sumWeight
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hp : P x
  · simp [hp,h x hp]
  · simp only [hp,ite_false]; split <;> positivity

private theorem decode_good (cs : List (X × Finset Y)) (δ : ℝ) (hδ : 0 ≤ δ)
    (frac : ∀ c ∈ cs, (c.2.card : ℝ) / Fintype.card Y ≤ δ) (v : DB X Y → V) :
    Real.sqrt (sumWeight (good cs) (tensor v)) ≤ Real.sqrt (sumWeight (good cs) v) +
      2 * (cs.length : ℝ) * Real.sqrt δ * Real.sqrt (∑ d, ‖v d‖^2) := by
  classical
  induction cs generalizing v with
  | nil => simp [sumWeight,good,tensor_energy]
  | cons c cs ih =>
    let g := fun d => if hit c d then v d else 0
    let f := fun d => if hit c d then 0 else v d
    have eqv : v = fun d => g d + f d := by funext d; by_cases h : hit c d <;> simp [g,f,h]
    have eqt : tensor v = fun d => tensor g d + tensor f d := by
      conv_lhs => rw [eqv]
      funext d
      simp [tensor,smul_add,Finset.sum_add_distrib]
    have hc d : good (c :: cs) d ↔ hit c d ∧ good cs d := by simp [good]
    have eg : ∑ d, ‖g d‖^2 ≤ ∑ d, ‖v d‖^2 := by
      apply Finset.sum_le_sum; intro d _; by_cases h : hit c d <;> simp [g,h]
    have ef : ∑ d, ‖f d‖^2 ≤ ∑ d, ‖v d‖^2 := by
      apply Finset.sum_le_sum; intro d _; by_cases h : hit c d <;> simp [f,h]
    have wg : sumWeight (good cs) g = sumWeight (good (c :: cs)) v := by
      unfold sumWeight
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases h : hit c d <;> simp [g,h,hc]
    have lg := Real.sqrt_le_sqrt (weight_mono _ _ (fun d h => ((hc d).mp h).2) (tensor g))
    have lf := Real.sqrt_le_sqrt (weight_mono _ _ (fun d h => ((hc d).mp h).1) (tensor f))
    have mg := ih (fun a ha => frac a (List.mem_cons_of_mem _ ha)) g
    rw [wg] at mg
    have mf := (missed c δ hδ (frac c List.mem_cons_self) f (fun d hd => by simp [f,hd])).trans
      (mul_le_mul_of_nonneg_left ef (by positivity))
    have af := Real.sqrt_le_sqrt mf
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4*δ),Real.sqrt_mul (by norm_num : 0 ≤ (4:ℝ))] at af
    rw [show Real.sqrt 4 = 2 by exact (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).2 (by norm_num)] at af
    have mg' := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt eg)
      (by positivity : 0 ≤ 2*(cs.length:ℝ)*Real.sqrt δ)
    rw [eqt]
    apply (sw_triangle ..).trans
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith [lg,lf,mg,mg',af]

/-- Decoding a finite list of measured cells costs one amplitude term per observation.
The address and allowed set may repeat. -/
theorem readout_constraints (cs : List (X × Finset Y)) (δ : ℝ) (hδ : 0 ≤ δ)
    (frac : ∀ c ∈ cs, (c.2.card : ℝ) / Fintype.card Y ≤ δ) (v : DB X Y → V) :
    Real.sqrt (sumWeight (fun H : X → Y => ∀ c ∈ cs, H c.1 ∈ c.2)
      (fun H => tensor v (fun j => some (H j)))) ≤
    Real.sqrt (sumWeight (fun d : DB X Y => ∀ c ∈ cs, ∃ y ∈ c.2, d c.1 = some y) v) +
      2 * (cs.length : ℝ) * Real.sqrt δ * Real.sqrt (∑ d, ‖v d‖^2) := by
  classical
  apply le_trans _ (decode_good cs δ hδ frac v)
  apply Real.sqrt_le_sqrt
  let incl : (X → Y) ↪ DB X Y := ⟨fun H j => some (H j), fun f g h =>
    funext fun x => Option.some.inj (congrFun h x)⟩
  let val := fun d : DB X Y => if good cs d then ‖tensor v d‖^2 else 0
  have h : ∑ d ∈ Finset.univ.map incl, val d ≤ ∑ d, val d :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun d _ _ => by
      unfold val
      split <;> first | exact sq_nonneg _ | exact le_rfl
  rw [Finset.sum_map] at h
  have e (H : X → Y) : good cs (incl H) ↔ ∀ c ∈ cs, H c.1 ∈ c.2 := by
    change (∀ c ∈ cs, ∃ y ∈ c.2, some (H c.1) = some y) ↔ _
    simp
  have weight (H : X → Y) : val (incl H) = if ∀ c ∈ cs, H c.1 ∈ c.2 then ‖tensor v (fun j => some (H j))‖^2 else 0 := by
    simp only [val,e]
    rfl
  simpa only [sumWeight,val,weight] using h

/-- An event certified by the measured cells is charged to a recorded failure
event, with a common length bound across measured branches. -/
theorem readout_failure (cs : List (X × Finset Y)) (m : ℕ) (hm : cs.length ≤ m)
    (δ : ℝ) (hδ : 0 ≤ δ) (frac : ∀ c ∈ cs, (c.2.card : ℝ) / Fintype.card Y ≤ δ)
    (E : (X → Y) → Prop) (P : DB X Y → Prop)
    (measure : ∀ H, E H → ∀ c ∈ cs, H c.1 ∈ c.2)
    (record : ∀ d, (∀ c ∈ cs, ∃ y ∈ c.2, d c.1 = some y) → P d)
    (v : DB X Y → V) :
    sumWeight E (fun H => tensor v (fun j => some (H j))) ≤
      (Real.sqrt (sumWeight P v) + (2*(m:ℝ)*Real.sqrt δ)*Real.sqrt (∑ d, ‖v d‖^2))^2 := by
  have h := (Real.sqrt_le_sqrt (weight_mono _ _ measure _)).trans (readout_constraints cs δ hδ frac v)
  have r := Real.sqrt_le_sqrt (weight_mono _ _ record v)
  have n : (cs.length : ℝ) ≤ m := by exact_mod_cast hm
  have err := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left n (by norm_num : 0 ≤ (2:ℝ))) (Real.sqrt_nonneg δ))
    (Real.sqrt_nonneg (∑ d, ‖v d‖^2))
  have bound := h.trans (add_le_add r err)
  exact (Real.sq_sqrt (sw_nonneg E (fun H => tensor v (fun j => some (H j))))) ▸ (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr bound

#print axioms readout_constraints
#print axioms readout_failure
end Reduction.Compression.Recording.Database
