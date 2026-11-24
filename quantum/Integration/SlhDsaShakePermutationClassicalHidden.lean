import Integration.SlhDsaShakePermutationClassicalLazy
import Integration.SlhDsaSetPrf

/-! After a classical adaptive transcript has been fixed, its unobserved
capacity rows still form an independent uniform table. The simultaneous
swap below uses the transcript-dependent set of observed addresses. -/
namespace Reduction.ShakePermutation.Classic
open Classical
open scoped ENNReal
open SetOracle (uniformMean)
noncomputable section
variable {I C T : Type} [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C] [Nonempty C]

def keep (s : Finset I) (g h : I → C) : I → C := fun i => if i ∈ s then g i else h i

theorem resample_after (transcript : (I → C) → T) (exposed : T → Finset I)
    (stable : ∀ g h, (∀ i ∈ exposed (transcript g), h i = g i) → transcript h = transcript g)
    (score : T → (I → C) → ℝ≥0∞) :
    uniformMean (fun g => score (transcript g) g) = uniformMean (fun g =>
      uniformMean (fun h => score (transcript g) (keep (exposed (transcript g)) g h))) := by
  let swap (z : (I → C) × (I → C)) :=
    (keep (exposed (transcript z.1)) z.1 z.2,keep (exposed (transcript z.1)) z.2 z.1)
  have fixed (g h : I → C) : transcript (keep (exposed (transcript g)) g h) = transcript g :=
    stable g _ (fun i hi => by simp [keep,hi])
  have inv : Function.Involutive swap := by
    rintro ⟨g,h⟩
    simp only [swap,fixed]
    apply Prod.ext <;> funext i <;> by_cases hi : i ∈ exposed (transcript g) <;> simp [keep,hi]
  have eq := Equiv.sum_comp (Function.Involutive.toPerm swap inv)
    (fun z => unifW (I → C) z.1 * (unifW (I → C) z.2 * score (transcript z.1) z.1))
  change (∑ z : (I → C) × (I → C), unifW (I → C) (swap z).1 * (unifW (I → C) (swap z).2 * score (transcript (swap z).1) (swap z).1)) = _ at eq
  simp only [Fintype.sum_prod_type,swap,fixed] at eq
  unfold uniformMean
  simp only [Finset.mul_sum]
  symm
  calc
    _ = ∑ g, ∑ h, unifW (I → C) g * (unifW (I → C) h * score (transcript g) g) := eq
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g _
      simp only [← mul_assoc,← Finset.sum_mul,← Finset.mul_sum,sum_unifW,mul_one]

private theorem resample_one (i : I) (v : (I → C) → ℝ≥0∞) :
    uniformMean v = uniformMean (fun h => uniformMean (fun c => v (Function.update h i c))) :=
  SetOracle.avg_resample (fun h c => Function.update h i c) (fun h => h i) (by
    rintro ⟨g,c⟩
    apply Prod.ext
    · funext j; by_cases eq : j=i <;> simp [Function.update,eq]
    · simp) v

def hit (p : Prop) [Decidable p] : ℝ≥0∞ := if p then 1 else 0

private theorem point_mean (c : C) : uniformMean (fun y => hit (y = c)) = (Fintype.card C : ℝ≥0∞)⁻¹ := by
  classical
  simp [uniformMean,hit,unifW,Finset.sum_ite_eq']

private theorem avg_fixed {U : Type} [Fintype U] [Nonempty U] (a : ℝ≥0∞) :
    uniformMean (fun _ : U => a) = a := by
  unfold uniformMean
  rw [← Finset.sum_mul,sum_unifW,one_mul]

theorem point_row (i : I) (c : C) :
    uniformMean (fun h : I → C => hit (h i = c)) = (Fintype.card C : ℝ≥0∞)⁻¹ := by
  rw [resample_one i]; simp only [Function.update_self,point_mean,avg_fixed]

theorem pair_rows (i j : I) (ne : i ≠ j) :
    uniformMean (fun h : I → C => hit (h i = h j)) = (Fintype.card C : ℝ≥0∞)⁻¹ := by
  rw [resample_one i]; simp only [Function.update_self,Function.update_of_ne ne.symm,point_mean,avg_fixed]

def leaked (hidden : Finset I) (denied : Finset C) (g : I → C) :=
  (∃ i ∈ hidden, g i ∈ denied) ∨ (∃ i ∈ hidden, ∃ j ∈ hidden, i ≠ j ∧ g i = g j)

private theorem witness_sum {J : Type} [DecidableEq J] (s : Finset J) (f : J → ℝ≥0∞) (i : J) (hi : i ∈ s) :
    f i ≤ ∑ j ∈ s, f j := Finset.single_le_sum (fun _ _ => zero_le) hi

private theorem hit_le (s : Finset I) (d : Finset C) (g : I → C) :
    hit (leaked s d g) ≤ (∑ i ∈ s, ∑ c ∈ d, hit (g i = c)) +
      ∑ i ∈ s, ∑ j ∈ s.erase i, hit (g i = g j) := by
  by_cases bad : leaked s d g
  · rw [hit,ite_eq_left bad]
    rcases bad with ⟨i,hi,hd⟩|⟨i,hi,j,hj,ne,eq⟩
    · have t := (witness_sum d (fun c => hit (g i = c)) (g i) hd).trans
        (witness_sum s (fun i => ∑ c ∈ d, hit (g i = c)) i hi)
      simp only [hit,ite_true] at t
      exact t.trans (le_add_right le_rfl)
    · have t := (witness_sum (s.erase i) (fun j => hit (g i = g j)) j (Finset.mem_erase.mpr ⟨ne.symm,hj⟩)).trans
        (witness_sum s (fun i => ∑ j ∈ s.erase i, hit (g i = g j)) i hi)
      rw [hit,ite_eq_left eq] at t
      exact t.trans (le_add_left le_rfl)
  · simp [hit,bad]

private theorem mean_sum {U J : Type} [Fintype U] (s : Finset J) (f : U → J → ℝ≥0∞) :
    uniformMean (fun g => ∑ j ∈ s, f g j) = ∑ j ∈ s, uniformMean (fun g => f g j) := by
  unfold uniformMean; simp only [Finset.mul_sum]; rw [Finset.sum_comm]

theorem hidden_risk (s : Finset I) (d : Finset C) :
    uniformMean (fun g : I → C => hit (leaked s d g)) ≤
      ((s.card * d.card + s.card ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card C := by
  calc
    _ ≤ uniformMean (fun g : I → C => (∑ i ∈ s, ∑ c ∈ d, hit (g i=c)) +
        ∑ i ∈ s, ∑ j ∈ s.erase i, hit (g i=g j)) :=
      Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (hit_le s d g)
    _ = (∑ i ∈ s, ∑ c ∈ d, uniformMean (fun g : I → C => hit (g i=c))) +
        ∑ i ∈ s, ∑ j ∈ s.erase i, uniformMean (fun g : I → C => hit (g i=g j)) := by
      have addMean (a b : (I → C) → ℝ≥0∞) :
          (uniformMean fun g => a g + b g) = uniformMean a + uniformMean b := by
        simp only [uniformMean,mul_add,Finset.sum_add_distrib]
      rw [addMean]
      congr 1 <;> rw [mean_sum] <;> apply Finset.sum_congr rfl <;> intro i _ <;> apply mean_sum
    _ ≤ (∑ i ∈ s, ∑ _ ∈ d, (Fintype.card C : ℝ≥0∞)⁻¹) +
        ∑ i ∈ s, ∑ _ ∈ s, (Fintype.card C : ℝ≥0∞)⁻¹ := by
      apply add_le_add
      · simp only [point_row,le_rfl]
      · refine Finset.sum_le_sum fun i _ => ?_
        calc _ = ∑ j ∈ s.erase i, (Fintype.card C : ℝ≥0∞)⁻¹ := by
                 apply Finset.sum_congr rfl
                 intro j hj
                 exact pair_rows i j (Finset.mem_erase.mp hj).1.symm
             _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset ..) (fun _ _ _ => zero_le)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,div_eq_mul_inv]; ring

theorem adaptive_hidden_risk (Tg : (I → C) → T) (seen hidden : T → Finset I) (denied : T → Finset C)
    (stable : ∀ g h, (∀ i ∈ seen (Tg g), h i = g i) → Tg h = Tg g)
    (disj : ∀ t i, i ∈ hidden t → i ∉ seen t) (m q : ℕ)
    (size : ∀ t, (hidden t).card ≤ m ∧ (denied t).card ≤ q) :
    uniformMean (fun g => hit (leaked (hidden (Tg g)) (denied (Tg g)) g)) ≤
      ((m*q+m^2 : ℕ) : ℝ≥0∞) / Fintype.card C := by
  rw [resample_after Tg seen stable (fun t g => hit (leaked (hidden t) (denied t) g))]
  calc
    _ ≤ uniformMean (fun _ : I → C => ((m*q+m^2 : ℕ) : ℝ≥0∞)/Fintype.card C) := by
      apply Finset.sum_le_sum
      intro g _
      apply mul_le_mul' le_rfl
      let t := Tg g
      have eq (h : I → C) : leaked (hidden t) (denied t) (keep (seen t) g h) ↔ leaked (hidden t) (denied t) h := by
        unfold leaked
        constructor <;> rintro (⟨i,hi,bad⟩ | ⟨i,hi,j,hj,ne,bad⟩)
        all_goals first
          | exact Or.inl ⟨i,hi,by simpa only [keep,ite_eq_right (disj t i hi)] using bad⟩
          | exact Or.inr ⟨i,hi,j,hj,ne,by simpa only [keep,ite_eq_right (disj t i hi),ite_eq_right (disj t j hj)] using bad⟩
      change uniformMean (fun h => hit (leaked (hidden t) (denied t) (keep (seen t) g h))) ≤ _
      simp_rw [eq]
      apply (hidden_risk (hidden t) (denied t)).trans
      rw [div_eq_mul_inv,div_eq_mul_inv]
      exact mul_le_mul' (Nat.cast_le.mpr (Nat.add_le_add (Nat.mul_le_mul (size t).1 (size t).2)
        (Nat.pow_le_pow_left (size t).1 2))) le_rfl
    _ = _ := avg_fixed _

end
end Reduction.ShakePermutation.Classic
#print axioms Reduction.ShakePermutation.Classic.adaptive_hidden_risk
