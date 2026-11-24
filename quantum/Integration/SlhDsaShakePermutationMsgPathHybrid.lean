import Integration.SlhDsaShakePermutationMsgColumnRisk
import Integration.SlhDsaShakePermutationTrajectoryPrefix
import Integration.SlhDsaShakePermutationInjectionSwap

namespace Reduction.ShakePermutation.MsgTrajectory.Risk
open Classical SetOracle ENNReal
noncomputable section
set_option maxRecDepth 8192
variable {J : Type} [Fintype J] (u : J ↪ Words) (x : Words) (π σ : Permutation)

/-- Absorption inputs along the honest suffix, each as a permutation
of the randomized first state. -/
def visits (π : Permutation) (s : Permutation) : List Rate → List Permutation
  | [] => []
  | b::bs => let g := s.trans (absorbBlock b); g :: visits π (g.trans π) bs

theorem visits_length (s : Permutation) (bs : List Rate) : (visits π s bs).length = bs.length := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih => simp only [visits,List.length_cons,ih]

private theorem visit_returns (s : Words) (b : Rate) (bs : List Rate)
    (w : Words) :
    returns π s (absorbBlock b w) (bs.map absorbBlock) = true ↔
      ∃ g ∈ visits π (Equiv.refl _) (b::bs), π (g w) = s := by
  suffices all : ∀ (base : Permutation) (b : Rate) (l : List Rate),
      returns π s (absorbBlock b (base w)) (l.map absorbBlock) = true ↔
        ∃ g ∈ visits π base (b::l), π (g w) = s from all (Equiv.refl _) b bs
  intro base b l
  induction l generalizing base b with
  | nil => simp [returns,visits]
  | cons c cs ih =>
    let base' := (base.trans (absorbBlock b)).trans π
    change (decide (π (absorbBlock b (base w)) = s) || returns π s (absorbBlock c (base' w)) (cs.map absorbBlock)) = true ↔
      ∃ g ∈ base.trans (absorbBlock b) :: visits π base' (c::cs), π (g w) = s
    simp only [Bool.or_eq_true,decide_eq_true_eq,List.mem_cons,exists_eq_or_imp,Equiv.trans_apply]
    exact or_congr Iff.rfl (ih base' c)

def replacement : Permutation := (Program.swapInjections u (π,imageTuple u σ)).1

private theorem clean_path (s : Permutation) (bs : List Rate)
    (clean : ∀ g ∈ visits π s bs, ¬marked u x π σ g)
    (noReturn : ∀ g ∈ visits π s bs, π (g (σ x)) ≠ σ x) :
    suffix (replacement u π σ) bs (s (σ x)) = suffix π bs (s (σ x)) := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    let g := s.trans (absorbBlock b)
    have miss := clean g (List.mem_cons_self ..)
    have old : π (g (σ x)) ∉ Set.range (imageTuple u π) := by
      rintro ⟨j,e⟩
      exact miss (Or.inl ⟨j,(π.injective e).symm⟩)
    have target : π (g (σ x)) ∉ Set.range (imageTuple u σ) := by
      rintro ⟨j,e⟩
      by_cases eq : u j = x
      · exact noReturn g (List.mem_cons_self ..) (by simpa only [imageTuple,Function.Embedding.trans_apply,Equiv.coe_toEmbedding,eq] using e.symm)
      · exact miss (Or.inr ⟨j,eq,e⟩)
    have step := Program.reassign_miss _ _ _ old target
    change suffix (replacement u π σ) bs (Program.reassign (imageTuple u π) (imageTuple u σ) (π (g (σ x)))) = _
    rw [step]
    exact ih (g.trans π) (fun v h => clean v (List.mem_cons_of_mem _ h))
      (fun v h => noReturn v (List.mem_cons_of_mem _ h))

private theorem any_marked (gs : List Permutation) :
    uniformMean (fun τ : Permutation => if ∃ g ∈ gs, marked u x π τ g then (1:ℝ≥0∞) else 0) ≤
      (gs.length : ℝ≥0∞)*((Fintype.card J : ℝ≥0∞)*(1/Fintype.card Words) +
        (Fintype.card J : ℝ≥0∞)*(1/((Fintype.card Words-1:ℕ):ℝ≥0∞))) := by
  induction gs with
  | nil => simp only [List.not_mem_nil,false_and,exists_false,ite_false,uniformMean,mul_zero,Finset.sum_const_zero,List.length_nil,Nat.cast_zero,zero_mul,le_rfl]
  | cons g gs ih =>
    have per (τ : Permutation) : (if ∃ v ∈ g::gs, marked u x π τ v then (1:ℝ≥0∞) else 0) ≤
        (if marked u x π τ g then 1 else 0) + (if ∃ v ∈ gs, marked u x π τ v then 1 else 0) := by
      simp only [List.mem_cons,exists_eq_or_imp]
      by_cases a : marked u x π τ g <;> by_cases b : ∃ v ∈ gs, marked u x π τ v <;> simp [a,b]
    apply (Finset.sum_le_sum (s:=Finset.univ) fun τ _ => mul_le_mul' (le_rfl : unifW _ τ ≤ _) (per τ)).trans
    simp only [mul_add,Finset.sum_add_distrib] at *
    apply (add_le_add (marked_step u x π g) ih).trans_eq
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

/-- Starting after the programmed first round, compare the entire suffix
on the modified and original permutations. This bound holds pointwise in
the message and in every nonexceptional public permutation. -/
theorem suffix_gap (bs : List Rate) (len : bs.length ≤ 483) (ok : ¬exceptional π) :
    uniformMean (fun τ : Permutation =>
      if suffix (replacement u π τ) bs (τ x) ≠ suffix π bs (τ x) then (1:ℝ≥0∞) else 0) ≤
      ((2:ℝ≥0∞)^400)⁻¹ + (bs.length : ℝ≥0∞)*((Fintype.card J : ℝ≥0∞)*(1/Fintype.card Words) +
        (Fintype.card J : ℝ≥0∞)*(1/((Fintype.card Words-1:ℕ):ℝ≥0∞))) := by
  classical
  cases bs with
  | nil =>
    simp only [suffix,ne_self_iff_false,ite_false,uniformMean,mul_zero,Finset.sum_const_zero]
    exact zero_le
  | cons b bs =>
    let gs := visits π (Equiv.refl _) (b::bs)
    let cycle (w : Words) := returns π w (absorbBlock b w) (bs.map absorbBlock) = true
    have limits := (random_image x (fun w => if cycle w then (1:ℝ≥0∞) else 0)).le.trans
      (return_risk π ok b bs (by simp only [List.length_cons] at len; omega))
    have per (τ : Permutation) :
        (if suffix (replacement u π τ) (b::bs) (τ x) ≠ suffix π (b::bs) (τ x) then (1:ℝ≥0∞) else 0) ≤
          (if cycle (τ x) then 1 else 0) + (if ∃ g ∈ gs, marked u x π τ g then 1 else 0) := by
      by_cases c : cycle (τ x)
      · rw [ite_eq_left c]; split <;> simp
      · rw [ite_eq_right c,zero_add]
        by_cases hit : ∃ g ∈ gs, marked u x π τ g
        · rw [ite_eq_left hit]; split <;> simp
        · have clear (g) (hg : g ∈ gs) : ¬ marked u x π τ g := fun h => hit ⟨g,hg,h⟩
          have noreturn (g) (hg : g ∈ gs) : π (g (τ x)) ≠ τ x := fun e =>
            c ((visit_returns π (τ x) b bs (τ x)).mpr ⟨g,hg,e⟩)
          have eq := clean_path u x π τ (Equiv.refl _) (b::bs) clear noreturn
          simp only [Equiv.refl_apply] at eq
          rw [ite_eq_right (not_ne_iff.mpr eq),ite_eq_right hit]
    apply (Finset.sum_le_sum (s:=Finset.univ) fun τ _ => mul_le_mul' (le_rfl : unifW _ τ ≤ _) (per τ)).trans
    simp only [mul_add,Finset.sum_add_distrib]
    apply add_le_add limits
    have last := any_marked u x π gs
    rw [show gs.length=(b::bs).length from visits_length ..] at last
    apply le_trans _ (by simpa only [mul_add] using last)
    apply Finset.sum_le_sum; intro τ _
    apply mul_le_mul' le_rfl
    by_cases e : ∃ g ∈ gs, marked u x π τ g <;> simp [e]

end
end Reduction.ShakePermutation.MsgTrajectory.Risk
#print axioms Reduction.ShakePermutation.MsgTrajectory.Risk.suffix_gap
