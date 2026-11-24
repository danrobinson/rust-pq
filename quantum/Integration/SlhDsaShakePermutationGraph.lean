import Integration.SlhDsaShakePermutationUpdate
import VCVio.Quantum.Oracle.Compressed.BinaryPartition

namespace Reduction.ShakePermutation.Tails.Graph
open Classical
variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

def Extends (k K : R → Option C) := ∀ r v, k r = some v → K r = some v

omit [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] in
theorem tail_mono (π : Layout R C) {k k' K K'} (h : Extends k K) (h' : Extends k' K')
    {l z} (t : Tail π k k' l z) : Tail π K K' l z := by
  induction t with
  | root => exact .root
  | step _ hu hv ih => exact .step ih (h _ _ hu) (h' _ _ hv)

theorem good_of_extension (π : Layout R C) {k k' K K'} (h : Extends k K) (h' : Extends k' K')
    (g : Good π K K') : Good π k k' := by
  have sub : intermediate π k k' ⊆ intermediate π K K' := by
    intro p hp
    obtain ⟨z,hz,r,u,hu,he⟩ := (mem_intermediate ..).mp hp
    obtain ⟨l,hl⟩ := (mem_reached ..).mp hz
    exact (mem_intermediate ..).mpr ⟨z,(mem_reached ..).mpr ⟨l,tail_mono π h h' hl⟩,r,u,h r u hu,he⟩
  exact ⟨fun ht ht' => g.uniqueTail (tail_mono π h h' ht) (tail_mono π h h' ht'),
    fun _ ha _ hb he => g.uniqueRate (sub ha) (sub hb) he⟩

theorem good_empty (π : Layout R C) : Good π (fun _ => none) (fun _ => none) := by
  have nil {l z} (h : Tail π (fun _ => none) (fun _ => none) l z) : l = [] := by
    cases h with
    | root => rfl
    | step _ hu _ => contradiction
  constructor
  · intro l m z hl hm
    exact (nil hl).trans (nil hm).symm
  · intro a ha
    rcases (mem_intermediate ..).mp ha with ⟨_,_,_,_,bad,_⟩
    contradiction

end Reduction.ShakePermutation.Tails.Graph

namespace Reduction.ShakePermutation.Tails
open Classical Quantum OracleSpec Matrix ENNReal
open scoped Matrix.Norms.L2Operator

abbrev Tagged (R : Type) := Bool × R
def half {R C : Type} (D : Database (Tagged R) C) (d : Bool) := fun x => D (d,x)
noncomputable def goodLabel {R C : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (π : Layout R C) (D : Database (Tagged R) C) : Bool := decide (Graph.Good π (half D false) (half D true))

section
variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

omit [Fintype R] [Fintype C] [DecidableEq C] in
private theorem half_extends (D : Database (Tagged R) C) (x : Tagged R) (hx : D x = none)
    (u : C) (d : Bool) : Graph.Extends (half D d) (half (Function.update D x (some u)) d) := by
  intro r v hv
  change D (d,r) = some v at hv
  have hn : (d,r) ≠ x := by rintro h; rw [h,hx] at hv; contradiction
  exact (Function.update_of_ne hn ..).trans hv

theorem goodLabel_stable_bad (π : Layout R C) (D : Database (Tagged R) C) (x : Tagged R)
    (hx : D x = none) (u : C) (hb : goodLabel π D = false) :
    goodLabel π (Function.update D x (some u)) = false := by
  simp only [goodLabel,decide_eq_false_iff_not] at hb ⊢
  exact fun hg => hb (Graph.good_of_extension π (half_extends D x hx u _) (half_extends D x hx u _) hg)

variable [UniformAnswerMeasure ((Tagged R) →ₒ C)]

theorem goodLabel_instability (π : Layout R C) (t B : Nat)
    (hb : ∀ (D : Database (Tagged R) C) (x : Tagged R), D.size < t → D x = none →
      goodLabel π D = true → (Finset.univ.filter fun u : C =>
        goodLabel π (Function.update D x (some u)) = false).card ≤ B) :
    Database.instability (goodLabel π) t ≤ (B : ℝ≥0∞) / Fintype.card C := by
  classical
  rw [Database.instability_eq_iSup]
  refine iSup_le fun i => iSup_le fun D => iSup_le fun hD => iSup_le fun ht =>
    iSup_le fun x => iSup_le fun hx => ?_
  cases i with
  | false =>
    have hf (u : C) := goodLabel_stable_bad π D x hx u hD
    simp [hf]
  | true =>
    have h := hb D x ht hx hD
    simp only [Bool.not_eq_true] at *
    gcongr

theorem goodLabel_transition [AddCommGroup C] (π : Layout R C) (t B : Nat)
    (hb : ∀ (D : Database (Tagged R) C) (x : Tagged R), D.size < t → D x = none →
      goodLabel π D = true → (Finset.univ.filter fun u : C =>
        goodLabel π (Function.update D x (some u)) = false).card ≤ B) :
    ‖labelProjector (fun z : (Tagged R × C) × Database (Tagged R) C => goodLabel π z.2) false *
        truncatedOracle (Tagged R) C t *
        labelProjector (fun z : (Tagged R × C) × Database (Tagged R) C => goodLabel π z.2) true‖ ^ 2 ≤
        6 * (B : ℝ) / Fintype.card C := by
  have he := goodLabel_instability π t B hb
  have h' : (Fintype.card C : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hr := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) h') he
  rw [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast] at hr
  exact (l2_opNorm_labelProjector_mul_truncatedOracle_mul_sq_le_six_mul (goodLabel π) t
    (by decide : false ≠ true)).trans (by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hr (by norm_num))

end
end Reduction.ShakePermutation.Tails
#print axioms Reduction.ShakePermutation.Tails.goodLabel_transition
