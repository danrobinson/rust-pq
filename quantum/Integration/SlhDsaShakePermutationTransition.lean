import Integration.SlhDsaShakePermutationAttach
import VCVio.Quantum.Oracle.Compressed.BinaryPartition

/-! A quantum compressed-oracle transition bound for fresh capacity masks
that hit already reachable or queried rates. Candidate sets may depend on
the queried rate. The norm bound applies to a coherent query. -/
namespace Reduction.ShakePermutation
open Classical Quantum ENNReal OracleSpec Matrix
open scoped Matrix.Norms.L2Operator

section
variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

noncomputable def hit (bad : X → Finset Y) (D : Database X Y) : Bool :=
  decide (∃ x y, D x = some y ∧ y ∈ bad x)

omit [Fintype Y] in
private theorem fresh_flip (bad : X → Finset Y) (D : Database X Y)
    (x : X) (hx : D x = none) (y : Y)
    (h : hit bad (Function.update D x (some y)) ≠ hit bad D) : y ∈ bad x := by
  classical
  by_contra hnot
  apply h
  unfold hit
  congr 1
  apply propext
  constructor
  · rintro ⟨x',y',he,hb⟩
    by_cases hh : x' = x
    · subst x'
      simp only [Function.update_self,Option.some.injEq] at he
      exact (hnot (he.symm ▸ hb)).elim
    · exact ⟨x',y',by simpa only [Function.update_of_ne hh] using he,hb⟩
  · rintro ⟨x',y',he,hb⟩
    have hh : x' ≠ x := by rintro rfl; simp [hx] at he
    exact ⟨x',y',by simpa only [Function.update_of_ne hh] using he,hb⟩

variable [UniformAnswerMeasure (X →ₒ Y)]

private theorem hit_instability (bad : X → Finset Y) (B t : Nat)
    (hB : ∀ x, (bad x).card ≤ B) :
    Database.instability (hit bad) t ≤ (B : ℝ≥0∞) / Fintype.card Y := by
  classical
  rw [Database.instability_eq_iSup]
  refine iSup_le fun i => iSup_le fun D => iSup_le fun hD => iSup_le fun _ =>
    iSup_le fun x => iSup_le fun hx => ?_
  subst i
  have he := Finset.card_le_card (s := Finset.univ.filter fun u : Y =>
    hit bad (Function.update D x (some u)) ≠ hit bad D) (t := bad x)
    (fun y hy => fresh_flip bad D x hx y (Finset.mem_filter.mp hy).2)
  gcongr
  exact he.trans (hB x)

private theorem hit_transition [AddCommGroup Y] (bad : X → Finset Y) (B t : Nat)
    (hB : ∀ x, (bad x).card ≤ B) :
    ‖labelProjector (fun z : (X × Y) × Database X Y => hit bad z.2) true *
        truncatedOracle X Y t *
        labelProjector (fun z : (X × Y) × Database X Y => hit bad z.2) false‖ ^ 2 ≤
        6 * (B : ℝ) / Fintype.card Y := by
  have hb := hit_instability bad B t hB
  have h' : (Fintype.card Y : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hr := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) h') hb
  rw [ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast] at hr
  exact (l2_opNorm_labelProjector_mul_truncatedOracle_mul_sq_le_six_mul (hit bad) t
    (by decide : true ≠ false)).trans (by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hr (by norm_num))

end

theorem attach_transition (π : Permutation) (hπ : ¬irregular π) (t : Nat)
    (pending : Rate → Finset (Rate × Capacity)) (forbidden : Rate → Finset Rate)
    (hp : ∀ x, (pending x).card ≤ t+1) (hf : ∀ x, (forbidden x).card ≤ t*(t+1)+t) :
    let label := hit (fun x => badAttach π (pending x) (forbidden x))
    ‖labelProjector (fun z : (Rate × Capacity) × Database Rate Capacity => label z.2) true *
        truncatedOracle Rate Capacity t *
        labelProjector (fun z : (Rate × Capacity) × Database Rate Capacity => label z.2) false‖ ^ 2
      ≤ 6 * (4*(t+1)*(t*(t+1)+t) : ℕ) / (2^512 : ℝ) := by
  classical
  let bad (x : Rate) := badAttach π (pending x) (forbidden x)
  let : UniformAnswerMeasure (Rate →ₒ Capacity) := UniformAnswerMeasure.ofFiniteNonempty _
  have hn := hit_transition bad (4*(t+1)*(t*(t+1)+t)) t
    (fun x => badAttach_step π hπ (pending x) (forbidden x) t (hp x) (hf x))
  have hc : Fintype.card Capacity = 2^512 := by
    change Fintype.card (Fin 8 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  rw [hc,Nat.cast_pow,Nat.cast_ofNat] at hn
  exact hn

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.attach_transition
