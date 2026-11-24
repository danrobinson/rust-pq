import Integration.SlhDsaShakePermutationSparseAverage

/-! The reverse statistical inequality for the baseline side of a two-world
game, by complementing a bounded continuation at the selection transcript. -/
namespace Reduction.ShakePermutation.SparsePort.Phase
open Classical SetOracle Classic OracleComp PQ.Interactive ENNReal
noncomputable section
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false
variable {J Y Z T α : Type} [Fintype J] [DecidableEq J] [Fintype Y] [DecidableEq Y] [Nonempty Y]
 [Fintype Z] [DecidableEq Z] [Nonempty Z] [DecidableEq T]
variable (e : Words ≃ Y × Z) (a : J ↪ Words) (base : J) (tag : J → T)
variable (P : OracleComp (Tagged T) α) (W : (Port → Words) → (J → Y) → α → ℝ≥0∞)

private theorem mean_pair {D : Type} [Fintype D] [Nonempty D] {x y : D → ℝ≥0∞} (h : ∀ z, x z + y z = 1) :
    uniformMean x + uniformMean y = 1 := by
  simp only [uniformMean,← Finset.sum_add_distrib,← mul_add,h,mul_one,sum_unifW]

private theorem run_pair (f : T → Words → Words) (x y : α → ℝ≥0∞) (p : OracleComp (Tagged T) α)
    (h : ∀ z, x z + y z = 1) : run f x p + run f y p = 1 := by
  induction p using OracleComp.inductionOn with
  | pure z => exact h z
  | query_bind i k ih =>
    rcases i with n|⟨d,w⟩
    · exact mean_pair ih
    · exact ih _

theorem phase_reverse (jcap : Fintype.card J ≤ 2^768) (zcap : 2^1344 ≤ Fintype.card Z)
    (cert : valid a tag P) (bounded : ∀ H f x, W H f x ≤ 1) (Q : ℕ)
    (count : CountBound (fun i => i.isRight = true) (simulateQ erase P) Q) :
    uniformMean (fun π => uniformMean (fun f : J → Y => uniformMean (fun s : J → Z => ideal e a base tag P W π (f,s)))) ≤
      uniformMean (actual e a P W) +
      (Q * forestPenalty Rate Words Q + Q*((Fintype.card J:ℝ≥0∞)/Fintype.card Words)) +
      (((2:ℝ≥0∞)^63)⁻¹ + ((2:ℝ≥0∞)^384)⁻¹) := by
  let V (H : Port → Words) (f : J → Y) (x : α) := 1-W H f x
  have hc := phase_transfer e a base tag P V jcap zcap cert (fun _ _ _ => tsub_le_self) Q count
  let r (L : (Port → Words) → (J → Y) → α → ℝ≥0∞) := uniformMean (actual e a P L)
  let i (L : (Port → Words) → (J → Y) → α → ℝ≥0∞) := uniformMean (fun π => uniformMean (fun f : J → Y =>
    uniformMean (fun s : J → Z => ideal e a base tag P L π (f,s))))
  let err := Q * forestPenalty Rate Words Q + Q*((Fintype.card J:ℝ≥0∞)/Fintype.card Words) +
    (((2:ℝ≥0∞)^63)⁻¹ + ((2:ℝ≥0∞)^384)⁻¹)
  have v (H f x) : W H f x + V H f x = 1 := add_tsub_cancel_of_le (bounded H f x)
  have rtot : r W + r V = 1 := mean_pair (fun π => run_pair _ _ _ _ (v _ _))
  have itot : i W + i V = 1 := mean_pair (fun π => mean_pair (fun f => mean_pair (fun s => run_pair _ _ _ _ (v _ _))))
  have fin : i V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq itot)
  have l : r V ≤ i V + err := by simpa only [r,i,err,add_assoc] using hc
  rw [add_assoc]
  change i W ≤ r W + err
  apply (ENNReal.add_le_add_iff_right fin).mp
  calc i W + i V = r W + r V := itot.trans rtot.symm
       _ ≤ r W + (i V + err) := add_le_add le_rfl l
       _ = _ := (congrArg (r W + ·) (add_comm (i V) err)).trans (add_assoc _ _ _).symm

end
end Reduction.ShakePermutation.SparsePort.Phase
#print axioms Reduction.ShakePermutation.SparsePort.Phase.phase_reverse
