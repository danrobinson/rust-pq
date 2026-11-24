import Integration.SlhDsaShakePermutationSparseTransfer
import Integration.SlhDsaShakePermutationSparseLift
import Integration.SlhDsaShakeXofDspr

namespace Reduction.ShakePermutation.SparsePort
open SetOracle Classical PQ.Interactive PQ.QROM Quantum ENNReal
open scoped ComplexOrder
noncomputable section
variable {J Y Z E L : Type} [Fintype J] [DecidableEq J] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype E] [DecidableEq E]
variable (e : Words ≃ Y × Z) (a : J ↪ Words) (b : J)
local notation "Work" => WS Port Words E

theorem row_model (π : Permutation) (s : J → Z) (m : (Port → Words) → Closed Work L) (q : ℕ)
    (ρ₀ : Matrix Work Work ℂ) (hp : ρ₀.PosSemidef) (ht : ρ₀.trace = 1)
    (cost : PUE (spec := unifSpec) cnt0 m q) :
    ∃ M : HybridModel J Y L (12*q), M.Additive ∧ Rows.RowsBound (fun H ev => (M.prob H ev).toReal) (12*q) ∧
      ∀ F ev [DecidablePred ev], M.prob F ev = qWeight ev (m (simulatedPort e a π s b F)) ρ₀ := by
  obtain ⟨f,hf,he⟩ := Lift.lift_machine e a π s b cost
  let M := Workspace.state (Y := Y) b ρ₀
  obtain ⟨ρ,eq⟩ := exists_subState (A := Workspace.W J Y Work) M (Workspace.state_pos b ρ₀ hp)
    ((Workspace.state_trace b ρ₀).trans ht)
  obtain ⟨x,hx,hw⟩ := hf.exists_prog_qprob
  exact ⟨HybridModel.ofProgram LocalSig.Interp.instruments x ρ _ hx Sigma.snd,
    HybridModel.ofProgram_additive _ x ρ _ hx Sigma.snd,Rows.ofProgram_rowsBound _ x ρ _ hx Sigma.snd,
    fun F ev _ => (hw ev F ρ).trans (by rw [← eq]; exact he F ev ρ₀)⟩

def exactMean (W : (Port → Words) → (J → Y) → ℝ≥0∞) :=
  uniformMean (fun π : Permutation => W (oracle π) (exactTable e a π))
def simulatedMean (W : (Port → Words) → (J → Y) → ℝ≥0∞) :=
  uniformMean (fun π : Permutation => uniformMean (fun s : J → Z => uniformMean (fun F : J → Y => W (simulatedPort e a π s b F) F)))
def switchLoss : ℝ≥0∞ := ((2:ℝ≥0∞)^63)⁻¹ + ((2:ℝ≥0∞)^384)⁻¹

theorem score_transfer (W : (Port → Words) → (J → Y) → ℝ≥0∞)
    (jcap : Fintype.card J ≤ 2^768) (zcap : 2^1344 ≤ Fintype.card Z) (hw : ∀ H F, W H F ≤ 1) :
    exactMean e a W ≤ simulatedMean e a b W + switchLoss := by
  apply (transfer e a b jcap zcap W hw).trans_eq
  apply congrArg (· + switchLoss)
  apply congrArg uniformMean
  funext π
  unfold uniformMean
  simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp only [mul_left_comm]

private theorem mean_pair {D : Type} [Fintype D] [Nonempty D] {x y : D → ℝ≥0∞} (h : ∀ z, x z + y z = 1) :
    uniformMean x + uniformMean y = 1 := by
  simp only [uniformMean,← Finset.sum_add_distrib,← mul_add,h,mul_one,sum_unifW]

theorem score_reverse (W : (Port → Words) → (J → Y) → ℝ≥0∞)
    (jcap : Fintype.card J ≤ 2^768) (zcap : 2^1344 ≤ Fintype.card Z) (hw : ∀ H F, W H F ≤ 1) :
    simulatedMean e a b W ≤ exactMean e a W + switchLoss := by
  let V := fun H F => 1-W H F
  have v (H F) : W H F + V H F = 1 := add_tsub_cancel_of_le (hw H F)
  have rtot : exactMean e a W + exactMean e a V = 1 := mean_pair (fun π => v _ _)
  have itot : simulatedMean e a b W + simulatedMean e a b V = 1 :=
    mean_pair (fun π => mean_pair (fun s => mean_pair (fun F => v _ _)))
  have fin : simulatedMean e a b V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq itot)
  apply (ENNReal.add_le_add_iff_right fin).mp
  calc _ = exactMean e a W + exactMean e a V := itot.trans rtot.symm
       _ ≤ _ := add_le_add le_rfl (score_transfer e a b V jcap zcap (fun _ _ => tsub_le_self))
       _ = _ := (congrArg (exactMean e a W + ·) (add_comm _ _)).trans (add_assoc _ _ _).symm

end
end Reduction.ShakePermutation.SparsePort
#print axioms Reduction.ShakePermutation.SparsePort.row_model
#print axioms Reduction.ShakePermutation.SparsePort.score_reverse
