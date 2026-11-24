import Integration.SlhDsaShakePermutationSkMarginal

/-! The native real and ideal SK.PRF experiments, with the same coherent
two-way permutation port in the machine and the actual padded primitive. -/
namespace Reduction.ShakePermutation.SkGames
open Classical MLink SLHDSA SLHDSA.Security Quantum PQ.Interactive PQ.QROM ENNReal
open scoped Kronecker ComplexOrder
set_option maxRecDepth 8192
variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
abbrev Rows := S.Node × Bytes 32
abbrev Dom := S.Node × SkAdrs S.vp
abbrev Machine (E : Type) [Fintype E] [DecidableEq E] := (Port → Words) →
  QOC (WS Port Words E) (PRFScheme.PRFOracleSpec (Dom S) S.Node) Bool

def realTable (π : Permutation) (k : S.Node) (j : Rows S) :=
  (SkFormat.split S (π (SkFormat.input S (k,j)))).1

noncomputable def B (A : Machine S E) (ρ : SubState ((Port × Words) × E))
    (π : Permutation) (F : Rows S → S.Node) :=
  qWeight (· = true) (ansRun (fun d => F (ShakeXof.skAddress S d)) (A (oracle π)))
    (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)

theorem scheme_eq (π : Permutation) :
    skPrfC S.vp (primitives (lanes π) S.vp.params) =
      keyedScheme (ShakeXof.skAddress S) (fun x => realTable S π x.1 x.2) := by
  unfold skPrfC keyedScheme
  congr 1
  funext k d
  exact SkFormat.prf_eq S π d.1 k d.2.val

variable (A : Machine S E) (ρ : SubState ((Port × Words) × E))

theorem real_at (π : Permutation) :
    qPrfRealPr (skPrfC S.vp (primitives (lanes π) S.vp.params)) (A (oracle π))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) =
    SetOracle.uniformMean (fun k => B S A ρ π (realTable S π k)) := by
  rw [scheme_eq]
  unfold qPrfRealPr qPrfRealExperiment
  rw [show (keyedScheme (ShakeXof.skAddress S) (fun x => realTable S π x.1 x.2)).keygen =
    ($ᵗ S.Node) from rfl,qWeight_liftU_uniform_bind]
  simp only [SetOracle.uniformMean, unifW,Finset.mul_sum]
  rfl

theorem ideal_at (π : Permutation) : qPrfIdealPr (A (oracle π))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) = SetOracle.uniformMean (B S A ρ π) := by
  have h := lazy_eq_avg (ShakeXof.skAddress S) (ShakeXof.skAddress_injective S)
    (· = true) (A (oracle π)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
  change qWeight _ (idealRun (A (oracle π)) ∅) _ = _
  simpa only [SetOracle.uniformMean,unifW,Finset.mul_sum,B,Rows] using h

theorem real_mean :
    SetOracle.uniformMean (fun π : Permutation => qPrfRealPr (skPrfC S.vp (primitives (lanes π) S.vp.params))
      (A (oracle π)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) =
    SetOracle.uniformMean (fun π => SetOracle.uniformMean (fun k => B S A ρ π (realTable S π k))) := by
  exact congrArg SetOracle.uniformMean (funext (real_at S A ρ))

theorem ideal_mean :
    SetOracle.uniformMean (fun π => qPrfIdealPr (A (oracle π))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)) =
    SetOracle.uniformMean (fun π => SetOracle.uniformMean (B S A ρ π)) := by
  exact congrArg SetOracle.uniformMean (funext (ideal_at S A ρ))

theorem B_le_one (q : ℕ) (hA : PrfAnswerCost A q) (π : Permutation) (F : Rows S → S.Node) :
    B S A ρ π F ≤ 1 := by
  obtain ⟨x,hx,eval⟩ := (hA (fun d => F (ShakeXof.skAddress S d))).exists_prog_qprob
  unfold B
  rw [← eval (· = true) (oracle π) ρ]
  exact (HybridModel.ofProgram LocalSig.Interp.instruments x ρ q hx (fun p => p.2 = true)).prob_le_one _ id

end Reduction.ShakePermutation.SkGames
#print axioms Reduction.ShakePermutation.SkGames.real_mean
#print axioms Reduction.ShakePermutation.SkGames.ideal_mean
#print axioms Reduction.ShakePermutation.SkGames.B_le_one
