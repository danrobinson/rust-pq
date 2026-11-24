import Integration.SlhDsaShakePermutationPlayerEval
import Integration.SlhDsaShakePermutationFixProgram
import PQ.Interactive.QromBridgeWotsPre

/-! Born weights of the expanded real permutation player agree with compiling
and closing its original port program against the stateful challenger. -/
namespace Reduction.ShakePermutation.RoundPort.Player
open Classical Quantum OracleComp OracleSpec PQ.Interactive Fix Matrix ENNReal
open scoped Kronecker
variable {ι E α σ : Type} [Fintype E] [DecidableEq E] {sp : OracleSpec ι}

noncomputable def classicalEnv (impl : QueryImpl sp (StateT σ ProbComp)) : Env sp σ :=
  fun t f s => ∑' u, prob ((impl t).run s) (· = u) * f u.1 u.2

def padUnit {A : Type} (ρ : Density A) : Density (A × Unit) :=
  ρ.submatrix Prod.fst Prod.fst

noncomputable def measured {A : Type} [Fintype A] (ev : α × σ → Prop) [DecidablePred ev]
    (a : α) (s : σ) (ρ : Density A) : ℝ≥0∞ :=
  if ev (a,s) then ENNReal.ofReal ρ.trace.re else 0

private theorem pad_trace {A : Type} [Fintype A] (ρ : Density A) : (padUnit ρ).trace = ρ.trace := by
  simp [padUnit,Matrix.trace,Fintype.sum_prod_type]

private theorem pad_instr (j : InstrIdx (Old E))
    (i : Fin (j.1+1)) (ρ : Density (Old E)) :
    (framedIdx j).2.1.branch i (padUnit ρ) = padUnit (j.2.1.branch i ρ) := by
  ext p q
  change ((j.2.1.frame Unit).branch i _) _ _ = _
  rw [DSubInstrument.branch_frame_apply,MatrixMap.amplify_apply]
  rfl

theorem old_wp_weight (H : Port → Words) (impl : QueryImpl sp (StateT σ ProbComp))
    (p : QOC (Old E) (portSpec + sp) α) (s : σ) (ev : α × σ → Prop) [DecidablePred ev]
    (ρ : Density (Old E)) :
    qWeight ev (close impl (compileQ H p) s) (padUnit ρ) =
      wp (oldStep H (classicalEnv impl)) p (measured ev) s ρ := by
  induction p using OracleComp.inductionOn generalizing s ρ with
  | pure a =>
    rw [compileQ_pure,close_pure,qWeight_pure,wp_pure]
    rw [pad_trace]; rfl
  | query_bind t c ih =>
    rw [wp_query]
    rcases t with j | (⟨⟩|t)
    · rw [compileQ_instr_bind,close_instr_bind,qWeight_instr_bind]
      apply Finset.sum_congr rfl
      intro n _
      rw [pad_instr]
      exact ih n _ _
    · rw [compileQ_port_bind,close_instr_bind,qWeight_instr_bind]
      change (∑ i : Fin 1, qWeight ev (close impl (compileQ H (c ())) s)
        ((portInstr (E := E) H).branch i (padUnit ρ))) = _
      rw [Fin.sum_univ_one,Circuit.port_branch]
      exact ih () s (turn ((oracleEquiv H).prodCongr (Equiv.refl E)) ρ)
    · rw [compileQ_query_bind,close_query_bind,wq_qWeight_liftU_bind_tsum]
      change (∑' u : sp.Range t × σ, _ * _) = ∑' u : sp.Range t × σ, _ * _
      apply tsum_congr
      intro u
      rw [ih]

private theorem prepared_trace {A : Type} [Fintype A] (ρ : Density A) :
    (prepared ρ).trace = ρ.trace := by
  rw [prepared, Matrix.trace_kronecker, Matrix.trace_single_eq_same, mul_one]

theorem expanded_weight (π : Permutation) (ki ko : Mask) (h : RateMask)
    (impl : QueryImpl sp (StateT σ ProbComp)) (p : QOC (Old E) (portSpec + sp) α)
    (s : σ) (ev : α × σ → Prop) [DecidablePred ev] (ρ : Density (Old E)) :
    wp (bigStep (bank ki ko) h (classicalEnv impl)) (expanded π p)
        (measured ev) s (prepared ρ) =
      qWeight ev (close impl (compileQ (oracle (salted ki ko h π)) p) s) (padUnit ρ) := by
  rw [expanded_wp,old_wp_weight]
  simp only [measured,prepared_trace]
  rfl

end Reduction.ShakePermutation.RoundPort.Player
#print axioms Reduction.ShakePermutation.RoundPort.Player.expanded_weight
