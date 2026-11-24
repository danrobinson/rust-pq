import Integration.SlhDsaShakeXofClassicalReadHop
import Integration.SlhDsaShakePermutationColumnGame

namespace Reduction.ShakeXof
open OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal Ideal.HP QItsr
open scoped ComplexOrder Kronecker

private theorem trace_length {X Y W α : Type} [Fintype W] (G : X → Y)
    (P : QOC W (unifSpec + (X →ₒ Y)) α) (n : ℕ) (log : List X)
    (count : CountBound (QC W isR) P n) :
    AllQueries (fun _ => True) (fun z : α × List X => z.2.length ≤ log.length+n) (close (trImpl G) P log) := by
  induction P using OracleComp.inductionOn generalizing n log with
  | pure a => exact Nat.le_add_right ..
  | query_bind t f ih =>
    rcases t with j|u|x
    · rw [close_instr_bind]
      exact ⟨trivial, fun i => ih i n log (count i)⟩
    · rw [close_unif_bind _ (show ForwardsUnif (trImpl (spec := X →ₒ Y) G) from fun _ _ => rfl)]
      exact ⟨trivial, fun i => ih i n log (count i)⟩
    · have hc : 0 < n ∧ ∀ ans, CountBound (QC W isR) (f ans) (n-1) := count
      rw [close_query_bind]
      change AllQueries _ _ (liftU (pure (G x,log++[x])) >>= _)
      rw [liftU_pure,pure_bind]
      apply QMsg.allQ_mono (fun _ h => h) _ (ih _ (n-1) (log++[x]) (hc.2 _))
      intro z hz
      simp only [List.length_append,List.length_singleton] at hz
      omega

/-- Reprogramming one uniformly hidden row of both ports of a quantum
machine. The public quantum port incurs q coherent queries and the separately
exposed classical port receives t adaptive reads, in arbitrary order.
The difference in acceptance is bounded even when both ports access the
same oracle. -/
theorem mixed_row_reprogram {K X Y E : Type} [Fintype K] [Nonempty K] [DecidableEq K]
    [Fintype X] [Nonempty X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
    [Fintype E] [DecidableEq E] (G : X → Y) (H : K → X → Y) (row : X → K)
    (agree : ∀ k z, row z ≠ k → H k z = G z)
    (Q : (X → Y) → QOC (WS X Y E) (unifSpec + (X →ₒ Y)) Bool)
    (q t : ℕ) (coherent : PU Q q)
    (reads : ∀ h, CountBound (QC (WS X Y E) isR) (Q h) t)
    (ρ : SubState ((X × Y) × E)) (unit : ρ.matrix.trace = 1) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    let accept := fun (a b : X → Y) => qWeight (fun z => z.1 = true) (close (trImpl a) (Q b) []) M
    SetOracle.uniformMean (fun k => accept (H k) (H k)) ≤ accept G G +
      ENNReal.ofReal (8*(q:ℝ)^2 / Fintype.card K) +
      ((t:ℝ≥0∞)^(2⁻¹:ℝ)+2*q)^2 / Fintype.card K := by
  classical
  intro M accept
  let run := fun h => close (trImpl (spec := X →ₒ Y) G) (Q h) []
  have hc : PUE (spec := unifSpec) cnt0 run q :=
    PUE.close (fun _ => trImpl G) (fun _ _ => EvalCost.const _) coherent.toPUE []
  let bad := fun k z => decide (row z = k)
  have hop (k : K) := freeze_classical_reads (sp := X →ₒ Y) (H k) G (bad k)
    (fun z h => agree k z (by simpa [bad] using h)) (Q (H k)) M
    (ρ.prod (SubState.basis ())).posSemidef (by simp [M,Matrix.trace_kronecker,unit])
  have coherentHop := ShakePermutation.Program.fiber_game G H (fun z => some (row z))
    (fun k z ne => agree k z (fun h => ne (congrArg some h)))
    (fun h => Prod.fst <$> run h) q (PUE.map _ hc) ρ
  simp only [qWeight_map] at coherentHop
  let keys := fun z : Bool × List X => ((z.2.take t).map row).toFinset
  have hk (z) : (keys z).card ≤ t := (List.toFinset_card_le ..).trans (by simp)
  obtain ⟨x,hx,eval⟩ := hc.exists_prog_qprob
  have hit := hidden_row_list_bound LocalSig.Interp.instruments G row H agree x ρ q hx
    (fun p => keys p.2) t (fun p => hk p.2)
  have same (k : K) : qWeight (fun z : Bool × List X => z.2.any (bad k) = true) (run (H k)) M =
      qprob LocalSig.Interp.instruments (H k) x ρ (fun p => k ∈ keys p.2) := by
    rw [eval (fun z => k ∈ keys z)]
    apply qWeight_congr_allQ (trace_length G (Q _) t [] (reads _))
    intro z hz
    have e : z.2.take t = z.2 := List.take_of_length_le (by simpa using hz)
    dsimp only [keys]
    rw [e]
    simp [bad]
  have badHop : SetOracle.uniformMean (fun k => qWeight (fun z => z.2.any (bad k) = true) (run (H k)) M) ≤ ((t:ℝ≥0∞)^(2⁻¹:ℝ)+2*q)^2 / Fintype.card K := by
    simp_rw [same]
    simpa [SetOracle.uniformMean, unifW, ← Finset.sum_mul, div_eq_mul_inv,
      mul_comm (Fintype.card K : ℝ≥0∞)⁻¹] using hit
  apply (Finset.sum_le_sum (fun k _ => mul_le_mul' (a := unifW K k) le_rfl (hop k))).trans
  simp only [mul_add,Finset.sum_add_distrib]
  exact add_le_add coherentHop badHop

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.mixed_row_reprogram
