import Integration.SlhDsaShakePermutationLongTargetWitness
import Integration.SlhDsaShakePermutationLongTargetNumbers
import Integration.SlhDsaShakePermutationLongPinned
import Integration.SlhDsaShakePermutationItsrLog

/-! Quantum second phase of the multi-block target search. The adversary
has a coherent forward and inverse public port at all times and may choose
the final bounded candidate after measuring its quantum work registers. -/
namespace Reduction.ShakePermutation.ItsrLabel.Target
open Classical MLink SLHDSA Quantum OracleSpec OracleComp PQ.Interactive ENNReal SetOracle
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
variable {A E : Type} [Fintype E] [DecidableEq E]

def hit (S : Sha2Set) (π : Permutation) (go : Goal S) (xs : List Rate) :=
  go (Fix.fix (rateOf ∘ Fix.overwrite π) xs) = some ((SkFormat.split S (Fix.ordinary π xs)).1)

def observe (π : Permutation) (H : Table) (path : A → List Rate) (a : A) :=
  (replay π H (path a).reverse).log

theorem observe_evidence (S π H L) (go : Goal S) (path : A → List Rate) {a : A}
    (ne : path a ≠ []) (len : (path a).length ≤ L) (win : hit S (perm π H) go (path a)) :
    Long.Pinned.evidence (label S π L go) (3*L) (observe π H path a) H := by
  refine ⟨fun D mem => certify S π H L go D (path a) ne len mem win,?_,consistent π H (path a).reverse⟩
  simp only [observe,(replay_length ..).1,List.length_reverse]
  exact Nat.mul_le_mul_left _ len

theorem observe_cost (π : Permutation) (L : ℕ) (path : A → List Rate) (a : A) (len : (path a).length ≤ L) :
    EvalCost (fun H : Table => (pure (observe π H path a) : ProbComp Log)) (3*L) := by
  have cl := (replay_cost π (path a).reverse).map Report.log
  apply EvalCost.mono _ (Nat.mul_le_mul_left 3 len)
  simpa only [observe,List.length_reverse,map_pure] using cl

theorem fixed_search (S : Sha2Set) (π : Permutation) (hp : ¬irregular π) (he : ¬Pairs.exceptional π)
    (pins : Bank) {Q L : ℕ} (go : Goal S) (clean : label S π L go pins = true)
    (M : (Port → Words) → Closed (WS Port Words E) A) (hm : PUE (spec := unifSpec) cnt0 M Q)
    (ρ : Matrix (WS Port Words E) (WS Port Words E) ℂ) (pos : ρ.PosSemidef) (tr : ρ.trace = 1)
    (path : A → List Rate) (ne : ∀ a, path a ≠ []) (len : ∀ a, (path a).length ≤ L) :
    let q := 16*Q + 3*L
    uniformMean (fun H : Table => let F := Long.Pinned.complete pins H
      qWeight (fun a => hit S (perm π F) go (path a)) (M (oracle (perm π F))) ρ) ≤
      ENNReal.ofReal ((2*((3*L:ℕ):ℝ)*Real.sqrt (Fintype.card Words : ℝ)⁻¹ +
        q*(4*Real.sqrt (rateBound S (pins.size+(q+1))).toReal))^2) := by
  obtain ⟨m,hm,eq⟩ := ItsrCircuit.lift_machine π hm
  let run := fun H => (observe π H path) <$> m H
  have cost : PUE (spec := unifSpec) cnt0 run (16*Q+3*L) := by
    have endCost (a : A) := (observe_cost π L path a (len a)) (ItsrCircuit.Mem (WS Port Words E)) Log
      (fun v _ => pure v) 0 (fun v => PUE.pure v 0)
    simpa only [run,map_eq_bind_pure_comp,liftU_pure,pure_bind,Nat.zero_add,Function.comp_def] using hm.bind endCost
  let σ := SparsePort.Workspace.state (Y := Words) ItsrCircuit.base ρ
  let tag := label S π L go
  let q := 16*Q+3*L
  apply le_trans _ (Long.Pinned.machine tag pins run q (3*L) cost σ
    (SparsePort.Workspace.state_pos _ _ pos) ((SparsePort.Workspace.state_trace ..).trans tr) _
    (rate_finite S (pins.size+(q+1))) clean (stable_bad S π L go)
      (fun D => mean_step S π L go hp he D (pins.size+(q+1))))
  apply Classic.mean_mono
  intro H
  let F := Long.Pinned.complete pins H
  rw [← eq F (fun a => hit S (perm π F) go (path a)) ρ]
  change _ ≤ qWeight _ ((observe π F path) <$> m F) σ
  rw [qWeight_map]
  apply qWeight_mono
  exact fun a => observe_evidence S π F L go path (ne a) (len a)

theorem fixed_search_benchmark (S : Sha2Set) (π : Permutation) (hp : ¬irregular π) (he : ¬Pairs.exceptional π)
    (pins : Bank) (pinCap : pins.size ≤ 2^104) (go : Goal S) (clean : label S π 17 go pins = true)
    (M : (Port → Words) → Closed (WS Port Words E) A) (hm : PUE (spec := unifSpec) cnt0 M (2^41))
    (ρ : Matrix (WS Port Words E) (WS Port Words E) ℂ) (pos : ρ.PosSemidef) (tr : ρ.trace = 1)
    (path : A → List Rate) (ne : ∀ a, path a ≠ []) (len : ∀ a, (path a).length ≤ 17) :
    uniformMean (fun H : Table => let F := Long.Pinned.complete pins H
      qWeight (fun a => hit S (perm π F) go (path a)) (M (oracle (perm π F))) ρ) ≤ ((2:ℝ≥0∞)^28)⁻¹ := by
  apply (fixed_search S π hp he pins go clean M hm ρ pos tr path ne len).trans
  apply (ENNReal.ofReal_le_ofReal (price_small S pinCap (show 16*2^41+3*17 ≤ 2^46 by decide +kernel)
    (show 3*17 ≤ 2^12 by decide +kernel))).trans_eq
  rw [ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_ofNat]

end
end Reduction.ShakePermutation.ItsrLabel.Target
#print axioms Reduction.ShakePermutation.ItsrLabel.Target.fixed_search_benchmark
