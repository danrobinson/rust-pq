import Integration.SlhDsaShakePermutationItsrRecorded
import Integration.SlhDsaShakePermutationItsrLift

namespace Reduction.ShakePermutation.ItsrLabel
open Classical MLink SLHDSA Quantum OracleSpec OracleComp PQ.Interactive ENNReal SetOracle
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 11000
set_option maxHeartbeats 1300000
abbrev Pair (N : ℕ) := Option (ShakeApi.Input N × ShakeApi.Input N)
def win (S : Sha2Set) (π : Permutation) {N : ℕ} (v : Pair N) :=
  ∃ x y, v = some (x,y) ∧ x ≠ y ∧
    DigestTransport.coveringDigest S.vp (answer S (lanes π) (List.ofFn x.2)) =
    DigestTransport.coveringDigest S.vp (answer S (lanes π) (List.ofFn y.2))

def blocks {N : ℕ} (x : ShakeApi.Input N) := (messageBlocks (sp (List.ofFn x.2))).reverse

def recordPair (π : Permutation) (H : Table) {N : ℕ} : Pair N → Log
  | none => []
  | some (x,y) => (replay π H (blocks x)).log ++ (replay π H (blocks y)).log

private theorem block_length {N : ℕ} (x : ShakeApi.Input N) :
    0 < (blocks x).length ∧ (blocks x).length ≤ Completion.blockCap N := by
  simp only [blocks,List.length_reverse,messageBlocks_length,sp,List.length_map,List.length_ofFn,Completion.blockCap]
  exact ⟨by omega,Nat.succ_le_succ (Nat.div_le_div_right (Nat.le_of_lt_succ x.1.isLt))⟩

private theorem block_inj (N : ℕ) : Function.Injective (blocks (N := N)) := by
  intro x y eq
  have he : messageBlocks (sp (List.ofFn x.2)) = messageBlocks (sp (List.ofFn y.2)) := List.reverse_injective eq
  apply (Completion.address (N := N) le_rfl).injective
  have cong {l r : List Rate} (a : l.length ≤ Completion.blockCap N) (b : r.length ≤ Completion.blockCap N) (same : l = r) :
      BList.ofList l a = BList.ofList r b := by cases same; rfl
  exact cong (by simpa only [blocks,List.length_reverse] using (block_length x).2)
    (by simpa only [blocks,List.length_reverse] using (block_length y).2) he

theorem winning_evidence (S π H L) {N : ℕ} (cap : Completion.blockCap N ≤ L) {p : Pair N}
    (h : win S (perm π H) p) : evidence S π L (6*L) (recordPair π H p) H := by
  obtain ⟨x,y,rfl,ne,dig⟩ := h
  have hx := block_length x
  have hy := block_length y
  have cond := (replay_digest S π H (List.ofFn x.2)).symm.trans (dig.trans (replay_digest S π H (List.ofFn y.2)))
  refine ⟨fun D logged => certify S π H L D (blocks x) (blocks y)
    (fun e => by rw [e] at hx; exact Nat.lt_irrefl 0 hx.1)
    (fun e => by rw [e] at hy; exact Nat.lt_irrefl 0 hy.1)
    (hx.2.trans cap) (hy.2.trans cap) ((block_inj N).ne ne) logged cond,?_,?_⟩
  · simp only [recordPair,List.length_append,(replay_length ..).1]
    omega
  · intro i v hv
    obtain a|b := List.mem_append.mp hv
    · exact consistent π H (blocks x) i v a
    · exact consistent π H (blocks y) i v b

private theorem step_cost (π : Permutation) (p : Report) (b : Rate) :
    EvalCost (fun H : Table => (pure (step π H p b) : ProbComp Report)) 3 := by
  intro W _ _ β f q hf
  simp only [liftU_pure,pure_bind]
  let r := rateXor b (rateOf (result p))
  let mid := fun a : Words => (Tails.layout π).middle r p.cap (capOf a)
  exact PUE.eval (mask false r) _ _ (fun a => PUE.eval (mask true (mid a).1) _ _ (fun v =>
    PUE.eval (tailHead ((Tails.layout π).finish (mid a).2 (capOf v)))
      (fun y H => f (push π p b a v y) H) q (fun _ => hf _)))

private theorem replay_cost (π : Permutation) (xs : List Rate) :
    EvalCost (fun H : Table => (pure (replay π H xs) : ProbComp Report)) (3*xs.length) := by
  induction xs with
  | nil => exact EvalCost.const (X := Addr) (Y := Words) (pure empty)
  | cons b bs ih =>
    simpa only [pure_bind,replay,List.length_cons,Nat.mul_add,Nat.mul_one] using
      EvalCost.bind ih (fun p => step_cost π p b)

theorem log_cost (π : Permutation) {N L : ℕ} (cap : Completion.blockCap N ≤ L) (o : Pair N) :
    EvalCost (fun H : Table => (pure (recordPair π H o) : ProbComp Log)) (6*L) := by
  obtain _|⟨x,y⟩ := o
  · exact (EvalCost.const (X := Addr) (Y := Words) (pure ([] : Log))).mono (Nat.zero_le _)
  · have h := EvalCost.bind (replay_cost π (blocks x)) (fun r => (replay_cost π (blocks y)).map (fun s => r.log ++ s.log))
    have len₁ := (block_length x).2.trans cap
    have len₂ := (block_length y).2.trans cap
    apply EvalCost.mono _ (show 3*(blocks x).length+3*(blocks y).length ≤ 6*L by omega)
    simpa only [map_pure,pure_bind,recordPair] using h

theorem fixed_search (S π L) (hp : ¬irregular π) (he : ¬Pairs.exceptional π) {N Q : ℕ} (cap : Completion.blockCap N ≤ L)
    {E : Type} [Fintype E] [DecidableEq E] (M : (Port → Words) → Closed (WS Port Words E) (Pair N))
    (hm : PUE (spec := unifSpec) cnt0 M Q) (ρ : Matrix (WS Port Words E) (WS Port Words E) ℂ)
    (pos : ρ.PosSemidef) (tr : ρ.trace = 1) :
    uniformMean (fun H => qWeight (win S (perm π H)) (M (oracle (perm π H))) ρ) ≤
      ENNReal.ofReal (price S (16*Q+6*L) (6*L)) := by
  obtain ⟨m,hm,eq⟩ := ItsrCircuit.lift_machine π hm
  let run := fun H => (recordPair π H) <$> m H
  have cost : PUE (spec := unifSpec) cnt0 run (16*Q+6*L) := by
    have endCost (p : Pair N) := (log_cost π cap p) (ItsrCircuit.Mem (WS Port Words E)) Log (fun y _ => pure y) 0
      (fun y => PUE.pure y 0)
    simpa only [run,map_eq_bind_pure_comp,liftU_pure,pure_bind,Nat.zero_add,Function.comp_def] using hm.bind endCost
  let σ := SparsePort.Workspace.state (Y := Words) ItsrCircuit.base ρ
  apply le_trans _ (recorded_security S π L hp he run _ _ cost σ
    (SparsePort.Workspace.state_pos _ _ pos) ((SparsePort.Workspace.state_trace ..).trans tr))
  apply Classic.mean_mono
  intro H
  rw [← eq H (win S (perm π H)) ρ]
  change _ ≤ qWeight _ ((recordPair π H) <$> m H) σ
  rw [qWeight_map]
  apply qWeight_mono
  exact fun _ => winning_evidence S π H L cap

end
end Reduction.ShakePermutation.ItsrLabel
