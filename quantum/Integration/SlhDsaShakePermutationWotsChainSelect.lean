import Integration.SlhDsaShakePermutationWotsLeaf
import Integration.SlhDsaShakeXofWotsTcr

namespace Reduction.ShakePermutation.SparsePort.Wots.Chain
open Classical OracleComp OracleSpec SLHDSA SLHDSA.Security MLink TweakableHash PQ.Interactive SetOracle Phase
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
variable (S : Sha2Set)
abbrev Spec := Open.tcrSpecC (Bytes 32) S.Node
abbrev History := SM_DT_TCR_State (Bytes 32) S.Node
attribute [local irreducible] wotsStepTargetsT

def handler (pk : S.Node) : QueryImpl (Spec S) (StateT (History S) Select.Prog)
  | .inl n => StateT.mk fun s => do
    let v ← (Tagged (Bytes 32)).query (.inl n)
    pure (v,s)
  | .inr (.inl t) => StateT.mk fun (l,c) =>
    if wotsStepTargetsT S.vp ≤ l.length ∨ ¬TweakFresh Prod.fst l c t.1 then pure (none,(l,c))
    else do
      let y ← Wots.eval S pk t.1 [t.2]
      pure (some y,(l ++ [t],c))
  | .inr (.inr t) => StateT.mk fun (l,c) =>
    if TweakReserved (Q:=Bytes 32 × S.Node) Prod.fst l t.2.1 then pure (none,(l,c))
    else do
      let y ← Wots.eval S pk t.2.1 t.2.2
      pure (some y,(l,c ++ [t.2.1]))

def prog {A : Type} (pk : S.Node) (o : OracleComp (Spec S) A) (s : History S) := (simulateQ (handler S pk) o).run s

theorem valid_prog {A : Type} (pk : S.Node) (o : OracleComp (Spec S) A) (s : History S) :
    valid (input S pk) Prod.fst (prog S pk o s) := by
  induction o using OracleComp.inductionOn generalizing s with
  | pure x => trivial
  | query_bind t k ih =>
    simp only [prog,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    apply valid_bind
    · obtain ⟨l,c⟩ := s
      rcases t with n|d|v
      · exact fun _ => trivial
      · change valid _ _ (if _ then _ else _)
        split
        · trivial
        · exact valid_bind _ _ _ _ (eval_valid S pk d.1 [d.2]) (fun _ => trivial)
      · change valid _ _ (if _ then _ else _)
        split
        · trivial
        · exact valid_bind _ _ _ _ (eval_valid S pk _ _) (fun _ => trivial)
    · rintro ⟨v,s'⟩; exact ih v s'

def game (seeds : ProbComp S.Node) (f : Bytes 32 → Words → Words) :=
  tcrWithEval (ShakeXof.baseWotsTcr S seeds) (fun p d m => Wots.value S f p d [m]) (fun _ p d xs => Wots.value S f p d xs)

theorem close_step (seeds : ProbComp S.Node) (pk : S.Node) (f : Bytes 32 → Words → Words)
    (i : (Spec S).Domain) (s : History S) :
    (SM_DT_TCR_oracles (game S seeds f) pk i).run s = simulateQ (Select.close f) ((handler S pk i).run s) := by
  obtain ⟨l,c⟩ := s
  rcases i with n|d|t
  · simp [SM_DT_TCR_oracles,handler,Select.close]; rfl
  · change (SM_DT_TCR_challengeOracle _ pk d).run (l,c) = _
    by_cases h : wotsStepTargetsT S.vp ≤ l.length ∨ ¬TweakFresh Prod.fst l c d.1 <;>
      simp [SM_DT_TCR_challengeOracle,handler,game,ShakeXof.baseWotsTcr,tcrWithEval,h,eval_close]
  · change (collectionOracle (Q := Bytes 32 × S.Node) Prod.fst (game S seeds f).thColl pk t).run (l,c) = _
    by_cases h : TweakReserved (Q := Bytes 32 × S.Node) Prod.fst l t.2.1 <;>
      simp [collectionOracle,handler,game,ShakeXof.baseWotsTcr,h,eval_close,tcrWithEval]

theorem close_prog {A : Type} (seeds : ProbComp S.Node) (pk : S.Node) (f : Bytes 32 → Words → Words)
    (o : OracleComp (Spec S) A) (s : History S) :
    (simulateQ (SM_DT_TCR_oracles (game S seeds f) pk) o).run s = simulateQ (Select.close f) (prog S pk o s) := by
  let native : QueryImpl (Spec S) (StateT (History S) ProbComp) := SM_DT_TCR_oracles (game S seeds f) pk
  change (simulateQ native o).run s = _
  induction o using OracleComp.inductionOn generalizing s with
  | pure x => simp [prog]
  | query_bind t k ih =>
    simp only [prog,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    rw [show (native t).run s = _ from close_step S seeds pk f t s]
    exact bind_congr fun z => ih z.1 z.2

private theorem charge (pk : S.Node) (i : (Spec S).Domain) (s : History S) :
    WCount Select.wt (simulateQ erase ((handler S pk i).run s)) (if i.isRight then 483 else 0) := by
  obtain ⟨l,c⟩ := s
  rcases i with n|d|t
  · simp only [handler,StateT.run_mk,simulateQ_bind,simulateQ_spec_query,erase,simulateQ_pure,wCount_query_bind]
    exact ⟨Nat.zero_le _,fun _ => trivial⟩
  · change WCount _ (simulateQ erase (if _ then _ else _)) 483
    split
    · rw [simulateQ_pure]; trivial
    · simp only [simulateQ_bind,simulateQ_pure]
      exact WCount.bind (m:=0) (eval_cost S pk d.1 [d.2]) (fun _ => wCount_pure _ _ 0)
  · change WCount _ (simulateQ erase (if _ then _ else _)) 483
    split
    · rw [simulateQ_pure]; trivial
    · simp only [simulateQ_bind,simulateQ_pure]
      exact WCount.bind (m:=0) (eval_cost S pk _ _) (fun _ => wCount_pure _ _ 0)

theorem prog_cost {A : Type} (pk : S.Node) (o : OracleComp (Spec S) A) (s : History S) (Q : ℕ)
    (bound : IsQueryBoundP o (fun i => i.isRight = true) Q) :
    CountBound (fun i => i.isRight = true) (simulateQ erase (prog S pk o s)) (483*Q) := by
  apply (countBound_iff_wCount _ _ _).mpr
  induction o using OracleComp.inductionOn generalizing s Q with
  | pure x => simp [prog,wCount_pure]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at bound
    simp only [prog,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    have h := WCount.bind (charge S pk t s) (fun z => ih z.1 z.2 _ (bound.2 z.1))
    exact h.mono (by split_ifs <;> simp_all; omega)

end
end Reduction.ShakePermutation.SparsePort.Wots.Chain
#print axioms Reduction.ShakePermutation.SparsePort.Wots.Chain.prog_cost
