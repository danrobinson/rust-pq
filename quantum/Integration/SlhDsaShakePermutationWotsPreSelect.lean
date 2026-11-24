import Integration.SlhDsaShakePermutationWotsLeaf
import Integration.SlhDsaShakeXofWotsPre

namespace Reduction.ShakePermutation.SparsePort.Wots.Pre
open Classical OracleComp OracleSpec SLHDSA SLHDSA.Security MLink TweakableHash PQ.Interactive SetOracle Phase
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
variable (S : Sha2Set)
abbrev Spec := Open.preSpecC (Bytes 32) S.Node
abbrev History := SM_DT_PRE_State (Bytes 32) S.Node
attribute [local irreducible] wotsChainTargets

def draw {A : Type} (p : ProbComp A) : Select.Prog A :=
  simulateQ (fun n => liftM ((Tagged (Bytes 32)).query (.inl n))) p

theorem draw_close {A : Type} (f : Bytes 32 → Words → Words) (p : ProbComp A) :
    simulateQ (Select.close f) (draw p) = p := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [draw]
  | query_bind n k ih =>
    simp only [draw,simulateQ_bind,simulateQ_spec_query]
    exact bind_congr fun i => ih i

theorem draw_valid {A : Type} (pk : S.Node) (p : ProbComp A) : valid (input S pk) Prod.fst (draw p) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp only [draw,simulateQ_pure]; trivial
  | query_bind n k ih =>
    simp only [draw,simulateQ_bind,simulateQ_spec_query]
    exact ih

theorem draw_cost {A : Type} (p : ProbComp A) : WCount Select.wt (simulateQ erase (draw p)) 0 := by
  induction p using OracleComp.inductionOn with
  | pure x => simp only [draw,simulateQ_pure]; trivial
  | query_bind n k ih =>
    simp only [draw,simulateQ_bind,simulateQ_spec_query,erase,wCount_query_bind]
    exact ⟨Nat.zero_le _,fun i => ih i⟩

def handler (pk : S.Node) : QueryImpl (Spec S) (StateT (History S) Select.Prog)
  | .inl n => StateT.mk fun s => do
    let v ← (Tagged (Bytes 32)).query (.inl n)
    pure (v,s)
  | .inr (.inl t) => StateT.mk fun (l,c) =>
    if wotsChainTargets S.vp ≤ l.length ∨ ¬TweakFresh Prod.fst l c t then pure (none,(l,c))
    else do
      let m ← draw ($ᵗ S.Node)
      let y ← Wots.eval S pk t [m]
      pure (some y,(l ++ [(t,m)],c))
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
        · apply valid_bind _ _ _ _ (draw_valid S pk _)
          intro m
          exact valid_bind _ _ _ _ (eval_valid S pk d [m]) (fun _ => trivial)
      · change valid _ _ (if _ then _ else _)
        split
        · trivial
        · exact valid_bind _ _ _ _ (eval_valid S pk _ _) (fun _ => trivial)
    · rintro ⟨v,s'⟩; exact ih v s'

def game (seeds : ProbComp S.Node) (f : Bytes 32 → Words → Words) :=
  preWithEval (ShakeXof.basePre S seeds) (fun p d m => Wots.value S f p d [m]) (fun _ p d xs => Wots.value S f p d xs)

theorem close_step (seeds : ProbComp S.Node) (pk : S.Node) (f : Bytes 32 → Words → Words)
    (i : (Spec S).Domain) (s : History S) :
    (SM_DT_PRE_oracles (game S seeds f) pk i).run s = simulateQ (Select.close f) ((handler S pk i).run s) := by
  obtain ⟨l,c⟩ := s
  rcases i with n|d|t
  · simp [SM_DT_PRE_oracles,handler,Select.close]; rfl
  · change (SM_DT_PRE_challengeOracle _ pk d).run (l,c) = _
    by_cases h : wotsChainTargets S.vp ≤ l.length ∨ ¬TweakFresh Prod.fst l c d <;>
      simp [SM_DT_PRE_challengeOracle,handler,game,ShakeXof.basePre,preWithEval,h,eval_close,draw_close]
  · change (collectionOracle (Q := Bytes 32 × S.Node) Prod.fst (game S seeds f).thColl pk t).run (l,c) = _
    by_cases h : TweakReserved (Q := Bytes 32 × S.Node) Prod.fst l t.2.1 <;>
      simp [collectionOracle,handler,game,ShakeXof.basePre,h,eval_close,preWithEval]

theorem close_prog {A : Type} (seeds : ProbComp S.Node) (pk : S.Node) (f : Bytes 32 → Words → Words)
    (o : OracleComp (Spec S) A) (s : History S) :
    (simulateQ (SM_DT_PRE_oracles (game S seeds f) pk) o).run s = simulateQ (Select.close f) (prog S pk o s) := by
  let native : QueryImpl (Spec S) (StateT (History S) ProbComp) := SM_DT_PRE_oracles (game S seeds f) pk
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
      exact WCount.bind (m:=483) (draw_cost _) (fun m => (WCount.bind (m:=0) (eval_cost S pk d [m]) (fun _ => wCount_pure _ _ 0)))
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
end Reduction.ShakePermutation.SparsePort.Wots.Pre
#print axioms Reduction.ShakePermutation.SparsePort.Wots.Pre.prog_cost
