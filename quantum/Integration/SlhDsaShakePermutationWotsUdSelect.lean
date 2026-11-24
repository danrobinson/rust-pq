import Integration.SlhDsaShakePermutationWotsPreSelect
import Integration.SlhDsaShakeXofWotsUd

namespace Reduction.ShakePermutation.SparsePort.Wots.Ud
open Classical OracleComp OracleSpec SLHDSA SLHDSA.Security MLink TweakableHash PQ.Interactive SetOracle Phase
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
variable (S : Sha2Set)
abbrev Spec := Open.preSpecC (Bytes 32) S.Node
abbrev History (_S : Sha2Set) := SM_DT_UD_State (Bytes 32)
attribute [local irreducible] wotsChainTargets

open Pre (draw draw_valid draw_cost draw_close)
variable (world : SM_DT_UD_World)
def response (pk : S.Node) (d : Bytes 32) : Select.Prog S.Node :=
  match world with
  | .real => do let m ← draw ($ᵗ S.Node); Wots.eval S pk d [m]
  | .ideal => draw ($ᵗ S.Node)
theorem response_valid (pk : S.Node) (d : Bytes 32) : valid (input S pk) Prod.fst (response S world pk d) := by
  cases world with
  | real => exact valid_bind _ _ _ _ (draw_valid S pk _) (fun m => eval_valid S pk d [m])
  | ideal => exact draw_valid S pk _
theorem response_cost (pk : S.Node) (d : Bytes 32) :
    WCount Select.wt (simulateQ erase (response S world pk d)) 483 := by
  cases world with
  | real => simp only [response,simulateQ_bind]; exact WCount.bind (draw_cost _) (fun m => eval_cost S pk d [m])
  | ideal => exact (draw_cost _).mono (by decide)

def handler (pk : S.Node) : QueryImpl (Spec S) (StateT (History S) Select.Prog)
  | .inl n => StateT.mk fun s => do
    let v ← (Tagged (Bytes 32)).query (.inl n)
    pure (v,s)
  | .inr (.inl t) => StateT.mk fun (l,c) =>
    if wotsChainTargets S.vp ≤ l.length ∨ ¬TweakFresh id l c t then pure (none,(l,c))
    else do
      let y ← response S world pk t
      pure (some y,(l ++ [t],c))
  | .inr (.inr t) => StateT.mk fun (l,c) =>
    if TweakReserved (Q:=Bytes 32) id l t.2.1 then pure (none,(l,c))
    else do
      let y ← Wots.eval S pk t.2.1 t.2.2
      pure (some y,(l,c ++ [t.2.1]))

def prog {A : Type} (pk : S.Node) (o : OracleComp (Spec S) A) (s : History S) := (simulateQ (handler S world pk) o).run s

theorem valid_prog {A : Type} (pk : S.Node) (o : OracleComp (Spec S) A) (s : History S) :
    valid (input S pk) Prod.fst (prog S world pk o s) := by
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
        · apply valid_bind _ _ _ _ (response_valid S world pk d)
          intro _; trivial
      · change valid _ _ (if _ then _ else _)
        split
        · trivial
        · exact valid_bind _ _ _ _ (eval_valid S pk _ _) (fun _ => trivial)
    · rintro ⟨v,s'⟩; exact ih v s'

def game (seeds : ProbComp S.Node) (f : Bytes 32 → Words → Words) :=
  udWithEval (ShakeXof.baseUd S seeds) (fun p d m => Wots.value S f p d [m]) (fun _ p d xs => Wots.value S f p d xs)

theorem close_step (seeds : ProbComp S.Node) (pk : S.Node) (f : Bytes 32 → Words → Words)
    (i : (Spec S).Domain) (s : History S) :
    (SM_DT_UD_oracles world (game S seeds f) pk i).run s = simulateQ (Select.close f) ((handler S world pk i).run s) := by
  obtain ⟨l,c⟩ := s
  rcases i with n|d|t
  · simp [SM_DT_UD_oracles,handler,Select.close]; rfl
  · change (SM_DT_UD_challengeOracle world _ pk d).run (l,c) = _
    by_cases h : wotsChainTargets S.vp ≤ l.length ∨ ¬TweakFresh id l c d <;>
      cases world <;> simp [SM_DT_UD_challengeOracle,SM_DT_UD_response,response,handler,game,ShakeXof.baseUd,ShakeXof.basePre,udWithEval,h,eval_close,draw_close]
  · change (collectionOracle (Q := Bytes 32) id (game S seeds f).thColl pk t).run (l,c) = _
    by_cases h : TweakReserved (Q := Bytes 32) id l t.2.1 <;>
      simp [collectionOracle,handler,game,ShakeXof.baseUd,ShakeXof.basePre,h,eval_close,udWithEval]

theorem close_prog {A : Type} (seeds : ProbComp S.Node) (pk : S.Node) (f : Bytes 32 → Words → Words)
    (o : OracleComp (Spec S) A) (s : History S) :
    (simulateQ (SM_DT_UD_oracles world (game S seeds f) pk) o).run s = simulateQ (Select.close f) (prog S world pk o s) := by
  let native : QueryImpl (Spec S) (StateT (History S) ProbComp) := SM_DT_UD_oracles world (game S seeds f) pk
  change (simulateQ native o).run s = _
  induction o using OracleComp.inductionOn generalizing s with
  | pure x => simp [prog]
  | query_bind t k ih =>
    simp only [prog,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    rw [show (native t).run s = _ from close_step S world seeds pk f t s]
    exact bind_congr fun z => ih z.1 z.2

private theorem charge (pk : S.Node) (i : (Spec S).Domain) (s : History S) :
    WCount Select.wt (simulateQ erase ((handler S world pk i).run s)) (if i.isRight then 483 else 0) := by
  obtain ⟨l,c⟩ := s
  rcases i with n|d|t
  · simp only [handler,StateT.run_mk,simulateQ_bind,simulateQ_spec_query,erase,simulateQ_pure,wCount_query_bind]
    exact ⟨Nat.zero_le _,fun _ => trivial⟩
  · change WCount _ (simulateQ erase (if _ then _ else _)) 483
    split
    · rw [simulateQ_pure]; trivial
    · simp only [simulateQ_bind,simulateQ_pure]
      exact WCount.bind (m:=0) (response_cost S world pk d) (fun _ => wCount_pure _ _ 0)
  · change WCount _ (simulateQ erase (if _ then _ else _)) 483
    split
    · rw [simulateQ_pure]; trivial
    · simp only [simulateQ_bind,simulateQ_pure]
      exact WCount.bind (m:=0) (eval_cost S pk _ _) (fun _ => wCount_pure _ _ 0)

theorem prog_cost {A : Type} (pk : S.Node) (o : OracleComp (Spec S) A) (s : History S) (Q : ℕ)
    (bound : IsQueryBoundP o (fun i => i.isRight = true) Q) :
    CountBound (fun i => i.isRight = true) (simulateQ erase (prog S world pk o s)) (483*Q) := by
  apply (countBound_iff_wCount _ _ _).mpr
  induction o using OracleComp.inductionOn generalizing s Q with
  | pure x => simp [prog,wCount_pure]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at bound
    simp only [prog,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    have h := WCount.bind (charge S world pk t s) (fun z => ih z.1 z.2 _ (bound.2 z.1))
    exact h.mono (by split_ifs <;> simp_all; omega)

end
end Reduction.ShakePermutation.SparsePort.Wots.Ud
#print axioms Reduction.ShakePermutation.SparsePort.Wots.Ud.prog_cost
