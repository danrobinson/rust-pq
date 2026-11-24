import Integration.SlhDsaShakePermutationSparseHash

/-! Lowering the native TCR selection oracle to actual sponge rounds,
including the challenge-freshness and collection-clash rules. -/
namespace Reduction.ShakePermutation.SparsePort.Select
open Classical MLink OracleComp OracleSpec SLHDSA TweakableHash PQ.Interactive SetOracle Phase
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

variable (S : Sha2Set) (ar : ℕ)
abbrev M := Arity.Msg S ar
abbrev History := SM_DT_TCR_State (Bytes 32) (M S ar)
abbrev Spec := unifSpec + (SM_DT_TCR_challengeSpec (Bytes 32) (M S ar) S.Node +
  (((_ : Unit) × Bytes 32 × List S.Node) →ₒ Option S.Node))
abbrev Prog := OracleComp (Tagged (Bytes 32))
attribute [local irreducible] arityTargets

def handler (pk : S.Node) : QueryImpl (Spec S ar) (StateT (History S ar) Prog)
  | .inl n => StateT.mk fun s => do
    let v ← (Tagged (Bytes 32)).query (.inl n)
    pure (v,s)
  | .inr (.inl tm) => StateT.mk fun (l,c) =>
    if arityTargets S.vp ar ≤ l.length ∨ ¬TweakFresh Prod.fst l c tm.1 then pure (none,(l,c))
    else do
      let y ← evalHash S pk tm.1 tm.2.val
      pure (some y,(l ++ [tm],c))
  | .inr (.inr t) => StateT.mk fun (l,c) =>
    if TweakReserved (Q := Bytes 32 × M S ar) Prod.fst l t.2.1 then pure (none,(l,c))
    else do
      let y ← evalHash S pk t.2.1 t.2.2
      pure (some y,(l,c ++ [t.2.1]))

def prog {A : Type} (pk : S.Node) (p : OracleComp (Spec S ar) A) (s : History S ar) :=
  (simulateQ (handler S ar pk) p).run s

theorem valid_prog {A : Type} (pk : S.Node) (h : ar ≤ 2) (p : OracleComp (Spec S ar) A) (s : History S ar) :
    valid (Arity.input S ar pk h) Prod.fst (prog S ar pk p s) := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure x => trivial
  | query_bind i k ih =>
    simp only [prog,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    apply valid_bind
    · obtain ⟨l,c⟩ := s
      rcases i with n|tm|t
      · exact fun _ => trivial
      · change valid _ _ (if _ then _ else _)
        split
        · trivial
        · apply valid_bind _ _ _ _ (evalHash_valid S pk ar h _ _)
          intro; trivial
      · change valid _ _ (if _ then _ else _)
        split
        · trivial
        · apply valid_bind _ _ _ _ (evalHash_valid S pk ar h _ _)
          intro; trivial
    · rintro ⟨v,s'⟩; exact ih v s'

def close (f : Bytes 32 → Words → Words) : QueryImpl (Tagged (Bytes 32)) ProbComp
  | .inl n => liftM (unifSpec.query n)
  | .inr (d,w) => pure (f d w)

def value (f : Bytes 32 → Words → Words) (pk : S.Node) (d : Bytes 32) (xs : List S.Node) :=
  (SkFormat.split S ((messageBlocks (sp (ShakeXof.thBytes S pk d xs))).foldl
    (fun w r => f d (join (rateXor r (rateOf w)) (capOf w))) 0)).1

theorem close_hash (f : Bytes 32 → Words → Words) (pk : S.Node) (d : Bytes 32) (xs : List S.Node) :
    simulateQ (close f) (evalHash S pk d xs) = pure (value S f pk d xs) := by
  have step (w : Words) (rs : List Rate) : simulateQ (close f) (Phase.absorb d w rs) =
      pure (rs.foldl (fun z r => f d (join (rateXor r (rateOf z)) (capOf z))) w) := by
    induction rs generalizing w with
    | nil => exact simulateQ_pure _ _
    | cons r rs ih =>
      simp only [Phase.absorb,simulateQ_bind,simulateQ_spec_query,close,pure_bind]
      exact ih _
  simp only [evalHash,simulateQ_bind,step,pure_bind,simulateQ_pure,value]

theorem value_actual (π : Permutation) (pk : S.Node) (d : Bytes 32) (xs : List S.Node) :
    value S (fun _ => π) pk d xs = (primitives (lanes π) S.vp.params).Thash pk d xs := by
  change (SkFormat.split S (Fix.ordinary π _)).1 = hash (lanes π) _ _
  rw [← Arity.fmt S pk,← hash_prefix,answer_blocks,← ShakeXof.head_eq_prefix (ShakeXof.node_le_digest S),SkFormat.split_fst]
  apply Vector.ext; intro i hi; simp [ShakeXof.head]

def game (seeds : ProbComp S.Node) (f : Bytes 32 → Words → Words) :=
  tcrWithEval (ShakeXof.Arity.base S ar seeds) (fun pk d m => value S f pk d m.val)
    (fun _ pk d xs => value S f pk d xs)

theorem close_step (seeds : ProbComp S.Node) (pk : S.Node) (f : Bytes 32 → Words → Words)
    (i : (Spec S ar).Domain) (s : History S ar) :
    (SM_DT_TCR_oracles (game S ar seeds f) pk i).run s = simulateQ (close f) ((handler S ar pk i).run s) := by
  obtain ⟨l,c⟩ := s
  rcases i with n|tm|t
  · simp [SM_DT_TCR_oracles,handler,close]; rfl
  · change (SM_DT_TCR_challengeOracle _ pk tm).run (l,c) = _
    by_cases h : arityTargets S.vp ar ≤ l.length ∨ ¬TweakFresh Prod.fst l c tm.1 <;>
      simp [SM_DT_TCR_challengeOracle,handler,game,ShakeXof.Arity.base,h,close_hash]
  · change (collectionOracle (Q := Bytes 32 × M S ar) Prod.fst (game S ar seeds f).thColl pk t).run (l,c) = _
    by_cases h : TweakReserved (Q := Bytes 32 × M S ar) Prod.fst l t.2.1 <;>
      simp [collectionOracle,handler,game,ShakeXof.Arity.base,h,close_hash]

theorem close_prog {A : Type} (seeds : ProbComp S.Node) (pk : S.Node) (f : Bytes 32 → Words → Words)
    (p : OracleComp (Spec S ar) A) (s : History S ar) :
    (simulateQ (SM_DT_TCR_oracles (game S ar seeds f) pk) p).run s = simulateQ (close f) (prog S ar pk p s) := by
  let native : QueryImpl (Spec S ar) (StateT (History S ar) ProbComp) := SM_DT_TCR_oracles (game S ar seeds f) pk
  change (simulateQ native p).run s = _
  induction p using OracleComp.inductionOn generalizing s with
  | pure x => simp [prog]
  | query_bind i k ih =>
    simp only [prog,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,close_step]
    rw [show (native i).run s = _ from close_step S ar seeds pk f i s]
    apply bind_congr
    rintro ⟨v,s'⟩
    exact ih v s'

end
end Reduction.ShakePermutation.SparsePort.Select
#print axioms Reduction.ShakePermutation.SparsePort.Select.close_prog
