import Ideal.Games.PreDefs
import Ideal.Games.TcrBridge

/-!
# SM-PRE in the ideal-compression model: the VCVio experiment as a two-phase program

`preAdvantage_eq_realGame`: the ideal-model SM-PRE advantage (VCVio's experiment at the hash
built from a uniform table `g`, adversary instantiated at `g`) is the probability that
`Ideal.realGame` returns `true` on the phase programs `preProg₁ emb A`, `preP₂ emb A`.
Query bounds of `preProg₁ emb A` in terms of the adversary's own query bounds.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M M' Y ι : Type} {F : THFam St Blk PkSeed Tweak M Y ι}

/-- The eager phase-one semantics runs a lifted sampling computation unchanged. -/
theorem simulateQ_ans₁_liftM {α : Type} (pub : CF St Blk) (chain : Blk × List Blk → St)
    (oa : ProbComp α) :
    simulateQ (ans₁ pub chain) (liftM oa : OracleComp (gS St Blk) α) = oa := by
  unfold ans₁ unifFwdAnswerImpl
  refine (QueryImpl.simulateQ_add_liftM_left _ _ oa).trans ?_
  simp

/-- A lifted sampling computation makes only uniform-sampling queries. -/
theorem allQueriesSatisfy_liftM_unif {ι α : Type} {spec : OracleSpec ι} (oa : ProbComp α)
    (Q : ℕ ⊕ ι → Prop) (hQ : ∀ n, Q (.inl n)) :
    AllQueriesSatisfy (liftM oa : OracleComp (unifSpec + spec) α) Q := by
  rw [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_def]
  have h : AllQueriesSatisfy oa (fun _ => True) := by
    induction oa using OracleComp.inductionOn with
    | pure x => exact allQueriesSatisfy_pure _ _
    | query_bind t k ih =>
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial, ih⟩
  refine h.simulateQ fun t _ => ?_
  have := (allQueriesSatisfy_query_bind_iff (spec := unifSpec + spec) (P := Q) (t := .inl t)
    (mx := fun x => pure x)).2 ⟨hQ t, fun _ => allQueriesSatisfy_pure _ _⟩
  change AllQueriesSatisfy
    (liftM ((unifSpec + spec).query (.inl t)) : OracleComp (unifSpec + spec) _) Q
  simpa using this

/-- A lifted sampling computation makes no query charged by a predicate that is false on
uniform-sampling queries. -/
theorem isQueryBoundP_liftM_unif {ι α : Type} {spec : OracleSpec ι} (oa : ProbComp α)
    (p : ℕ ⊕ ι → Prop) [DecidablePred p] (hp : ∀ n, ¬ p (.inl n)) :
    IsQueryBoundP (liftM oa : OracleComp (unifSpec + spec) α) p 0 :=
  (isQueryBoundP_congr_pred fun _ => not_not.symm).2
    ((isQueryBoundP_zero_iff _ _).2 (allQueriesSatisfy_liftM_unif oa (fun t => ¬ p t) hp))

theorem preGameM_run_inl [DecidableEq Tweak] [SampleableType M'] (emb : M' → M) (n : ℕ)
    (s : SM_DT_PRE_State Tweak M') :
    (preGameM F emb (.inl n)).run s =
      liftM ((gS St Blk).query (.inl n)) >>= fun x => pure (x, s) := by
  simp [preGameM]

theorem preGameM_run_h [DecidableEq Tweak] [SampleableType M'] (emb : M' → M) (q : St × Blk)
    (s : SM_DT_PRE_State Tweak M') :
    (preGameM F emb (.inr (.inl q))).run s =
      liftM ((gS St Blk).query (.inr (.inl q))) >>= fun x => pure (x, s) := by
  simp [preGameM]

theorem preGameM_run_chal [DecidableEq Tweak] [SampleableType M'] (emb : M' → M) (t : Tweak)
    (s : SM_DT_PRE_State Tweak M') :
    (preGameM F emb (.inr (.inr (.inl t)))).run s =
      if F.numTargets ≤ s.1.length ∨ ¬ TweakFresh Prod.fst s.1 s.2 t then pure (none, s)
      else (liftM ($ᵗ M' : ProbComp M') : OracleComp (gS St Blk) M') >>= fun x =>
        liftM ((gS St Blk).query (.inr (.inr (F.tch t (emb x))))) >>= fun c =>
        pure (some (F.out c), (s.1 ++ [(t, x)], s.2)) := by
  obtain ⟨qs, tw⟩ := s
  by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw t <;>
    simp [preGameM, h]

theorem preGameM_run_coll [DecidableEq Tweak] [SampleableType M'] (emb : M' → M)
    (q : (i : ι) × Tweak × F.Msg i) (s : SM_DT_PRE_State Tweak M') :
    (preGameM F emb (.inr (.inr (.inr q)))).run s =
      if TweakReserved (Q := Tweak × M') Prod.fst s.1 q.2.1 then pure (none, s)
      else liftM ((gS St Blk).query (.inr (.inr (F.cch q.1 q.2.1 q.2.2)))) >>= fun c =>
        pure (some (F.cout q.1 c), (s.1, s.2 ++ [q.2.1])) := by
  obtain ⟨qs, tw⟩ := s
  by_cases h : TweakReserved (Q := Tweak × M') Prod.fst qs q.2.1 <;>
    simp [preGameM, h]

/-- One step of VCVio's SM-PRE oracles after instantiating the compression oracle at `g` is one
step of the monadic game answered by `g` and the keyed chain. -/
theorem pre_step [DecidableEq Tweak] [SampleableType M'] (emb : M' → M)
    (hemb : Function.Injective emb) (g : CF St Blk) (seed : PkSeed) (t : F.padvS.Domain)
    (s : SM_DT_PRE_State Tweak M') :
    (simulateQ (SM_DT_PRE_oracles (F.preProb emb hemb g) seed) (instImpl g t)).run s =
      simulateQ (ans₁ g (keyedChain F.IV F.sb g seed)) ((preGameM F emb t).run s) := by
  rcases t with n | q | t | q
  · rw [preGameM_run_inl]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_PRE_oracles (F.preProb emb hemb g) seed) (.inl n))).trans ?_
    simp [SM_DT_PRE_oracles]
  · rw [preGameM_run_h]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_pure (SM_DT_PRE_oracles (F.preProb emb hemb g) seed) (g q))).trans ?_
    simp
  · rw [preGameM_run_chal]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_PRE_oracles (F.preProb emb hemb g) seed)
        (.inr (.inl t)))).trans ?_
    show (SM_DT_PRE_challengeOracle (F.preProb emb hemb g) seed t).run s = _
    obtain ⟨qs, tw⟩ := s
    by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw t
    · simp [SM_DT_PRE_challengeOracle, THFam.preProb, h]
    · simp [SM_DT_PRE_challengeOracle, THFam.preProb, THFam.evalT, h, simulateQ_ans₁_liftM,
        Functor.map_map]
  · rw [preGameM_run_coll]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_PRE_oracles (F.preProb emb hemb g) seed)
        (.inr (.inr q)))).trans ?_
    show (collectionOracle (Q := Tweak × M') Prod.fst (F.preProb emb hemb g).thColl seed q).run s
      = _
    obtain ⟨qs, tw⟩ := s
    by_cases h : TweakReserved (Q := Tweak × M') Prod.fst qs q.2.1 <;>
      simp [collectionOracle, THFam.preProb, THFam.coll, THFam.evalC, h]

theorem preAdvantage_eq_realGame [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    [SampleableType (CF St Blk)] (emb : M' → M) (hemb : Function.Injective emb)
    (A : PreAdv F M') :
    preAdvantage F emb hemb A =
      𝒟[realGame F.IV F.sb F.seedGen (preProg₁ emb A) (preP₂ emb A)] {true} := by
  unfold preAdvantage realGame
  congr 2
  refine bind_congr fun g => ?_
  simp only [SM_DT_PRE_Experiment, PreAdv.inst, preProg₁]
  refine bind_congr fun seed => ?_
  refine (congrArg (· >>= _) (simulateQ_run_simulateQ_eq_of_step (instImpl g) _ (preGameM F emb)
    (ans₁ g (keyedChain F.IV F.sb g seed)) (pre_step emb hemb g seed) A.choose ([], []))).trans ?_
  refine bind_congr fun x => ?_
  obtain ⟨st, qs, tw⟩ := x
  simp only [preP₂, simulateQ_bind]
  refine bind_congr fun jm => ?_
  obtain ⟨j, m⟩ := jm
  cases qs[j]? with
  | none => simp
  | some tm =>
    simp [simulateQ_instImpl₀_evalPub, THFam.preProb]
    congr

theorem preProg₁_pubBound [DecidableEq Tweak] [SampleableType M'] (emb : M' → M)
    (A : PreAdv F M') {q : ℕ} (h : A.ChooseBound q) :
    IsQueryBoundP (preProg₁ emb A) (fun i => isPub i = true) q := by
  refine IsQueryBoundP.simulateQ_run_of_step h (fun t ht s => ?_) (fun t ht s => ?_) _
  · rcases t with n | q | t | q
    · simp [THFam.pIsH] at ht
    · rw [preGameM_run_h]; simp [isPub]
    · simp [THFam.pIsH] at ht
    · simp [THFam.pIsH] at ht
  · rcases t with n | q | t | q
    · rw [preGameM_run_inl]; simp [isPub]
    · simp [THFam.pIsH] at ht
    · rw [preGameM_run_chal]
      split_ifs
      · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_bind_zero _ _ (isQueryBoundP_liftM_unif _ _ (by simp [isPub]))
          fun x => by simp [isPub]
    · rw [preGameM_run_coll]; split_ifs <;> first | exact isQueryBoundP_pure _ _ _ | simp [isPub]

theorem preProg₁_chainBound [DecidableEq Tweak] [SampleableType M'] (emb : M' → M)
    (A : PreAdv F M') {qch qc : ℕ} (h₁ : A.ChalBound qch) (h₂ : A.CollBound qc) :
    IsQueryBoundP (preProg₁ emb A) (fun i => isChain i = true) (qch + qc) := by
  refine IsQueryBoundP.simulateQ_run_of_step_or h₁ h₂ (fun t ht s => ?_) (fun t ht s => ?_) _
  · rcases t with n | q | t | q
    · simp [THFam.pIsChal, THFam.pIsColl] at ht
    · simp [THFam.pIsChal, THFam.pIsColl] at ht
    · rw [preGameM_run_chal]
      split_ifs
      · exact isQueryBoundP_pure _ _ _
      · have h0 : IsQueryBoundP (liftM ($ᵗ M' : ProbComp M') : OracleComp (gS St Blk) M')
            (fun i => isChain i = true) 0 :=
          isQueryBoundP_liftM_unif _ _ (by simp [isChain])
        have := isQueryBoundP_bind h0 (m := 1) (ob := fun x =>
          liftM ((gS St Blk).query (.inr (.inr (F.tch t (emb x))))) >>= fun c =>
            (pure (some (F.out c), (s.1 ++ [(t, x)], s.2)) :
              OracleComp (gS St Blk) (Option Y × SM_DT_PRE_State Tweak M')))
          fun x _ => by simp [isChain]
        simpa using this
    · rw [preGameM_run_coll]; split_ifs <;> first | exact isQueryBoundP_pure _ _ _ | simp [isChain]
  · rcases t with n | q | t | q
    · rw [preGameM_run_inl]; simp [isChain]
    · rw [preGameM_run_h]; simp [isChain]
    · simp [THFam.pIsChal, THFam.pIsColl] at ht
    · simp [THFam.pIsChal, THFam.pIsColl] at ht

theorem preProg₁_chainLen [DecidableEq Tweak] [SampleableType M'] (emb : M' → M)
    (A : PreAdv F M') {L : ℕ} (hT : ∀ t m, (F.tch t m).2.length ≤ L) (h : A.CollLen L) :
    AllQueriesSatisfy (preProg₁ emb A) (chainLenLe L) := by
  have key : ∀ {β : Type} (i : (gS St Blk).Domain) (f : (gS St Blk).Range i → β),
      chainLenLe L i → AllQueriesSatisfy
        (liftM ((gS St Blk).query i) >>= fun x => (pure (f x) : OracleComp (gS St Blk) β))
        (chainLenLe L) := by
    intro β i f hi
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨hi, fun _ => allQueriesSatisfy_pure _ _⟩
  refine AllQueriesSatisfy.simulateQ_run h (fun t ht s => ?_) _
  rcases t with n | q | t | q
  · rw [preGameM_run_inl]; exact key _ _ trivial
  · rw [preGameM_run_h]; exact key _ _ trivial
  · rw [preGameM_run_chal]
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_bind (allQueriesSatisfy_liftM_unif _ _ fun _ => trivial)
        fun x => key _ _ (hT _ _)
  · rw [preGameM_run_coll]
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact key _ _ ht

end Ideal

#print axioms Ideal.preAdvantage_eq_realGame
#print axioms Ideal.preProg₁_pubBound
#print axioms Ideal.preProg₁_chainBound
#print axioms Ideal.preProg₁_chainLen
