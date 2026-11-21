import Ideal.Games.TcrDefs
import Ideal.Core.SimLemmas

/-!
# SM-TCR in the ideal-compression model: the VCVio experiment as a two-phase program

`tcrAdvantage_eq_realGame`: the ideal-model SM-TCR advantage (VCVio's experiment at the hash
built from a uniform table `g`, adversary instantiated at `g`) is the probability that
`Ideal.realGame` returns `true` on the phase programs `tcrProg₁ A`, `tcrP₂ A`.
Query bounds of `tcrProg₁ A` in terms of the adversary's own query bounds.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y ι : Type} {F : THFam St Blk PkSeed Tweak M Y ι}

/-- `evalPub` at the table `g` computes the attacked member. -/
theorem simulateQ_instImpl₀_evalPub (g : CF St Blk) (pk : PkSeed) (t : Tweak) (m : M) :
    simulateQ (instImpl₀ g) (evalPub F pk t m) = pure (F.evalT g pk t m) := by
  have h := simulateQ_instImpl₀_keyedChain g F.IV F.sb pk (F.tch t m)
  simp only [simulateQ_bind] at h
  simp only [evalPub, simulateQ_bind, simulateQ_pure, THFam.evalT]
  simp only [← bind_assoc] at h ⊢
  rw [h, pure_bind]

private theorem tcrGameM_run_inl [DecidableEq Tweak] (n : ℕ) (s : SM_DT_TCR_State Tweak M) :
    (tcrGameM F (.inl n)).run s =
      liftM ((gS St Blk).query (.inl n)) >>= fun x => pure (x, s) := by
  simp [tcrGameM]

private theorem tcrGameM_run_h [DecidableEq Tweak] (q : St × Blk) (s : SM_DT_TCR_State Tweak M) :
    (tcrGameM F (.inr (.inl q))).run s =
      liftM ((gS St Blk).query (.inr (.inl q))) >>= fun x => pure (x, s) := by
  simp [tcrGameM]

private theorem tcrGameM_run_chal [DecidableEq Tweak] (tm : Tweak × M)
    (s : SM_DT_TCR_State Tweak M) :
    (tcrGameM F (.inr (.inr (.inl tm)))).run s =
      if F.numTargets ≤ s.1.length ∨ ¬ TweakFresh Prod.fst s.1 s.2 tm.1 then pure (none, s)
      else liftM ((gS St Blk).query (.inr (.inr (F.tch tm.1 tm.2)))) >>= fun c =>
        pure (some (F.out c), (s.1 ++ [tm], s.2)) := by
  obtain ⟨qs, tw⟩ := s
  by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1 <;>
    simp [tcrGameM, h]

private theorem tcrGameM_run_coll [DecidableEq Tweak] (q : (i : ι) × Tweak × F.Msg i)
    (s : SM_DT_TCR_State Tweak M) :
    (tcrGameM F (.inr (.inr (.inr q)))).run s =
      if TweakReserved (Q := Tweak × M) Prod.fst s.1 q.2.1 then pure (none, s)
      else liftM ((gS St Blk).query (.inr (.inr (F.cch q.1 q.2.1 q.2.2)))) >>= fun c =>
        pure (some (F.cout q.1 c), (s.1, s.2 ++ [q.2.1])) := by
  obtain ⟨qs, tw⟩ := s
  by_cases h : TweakReserved (Q := Tweak × M) Prod.fst qs q.2.1 <;>
    simp [tcrGameM, h]

/-- One step of VCVio's SM-TCR oracles after instantiating the compression oracle at `g` is one
step of the monadic game answered by `g` and the keyed chain. -/
theorem tcr_step [DecidableEq Tweak] (g : CF St Blk) (seed : PkSeed) (t : F.advS.Domain)
    (s : SM_DT_TCR_State Tweak M) :
    (simulateQ (SM_DT_TCR_oracles (F.tcrProb g) seed) (instImpl g t)).run s =
      simulateQ (ans₁ g (keyedChain F.IV F.sb g seed)) ((tcrGameM F t).run s) := by
  rcases t with n | q | tm | q
  · rw [tcrGameM_run_inl]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (F.tcrProb g) seed) (.inl n))).trans ?_
    simp [SM_DT_TCR_oracles]
  · rw [tcrGameM_run_h]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_pure (SM_DT_TCR_oracles (F.tcrProb g) seed) (g q))).trans ?_
    simp
  · rw [tcrGameM_run_chal]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (F.tcrProb g) seed) (.inr (.inl tm)))).trans ?_
    show (SM_DT_TCR_challengeOracle (F.tcrProb g) seed tm).run s = _
    obtain ⟨qs, tw⟩ := s
    by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1 <;>
      simp [SM_DT_TCR_challengeOracle, THFam.tcrProb, THFam.evalT, h]
  · rw [tcrGameM_run_coll]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (F.tcrProb g) seed) (.inr (.inr q)))).trans ?_
    show (collectionOracle (Q := Tweak × M) Prod.fst (F.tcrProb g).thColl seed q).run s = _
    obtain ⟨qs, tw⟩ := s
    by_cases h : TweakReserved (Q := Tweak × M) Prod.fst qs q.2.1 <;>
      simp [collectionOracle, THFam.tcrProb, THFam.coll, THFam.evalC, h]

theorem tcrAdvantage_eq_realGame [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (A : TcrAdv F) :
    tcrAdvantage F A = 𝒟[realGame F.IV F.sb F.seedGen (tcrProg₁ A) (tcrP₂ A)] {true} := by
  unfold tcrAdvantage realGame
  congr 2
  refine bind_congr fun g => ?_
  simp only [SM_DT_TCR_Experiment, TcrAdv.inst, tcrProg₁]
  refine bind_congr fun seed => ?_
  refine (congrArg (· >>= _) (simulateQ_run_simulateQ_eq_of_step (instImpl g) _ (tcrGameM F)
    (ans₁ g (keyedChain F.IV F.sb g seed)) (tcr_step g seed) A.choose ([], []))).trans ?_
  refine bind_congr fun x => ?_
  obtain ⟨st, qs, tw⟩ := x
  simp only [tcrP₂, simulateQ_bind]
  refine bind_congr fun jm => ?_
  obtain ⟨j, m⟩ := jm
  cases qs[j]? with
  | none => simp
  | some tm =>
    by_cases hm : m = tm.2 <;> simp [simulateQ_instImpl₀_evalPub, THFam.tcrProb, hm]

theorem tcrProg₁_pubBound [DecidableEq Tweak] (A : TcrAdv F) {q : ℕ} (h : A.ChooseBound q) :
    IsQueryBoundP (tcrProg₁ A) (fun i => isPub i = true) q := by
  refine IsQueryBoundP.simulateQ_run_of_step h (fun t ht s => ?_) (fun t ht s => ?_) _
  · rcases t with n | q | tm | q
    · simp [THFam.isH] at ht
    · rw [tcrGameM_run_h]; simp [isPub]
    · simp [THFam.isH] at ht
    · simp [THFam.isH] at ht
  · rcases t with n | q | tm | q
    · rw [tcrGameM_run_inl]; simp [isPub]
    · simp [THFam.isH] at ht
    · rw [tcrGameM_run_chal]; split_ifs <;> first | exact isQueryBoundP_pure _ _ _ | simp [isPub]
    · rw [tcrGameM_run_coll]; split_ifs <;> first | exact isQueryBoundP_pure _ _ _ | simp [isPub]

theorem tcrProg₁_chainBound [DecidableEq Tweak] (A : TcrAdv F) {qch qc : ℕ}
    (h₁ : A.ChalBound qch) (h₂ : A.CollBound qc) :
    IsQueryBoundP (tcrProg₁ A) (fun i => isChain i = true) (qch + qc) := by
  refine IsQueryBoundP.simulateQ_run_of_step_or h₁ h₂ (fun t ht s => ?_) (fun t ht s => ?_) _
  · rcases t with n | q | tm | q
    · simp [THFam.isChal, THFam.isColl] at ht
    · simp [THFam.isChal, THFam.isColl] at ht
    · rw [tcrGameM_run_chal]; split_ifs <;> first | exact isQueryBoundP_pure _ _ _ | simp [isChain]
    · rw [tcrGameM_run_coll]; split_ifs <;> first | exact isQueryBoundP_pure _ _ _ | simp [isChain]
  · rcases t with n | q | tm | q
    · rw [tcrGameM_run_inl]; simp [isChain]
    · rw [tcrGameM_run_h]; simp [isChain]
    · simp [THFam.isChal, THFam.isColl] at ht
    · simp [THFam.isChal, THFam.isColl] at ht

theorem tcrProg₁_chainLen [DecidableEq Tweak] (A : TcrAdv F) {L : ℕ}
    (hT : ∀ t m, (F.tch t m).2.length ≤ L) (h : A.CollLen L) :
    AllQueriesSatisfy (tcrProg₁ A) (chainLenLe L) := by
  have key : ∀ {β : Type} (i : (gS St Blk).Domain) (f : (gS St Blk).Range i → β),
      chainLenLe L i → AllQueriesSatisfy
        (liftM ((gS St Blk).query i) >>= fun x => (pure (f x) : OracleComp (gS St Blk) β))
        (chainLenLe L) := by
    intro β i f hi
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨hi, fun _ => allQueriesSatisfy_pure _ _⟩
  refine AllQueriesSatisfy.simulateQ_run h (fun t ht s => ?_) _
  rcases t with n | q | tm | q
  · rw [tcrGameM_run_inl]; exact key _ _ trivial
  · rw [tcrGameM_run_h]; exact key _ _ trivial
  · rw [tcrGameM_run_chal]
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact key _ _ (hT _ _)
  · rw [tcrGameM_run_coll]
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact key _ _ ht

end Ideal

#print axioms Ideal.tcrAdvantage_eq_realGame
#print axioms Ideal.tcrProg₁_pubBound
#print axioms Ideal.tcrProg₁_chainBound
#print axioms Ideal.tcrProg₁_chainLen
