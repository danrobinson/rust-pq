import Ideal.Games.UdDefs
import Ideal.Games.PreBridge

/-!
# SM-UD in the ideal-compression model: the VCVio experiments as two-phase programs

`udRealI_eq_realGame`, `udIdealI_eq_realGame`: the table-averaged success probabilities of
VCVio's real-world / ideal-world SM-UD experiment (hash built from a uniform table `g`,
adversary instantiated at `g`) are the probabilities that `Ideal.realGame` returns `true` on the
phase programs `udProg₁ world emb A`, `udP₂ A` (in both worlds the collection oracle hashes, so
both are "real games" of `Core/Defs`).  Query bounds of `udProg₁ world emb A` in terms of the
adversary's own query bounds.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M M' Y ι : Type} {F : THFam St Blk PkSeed Tweak M Y ι}

section Run

variable [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]

theorem udGameM_run_inl (world : SM_DT_UD_World) (emb : M' → M) (n : ℕ)
    (s : SM_DT_UD_State Tweak) :
    (udGameM F world emb (.inl n)).run s =
      liftM ((gS St Blk).query (.inl n)) >>= fun x => pure (x, s) := by
  simp [udGameM]

theorem udGameM_run_h (world : SM_DT_UD_World) (emb : M' → M) (q : St × Blk)
    (s : SM_DT_UD_State Tweak) :
    (udGameM F world emb (.inr (.inl q))).run s =
      liftM ((gS St Blk).query (.inr (.inl q))) >>= fun x => pure (x, s) := by
  simp [udGameM]

theorem udGameM_run_chal_real (emb : M' → M) (t : Tweak) (s : SM_DT_UD_State Tweak) :
    (udGameM F .real emb (.inr (.inr (.inl t)))).run s =
      if F.numTargets ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 t then pure (none, s)
      else (liftM ($ᵗ M' : ProbComp M') : OracleComp (gS St Blk) M') >>= fun x =>
        liftM ((gS St Blk).query (.inr (.inr (F.tch t (emb x))))) >>= fun c =>
        pure (some (F.out c), (s.1 ++ [t], s.2)) := by
  obtain ⟨qs, tw⟩ := s
  by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh id qs tw t <;>
    simp [udGameM, h]

theorem udGameM_run_chal_ideal (emb : M' → M) (t : Tweak) (s : SM_DT_UD_State Tweak) :
    (udGameM F .ideal emb (.inr (.inr (.inl t)))).run s =
      if F.numTargets ≤ s.1.length ∨ ¬ TweakFresh id s.1 s.2 t then pure (none, s)
      else (liftM ($ᵗ Y : ProbComp Y) : OracleComp (gS St Blk) Y) >>= fun y =>
        pure (some y, (s.1 ++ [t], s.2)) := by
  obtain ⟨qs, tw⟩ := s
  by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh id qs tw t <;>
    simp [udGameM, h]

theorem udGameM_run_coll (world : SM_DT_UD_World) (emb : M' → M)
    (q : (i : ι) × Tweak × F.Msg i) (s : SM_DT_UD_State Tweak) :
    (udGameM F world emb (.inr (.inr (.inr q)))).run s =
      if TweakReserved (Q := Tweak) id s.1 q.2.1 then pure (none, s)
      else liftM ((gS St Blk).query (.inr (.inr (F.cch q.1 q.2.1 q.2.2)))) >>= fun c =>
        pure (some (F.cout q.1 c), (s.1, s.2 ++ [q.2.1])) := by
  obtain ⟨qs, tw⟩ := s
  by_cases h : TweakReserved (Q := Tweak) id qs q.2.1 <;>
    simp [udGameM, h]

/-- One step of VCVio's SM-UD oracles after instantiating the compression oracle at `g` is one
step of the monadic game answered by `g` and the keyed chain. -/
theorem ud_step (world : SM_DT_UD_World) (emb : M' → M) (hemb : Function.Injective emb)
    (g : CF St Blk) (seed : PkSeed) (t : F.padvS.Domain) (s : SM_DT_UD_State Tweak) :
    (simulateQ (SM_DT_UD_oracles world (F.udProb emb hemb g) seed) (instImpl g t)).run s =
      simulateQ (ans₁ g (keyedChain F.IV F.sb g seed)) ((udGameM F world emb t).run s) := by
  rcases t with n | q | t | q
  · rw [udGameM_run_inl]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_UD_oracles world (F.udProb emb hemb g) seed) (.inl n))).trans ?_
    simp [SM_DT_UD_oracles]
  · rw [udGameM_run_h]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_pure (SM_DT_UD_oracles world (F.udProb emb hemb g) seed) (g q))).trans ?_
    simp
  · refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_UD_oracles world (F.udProb emb hemb g) seed)
        (.inr (.inl t)))).trans ?_
    show (SM_DT_UD_challengeOracle world (F.udProb emb hemb g) seed t).run s = _
    obtain ⟨qs, tw⟩ := s
    cases world
    · rw [udGameM_run_chal_real]
      by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh id qs tw t
      · simp [SM_DT_UD_challengeOracle, THFam.udProb, h]
      · simp [SM_DT_UD_challengeOracle, SM_DT_UD_response, THFam.udProb, THFam.evalT, h,
          simulateQ_ans₁_liftM, Functor.map_map]
    · rw [udGameM_run_chal_ideal]
      by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh id qs tw t
      · simp [SM_DT_UD_challengeOracle, THFam.udProb, h]
      · simp [SM_DT_UD_challengeOracle, SM_DT_UD_response, THFam.udProb, h,
          simulateQ_ans₁_liftM, Functor.map_map]
  · rw [udGameM_run_coll]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_UD_oracles world (F.udProb emb hemb g) seed)
        (.inr (.inr q)))).trans ?_
    show (collectionOracle (Q := Tweak) id (F.udProb emb hemb g).thColl seed q).run s = _
    obtain ⟨qs, tw⟩ := s
    by_cases h : TweakReserved (Q := Tweak) id qs q.2.1 <;>
      simp [collectionOracle, THFam.udProb, THFam.coll, THFam.evalC, h]

/-- VCVio's SM-UD experiment at the table `g` is the eager two-phase game at `g`. -/
theorem ud_experiment_eq (world : SM_DT_UD_World) (emb : M' → M)
    (hemb : Function.Injective emb) (A : UdAdv F) (g : CF St Blk) :
    SM_DT_UD_Experiment world (A.inst emb hemb g) =
      (F.seedGen >>= fun seed =>
        simulateQ (ans₁ g (keyedChain F.IV F.sb g seed)) (udProg₁ world emb A) >>= fun x =>
          simulateQ (instImpl₀ g) (udP₂ A seed x)) := by
  simp only [SM_DT_UD_Experiment, UdAdv.inst, udProg₁]
  refine bind_congr fun seed => ?_
  refine (congrArg (· >>= _) (simulateQ_run_simulateQ_eq_of_step (instImpl g) _
    (udGameM F world emb) (ans₁ g (keyedChain F.IV F.sb g seed)) (ud_step world emb hemb g seed)
    A.pick ([], []))).trans ?_
  rfl

theorem udRealI_eq_realGame [SampleableType (CF St Blk)] (emb : M' → M)
    (hemb : Function.Injective emb) (A : UdAdv F) :
    udRealI F emb hemb A =
      𝒟[realGame F.IV F.sb F.seedGen (udProg₁ .real emb A) (udP₂ A)] {true} := by
  unfold udRealI realGame
  congr 2
  exact bind_congr fun g => ud_experiment_eq .real emb hemb A g

theorem udIdealI_eq_realGame [SampleableType (CF St Blk)] (emb : M' → M)
    (hemb : Function.Injective emb) (A : UdAdv F) :
    udIdealI F emb hemb A =
      𝒟[realGame F.IV F.sb F.seedGen (udProg₁ .ideal emb A) (udP₂ A)] {true} := by
  unfold udIdealI realGame
  congr 2
  exact bind_congr fun g => ud_experiment_eq .ideal emb hemb A g

/-! ## Query bounds -/

theorem udProg₁_pubBound (world : SM_DT_UD_World) (emb : M' → M) (A : UdAdv F) {q : ℕ}
    (h : A.PickBound q) :
    IsQueryBoundP (udProg₁ world emb A) (fun i => isPub i = true) q := by
  refine IsQueryBoundP.simulateQ_run_of_step h (fun t ht s => ?_) (fun t ht s => ?_) _
  · rcases t with n | q | t | q
    · simp [THFam.pIsH] at ht
    · rw [udGameM_run_h]; simp [isPub]
    · simp [THFam.pIsH] at ht
    · simp [THFam.pIsH] at ht
  · rcases t with n | q | t | q
    · rw [udGameM_run_inl]; simp [isPub]
    · simp [THFam.pIsH] at ht
    · cases world
      · rw [udGameM_run_chal_real]
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact isQueryBoundP_bind_zero _ _ (isQueryBoundP_liftM_unif _ _ (by simp [isPub]))
            fun x => by simp [isPub]
      · rw [udGameM_run_chal_ideal]
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact isQueryBoundP_bind_zero _ _ (isQueryBoundP_liftM_unif _ _ (by simp [isPub]))
            fun x => isQueryBoundP_pure _ _ _
    · rw [udGameM_run_coll]; split_ifs <;> first | exact isQueryBoundP_pure _ _ _ | simp [isPub]

theorem udProg₁_chainBound (world : SM_DT_UD_World) (emb : M' → M) (A : UdAdv F) {qch qc : ℕ}
    (h₁ : A.ChalBound qch) (h₂ : A.CollBound qc) :
    IsQueryBoundP (udProg₁ world emb A) (fun i => isChain i = true) (qch + qc) := by
  refine IsQueryBoundP.simulateQ_run_of_step_or h₁ h₂ (fun t ht s => ?_) (fun t ht s => ?_) _
  · rcases t with n | q | t | q
    · simp [THFam.pIsChal, THFam.pIsColl] at ht
    · simp [THFam.pIsChal, THFam.pIsColl] at ht
    · cases world
      · rw [udGameM_run_chal_real]
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · have h0 : IsQueryBoundP (liftM ($ᵗ M' : ProbComp M') : OracleComp (gS St Blk) M')
              (fun i => isChain i = true) 0 :=
            isQueryBoundP_liftM_unif _ _ (by simp [isChain])
          have := isQueryBoundP_bind h0 (m := 1) (ob := fun x =>
            liftM ((gS St Blk).query (.inr (.inr (F.tch t (emb x))))) >>= fun c =>
              (pure (some (F.out c), (s.1 ++ [t], s.2)) :
                OracleComp (gS St Blk) (Option Y × SM_DT_UD_State Tweak)))
            fun x _ => by simp [isChain]
          simpa using this
      · rw [udGameM_run_chal_ideal]
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · have h0 : IsQueryBoundP (liftM ($ᵗ Y : ProbComp Y) : OracleComp (gS St Blk) Y)
              (fun i => isChain i = true) 0 :=
            isQueryBoundP_liftM_unif _ _ (by simp [isChain])
          have := isQueryBoundP_bind h0 (m := 1) (ob := fun y =>
              (pure (some y, (s.1 ++ [t], s.2)) :
                OracleComp (gS St Blk) (Option Y × SM_DT_UD_State Tweak)))
            fun x _ => isQueryBoundP_pure _ _ _
          simpa using this
    · rw [udGameM_run_coll]; split_ifs <;> first | exact isQueryBoundP_pure _ _ _ | simp [isChain]
  · rcases t with n | q | t | q
    · rw [udGameM_run_inl]; simp [isChain]
    · rw [udGameM_run_h]; simp [isChain]
    · simp [THFam.pIsChal, THFam.pIsColl] at ht
    · simp [THFam.pIsChal, THFam.pIsColl] at ht

theorem udProg₁_chainLen (world : SM_DT_UD_World) (emb : M' → M) (A : UdAdv F) {L : ℕ}
    (hT : ∀ t m, (F.tch t m).2.length ≤ L) (h : A.CollLen L) :
    AllQueriesSatisfy (udProg₁ world emb A) (chainLenLe L) := by
  have key : ∀ {β : Type} (i : (gS St Blk).Domain) (f : (gS St Blk).Range i → β),
      chainLenLe L i → AllQueriesSatisfy
        (liftM ((gS St Blk).query i) >>= fun x => (pure (f x) : OracleComp (gS St Blk) β))
        (chainLenLe L) := by
    intro β i f hi
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨hi, fun _ => allQueriesSatisfy_pure _ _⟩
  refine AllQueriesSatisfy.simulateQ_run h (fun t ht s => ?_) _
  rcases t with n | q | t | q
  · rw [udGameM_run_inl]; exact key _ _ trivial
  · rw [udGameM_run_h]; exact key _ _ trivial
  · cases world
    · rw [udGameM_run_chal_real]
      split_ifs
      · exact allQueriesSatisfy_pure _ _
      · exact allQueriesSatisfy_bind (allQueriesSatisfy_liftM_unif _ _ fun _ => trivial)
          fun x => key _ _ (hT _ _)
    · rw [udGameM_run_chal_ideal]
      split_ifs
      · exact allQueriesSatisfy_pure _ _
      · exact allQueriesSatisfy_bind (allQueriesSatisfy_liftM_unif _ _ fun _ => trivial)
          fun x => allQueriesSatisfy_pure _ _
  · rw [udGameM_run_coll]
    split_ifs
    · exact allQueriesSatisfy_pure _ _
    · exact key _ _ ht

end Run

end Ideal

#print axioms Ideal.udRealI_eq_realGame
#print axioms Ideal.udIdealI_eq_realGame
#print axioms Ideal.udProg₁_pubBound
#print axioms Ideal.udProg₁_chainBound
#print axioms Ideal.udProg₁_chainLen
