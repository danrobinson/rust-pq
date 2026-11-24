import Ideal.Games.UdBridge


namespace Reduction.Compression.WotsPhase
open Ideal TweakableHash OracleComp OracleSpec ENNReal
variable {St Blk PkSeed Tweak M M' Y ι : Type} {F : THFam St Blk PkSeed Tweak M Y ι}

/-- Interpret a family using the supplied chain first-phase oracle. -/
def chainCollection (F : THFam St Blk PkSeed Tweak M Y ι) (c : Blk × List Blk → St) :
    TweakableHashCollection ι PkSeed Tweak Y :=
  ⟨F.Msg,fun i _ t m => F.cout i (c (F.cch i t m))⟩

def chainTcr (F : THFam St Blk PkSeed Tweak M Y ι) (c : Blk × List Blk → St) :
    SM_DT_TCR_Problem ι PkSeed Tweak M Y :=
  ⟨⟨F.seedGen,fun _ t m => F.out (c (F.tch t m))⟩,chainCollection F c,F.numTargets⟩

def chainPre (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M) (he : Function.Injective emb)
    (c : Blk × List Blk → St) : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y :=
  ⟨⟨F.seedGen,fun _ t m => F.out (c (F.tch t m))⟩,emb,he,chainCollection F c,F.numTargets⟩

def chainUd [SampleableType M'] [SampleableType Y] (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M) (he : Function.Injective emb)
    (c : Blk × List Blk → St) : SM_DT_UD_Problem ι PkSeed Tweak M M' Y :=
  ⟨⟨F.seedGen,fun _ t m => F.out (c (F.tch t m))⟩,emb,he,$ᵗ M',$ᵗ Y,chainCollection F c,F.numTargets⟩

theorem pre_step [DecidableEq Tweak] [SampleableType M'] (emb : M' → M)
    (hemb : Function.Injective emb) (g : CF St Blk) (c : Blk × List Blk → St) (seed : PkSeed) (t : F.padvS.Domain)
    (s : SM_DT_PRE_State Tweak M') :
    (simulateQ (SM_DT_PRE_oracles (chainPre F emb hemb c) seed) (instImpl g t)).run s =
      simulateQ (ans₁ g c) ((preGameM F emb t).run s) := by
  rcases t with n | q | t | q
  · rw [preGameM_run_inl]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_PRE_oracles (chainPre F emb hemb c) seed) (.inl n))).trans ?_
    simp [SM_DT_PRE_oracles]
  · rw [preGameM_run_h]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_pure (SM_DT_PRE_oracles (chainPre F emb hemb c) seed) (g q))).trans ?_
    simp
  · rw [preGameM_run_chal]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_PRE_oracles (chainPre F emb hemb c) seed)
        (.inr (.inl t)))).trans ?_
    show (SM_DT_PRE_challengeOracle (chainPre F emb hemb c) seed t).run s = _
    obtain ⟨qs, tw⟩ := s
    by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw t
    · simp [SM_DT_PRE_challengeOracle, chainPre, h]
    · simp [SM_DT_PRE_challengeOracle, chainPre, h, simulateQ_ans₁_liftM,
        Functor.map_map]
  · rw [preGameM_run_coll]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_PRE_oracles (chainPre F emb hemb c) seed)
        (.inr (.inr q)))).trans ?_
    show (collectionOracle (Q := Tweak × M') Prod.fst (chainPre F emb hemb c).thColl seed q).run s
      = _
    obtain ⟨qs, tw⟩ := s
    by_cases h : TweakReserved (Q := Tweak × M') Prod.fst qs q.2.1 <;>
      simp [collectionOracle, chainPre, chainCollection, h]

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

theorem tcr_step [DecidableEq Tweak] (g : CF St Blk) (c : Blk × List Blk → St) (seed : PkSeed) (t : F.advS.Domain)
    (s : SM_DT_TCR_State Tweak M) :
    (simulateQ (SM_DT_TCR_oracles (chainTcr F c) seed) (instImpl g t)).run s =
      simulateQ (ans₁ g c) ((tcrGameM F t).run s) := by
  rcases t with n | q | tm | q
  · rw [tcrGameM_run_inl]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (chainTcr F c) seed) (.inl n))).trans ?_
    simp [SM_DT_TCR_oracles]
  · rw [tcrGameM_run_h]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_pure (SM_DT_TCR_oracles (chainTcr F c) seed) (g q))).trans ?_
    simp
  · rw [tcrGameM_run_chal]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (chainTcr F c) seed) (.inr (.inl tm)))).trans ?_
    show (SM_DT_TCR_challengeOracle (chainTcr F c) seed tm).run s = _
    obtain ⟨qs, tw⟩ := s
    by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh Prod.fst qs tw tm.1 <;>
      simp [SM_DT_TCR_challengeOracle, chainTcr, h]
  · rw [tcrGameM_run_coll]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_oracles (chainTcr F c) seed) (.inr (.inr q)))).trans ?_
    show (collectionOracle (Q := Tweak × M) Prod.fst (chainTcr F c).thColl seed q).run s = _
    obtain ⟨qs, tw⟩ := s
    by_cases h : TweakReserved (Q := Tweak × M) Prod.fst qs q.2.1 <;>
      simp [collectionOracle, chainTcr, chainCollection, h]

theorem ud_step [DecidableEq Tweak] [SampleableType M'] [SampleableType Y] (world : SM_DT_UD_World) (emb : M' → M) (hemb : Function.Injective emb)
    (g : CF St Blk) (c : Blk × List Blk → St) (seed : PkSeed) (t : F.padvS.Domain) (s : SM_DT_UD_State Tweak) :
    (simulateQ (SM_DT_UD_oracles world (chainUd F emb hemb c) seed) (instImpl g t)).run s =
      simulateQ (ans₁ g c) ((udGameM F world emb t).run s) := by
  rcases t with n | q | t | q
  · rw [udGameM_run_inl]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_UD_oracles world (chainUd F emb hemb c) seed) (.inl n))).trans ?_
    simp [SM_DT_UD_oracles]
  · rw [udGameM_run_h]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_pure (SM_DT_UD_oracles world (chainUd F emb hemb c) seed) (g q))).trans ?_
    simp
  · refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_UD_oracles world (chainUd F emb hemb c) seed)
        (.inr (.inl t)))).trans ?_
    show (SM_DT_UD_challengeOracle world (chainUd F emb hemb c) seed t).run s = _
    obtain ⟨qs, tw⟩ := s
    cases world
    · rw [udGameM_run_chal_real]
      by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh id qs tw t
      · simp [SM_DT_UD_challengeOracle, chainUd, h]
      · simp [SM_DT_UD_challengeOracle, SM_DT_UD_response, chainUd, h,
          simulateQ_ans₁_liftM, Functor.map_map]
    · rw [udGameM_run_chal_ideal]
      by_cases h : F.numTargets ≤ qs.length ∨ ¬ TweakFresh id qs tw t
      · simp [SM_DT_UD_challengeOracle, chainUd, h]
      · simp [SM_DT_UD_challengeOracle, SM_DT_UD_response, chainUd, h,
          simulateQ_ans₁_liftM, Functor.map_map]
  · rw [udGameM_run_coll]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_UD_oracles world (chainUd F emb hemb c) seed)
        (.inr (.inr q)))).trans ?_
    show (collectionOracle (Q := Tweak) id (chainUd F emb hemb c).thColl seed q).run s = _
    obtain ⟨qs, tw⟩ := s
    by_cases h : TweakReserved (Q := Tweak) id qs q.2.1 <;>
      simp [collectionOracle, chainUd, chainCollection, h]

theorem pre_run [DecidableEq Tweak] [SampleableType M'] (emb : M' → M) (he : Function.Injective emb)
    (A : PreAdv F M') (g : CF St Blk) (c : Blk × List Blk → St) (pk : PkSeed) :
    (simulateQ (SM_DT_PRE_oracles (chainPre F emb he c) pk) (simulateQ (instImpl g) A.choose)).run ([],[]) =
      simulateQ (ans₁ g c) (preProg₁ emb A) :=
  simulateQ_run_simulateQ_eq_of_step (instImpl g) _ (preGameM F emb) (ans₁ g c)
    (pre_step emb he g c pk) A.choose ([],[])

theorem tcr_run [DecidableEq Tweak] (A : TcrAdv F) (g : CF St Blk) (c : Blk × List Blk → St) (pk : PkSeed) :
    (simulateQ (SM_DT_TCR_oracles (chainTcr F c) pk) (simulateQ (instImpl g) A.choose)).run ([],[]) =
      simulateQ (ans₁ g c) (tcrProg₁ A) :=
  simulateQ_run_simulateQ_eq_of_step (instImpl g) _ (tcrGameM F) (ans₁ g c)
    (tcr_step g c pk) A.choose ([],[])

theorem ud_run [DecidableEq Tweak] [SampleableType M'] [SampleableType Y] (world : SM_DT_UD_World)
    (emb : M' → M) (he : Function.Injective emb) (A : UdAdv F) (g : CF St Blk) (c : Blk × List Blk → St) (pk : PkSeed) :
    (simulateQ (SM_DT_UD_oracles world (chainUd F emb he c) pk) (simulateQ (instImpl g) A.pick)).run ([],[]) =
      simulateQ (ans₁ g c) (udProg₁ world emb A) :=
  simulateQ_run_simulateQ_eq_of_step (instImpl g) _ (udGameM F world emb) (ans₁ g c)
    (ud_step world emb he g c pk) A.pick ([],[])

end Reduction.Compression.WotsPhase
#print axioms Reduction.Compression.WotsPhase.pre_run
#print axioms Reduction.Compression.WotsPhase.tcr_run
#print axioms Reduction.Compression.WotsPhase.ud_run
