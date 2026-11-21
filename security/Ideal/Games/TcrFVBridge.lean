import Ideal.Games.TcrFVDefs
import Ideal.Games.TcrBridge

/-!
# Source-final-validity SM-TCR in the ideal-compression model: the VCVio experiment as a
two-phase program

`tcrFVAdvantage_eq_realGame`: the ideal-model advantage (VCVio's source-final-validity experiment
at the hash built from a uniform table `g`, adversary instantiated at `g`) is the probability
that `Ideal.realGame` returns `true` on the phase programs `fvProg₁ A`, `fvP₂ A`.
Query bounds of `fvProg₁ A` in terms of the adversary's own query bounds.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y : Type} {F : THFam St Blk PkSeed Tweak M Y Empty}

theorem fvGameM_run_inl [DecidableEq Tweak] (n : ℕ)
    (s : SM_DT_TCR_SourceFinalValidity.State Tweak M) :
    (fvGameM F (.inl n)).run s =
      liftM ((gS St Blk).query (.inl n)) >>= fun x => pure (x, s) := by
  simp [fvGameM]

theorem fvGameM_run_h [DecidableEq Tweak] (q : St × Blk)
    (s : SM_DT_TCR_SourceFinalValidity.State Tweak M) :
    (fvGameM F (.inr (.inl q))).run s =
      liftM ((gS St Blk).query (.inr (.inl q))) >>= fun x => pure (x, s) := by
  simp [fvGameM]

theorem fvGameM_run_chal [DecidableEq Tweak] (tm : Tweak × M)
    (s : SM_DT_TCR_SourceFinalValidity.State Tweak M) :
    (fvGameM F (.inr (.inr (.inl tm)))).run s =
      liftM ((gS St Blk).query (.inr (.inr (F.tch tm.1 tm.2)))) >>= fun c =>
        pure (F.out c, s.recordTarget F.numTargets Prod.fst tm) := by
  simp [fvGameM]

/-- One step of VCVio's source-final-validity oracles after instantiating the compression oracle
at `g` is one step of the monadic game answered by `g` and the keyed chain. -/
theorem fv_step [DecidableEq Tweak] (g : CF St Blk) (seed : PkSeed) (t : F.fvAdvS.Domain)
    (s : SM_DT_TCR_SourceFinalValidity.State Tweak M) :
    (simulateQ (SM_DT_TCR_SourceFinalValidity.oracles (F.fvProb g) seed) (instImpl g t)).run s =
      simulateQ (ans₁ g (keyedChain F.IV F.sb g seed)) ((fvGameM F t).run s) := by
  rcases t with n | q | tm | q
  · rw [fvGameM_run_inl]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_SourceFinalValidity.oracles (F.fvProb g) seed)
        (.inl n))).trans ?_
    simp [SM_DT_TCR_SourceFinalValidity.oracles]
  · rw [fvGameM_run_h]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_pure (SM_DT_TCR_SourceFinalValidity.oracles (F.fvProb g) seed) (g q))).trans ?_
    simp
  · rw [fvGameM_run_chal]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_TCR_SourceFinalValidity.oracles (F.fvProb g) seed)
        (.inr (.inl tm)))).trans ?_
    show (SM_DT_TCR_SourceFinalValidity.challengeOracle (F.fvProb g) seed tm).run s = _
    obtain ⟨t, m⟩ := tm
    rw [SM_DT_TCR_SourceFinalValidity.challengeOracle_run]
    simp [THFam.fvProb, THFam.fvTh, THFam.evalT, SM_DT_TCR_SourceFinalValidity.Problem.standalone]
  · exact q.1.elim

theorem tcrFVAdvantage_eq_realGame [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (A : FvAdv F) :
    tcrFVAdvantage F A = 𝒟[realGame F.IV F.sb F.seedGen (fvProg₁ A) (fvP₂ A)] {true} := by
  unfold tcrFVAdvantage realGame
  congr 2
  refine bind_congr fun g => ?_
  simp only [SM_DT_TCR_SourceFinalValidity.experiment, FvAdv.inst, fvProg₁]
  refine bind_congr fun seed => ?_
  refine (congrArg (· >>= _) (simulateQ_run_simulateQ_eq_of_step (instImpl g) _ (fvGameM F)
    (ans₁ g (keyedChain F.IV F.sb g seed)) (fv_step g seed) A.choose .initial)).trans ?_
  refine bind_congr fun x => ?_
  obtain ⟨st, qs, tw, v⟩ := x
  simp only [fvP₂, simulateQ_bind]
  refine bind_congr fun jm => ?_
  obtain ⟨j, m⟩ := jm
  cases qs[j]? with
  | none => simp
  | some tm =>
    cases v <;> by_cases hm : m = tm.2 <;>
      simp [simulateQ_instImpl₀_evalPub, THFam.fvProb, THFam.fvTh,
        SM_DT_TCR_SourceFinalValidity.Problem.standalone, hm]

theorem fvProg₁_pubBound [DecidableEq Tweak] (A : FvAdv F) {q : ℕ} (h : A.ChooseBound q) :
    IsQueryBoundP (fvProg₁ A) (fun i => isPub i = true) q := by
  refine IsQueryBoundP.simulateQ_run_of_step h (fun t ht s => ?_) (fun t ht s => ?_) _
  · rcases t with n | q | tm | q
    · simp [THFam.fvIsH] at ht
    · rw [fvGameM_run_h]; simp [isPub]
    · simp [THFam.fvIsH] at ht
    · exact q.1.elim
  · rcases t with n | q | tm | q
    · rw [fvGameM_run_inl]; simp [isPub]
    · simp [THFam.fvIsH] at ht
    · rw [fvGameM_run_chal]; simp [isPub]
    · exact q.1.elim

theorem fvProg₁_chainBound [DecidableEq Tweak] (A : FvAdv F) {qch : ℕ} (h : A.ChalBound qch) :
    IsQueryBoundP (fvProg₁ A) (fun i => isChain i = true) qch := by
  refine IsQueryBoundP.simulateQ_run_of_step h (fun t ht s => ?_) (fun t ht s => ?_) _
  · rcases t with n | q | tm | q
    · simp [THFam.fvIsChal] at ht
    · simp [THFam.fvIsChal] at ht
    · rw [fvGameM_run_chal]; simp [isChain]
    · exact q.1.elim
  · rcases t with n | q | tm | q
    · rw [fvGameM_run_inl]; simp [isChain]
    · rw [fvGameM_run_h]; simp [isChain]
    · simp [THFam.fvIsChal] at ht
    · exact q.1.elim

theorem fvProg₁_chainLen [DecidableEq Tweak] (A : FvAdv F) {L : ℕ}
    (hT : ∀ t m, (F.tch t m).2.length ≤ L) :
    AllQueriesSatisfy (fvProg₁ A) (chainLenLe L) := by
  have key : ∀ {β : Type} (i : (gS St Blk).Domain) (f : (gS St Blk).Range i → β),
      chainLenLe L i → AllQueriesSatisfy
        (liftM ((gS St Blk).query i) >>= fun x => (pure (f x) : OracleComp (gS St Blk) β))
        (chainLenLe L) := by
    intro β i f hi
    rw [allQueriesSatisfy_query_bind_iff]
    exact ⟨hi, fun _ => allQueriesSatisfy_pure _ _⟩
  have htriv : AllQueriesSatisfy A.choose (fun _ => True) := by
    induction A.choose using OracleComp.inductionOn with
    | pure x => exact allQueriesSatisfy_pure _ _
    | query_bind t k ih =>
      rw [allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial, ih⟩
  refine AllQueriesSatisfy.simulateQ_run htriv (fun t _ s => ?_) _
  rcases t with n | q | tm | q
  · rw [fvGameM_run_inl]; exact key _ _ trivial
  · rw [fvGameM_run_h]; exact key _ _ trivial
  · rw [fvGameM_run_chal]; exact key _ _ (hT _ _)
  · exact q.1.elim

end Ideal

#print axioms Ideal.tcrFVAdvantage_eq_realGame
#print axioms Ideal.fvProg₁_pubBound
#print axioms Ideal.fvProg₁_chainBound
#print axioms Ideal.fvProg₁_chainLen
