import Ideal.Games.DsprDefs
import Ideal.Games.TcrFVBridge

/-!
# Source-final-validity SM-DSPR in the ideal-compression model: the VCVio experiments as
two-phase programs

`dsprSuccessI_eq_realGame`, `dsprSPI_eq_realGame`: the two table-averaged probabilities (VCVio's
`experiment` and `spExperiment` at the hash built from a uniform table `g`, adversary
instantiated at `g`) are the probabilities that `Ideal.realGame` returns `true` on the phase
programs `dsprProg₁ A`, `dsprP₂ winS A` resp. `dsprP₂ winSP A`.  In particular the scan
`spPub` over all messages computes, at every fixed table, VCVio's `SecondPreimageExists`
(`simulateQ_instImpl₀_spPub`).  Query bounds of `dsprProg₁ A`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y : Type} {F : THFam St Blk PkSeed Tweak M Y Empty}

/-- One step of VCVio's DSPR oracles after instantiating the compression oracle at `g` is one
step of the monadic game answered by `g` and the keyed chain. -/
theorem dspr_step [DecidableEq Tweak] (g : CF St Blk) (seed : PkSeed) (t : F.fvAdvS.Domain)
    (s : SM_DT_DSPR_SourceFinalValidity.State Tweak M) :
    (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles (F.dsprProb g) seed) (instImpl g t)).run s =
      simulateQ (ans₁ g (keyedChain F.IV F.sb g seed)) ((fvGameM F t).run s) := by
  rcases t with n | q | tm | q
  · rw [fvGameM_run_inl]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_DSPR_SourceFinalValidity.oracles (F.dsprProb g) seed)
        (.inl n))).trans ?_
    simp [SM_DT_DSPR_SourceFinalValidity.oracles]
  · rw [fvGameM_run_h]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_pure (SM_DT_DSPR_SourceFinalValidity.oracles (F.dsprProb g) seed) (g q))).trans ?_
    simp
  · rw [fvGameM_run_chal]
    refine (congrArg (fun z => StateT.run z s)
      (simulateQ_spec_query (SM_DT_DSPR_SourceFinalValidity.oracles (F.dsprProb g) seed)
        (.inr (.inl tm)))).trans ?_
    show (SM_DT_DSPR_SourceFinalValidity.challengeOracle (F.dsprProb g) seed tm).run s = _
    obtain ⟨t, m⟩ := tm
    rw [SM_DT_DSPR_SourceFinalValidity.challengeOracle_run]
    simp [THFam.dsprProb, THFam.fvTh, THFam.evalT,
      SM_DT_DSPR_SourceFinalValidity.Problem.standalone]
  · exact q.1.elim

/-- At the table `g` the scan returns whether the list contains a second preimage. -/
theorem simulateQ_instImpl₀_spScan [DecidableEq M] [DecidableEq Y] (g : CF St Blk) (pk : PkSeed)
    (t : Tweak) (m : M) (y : Y) (l : List M) :
    simulateQ (instImpl₀ g) (spScan F pk t m y l) =
      pure (decide (∃ a ∈ l, m ≠ a ∧ y = F.evalT g pk t a)) := by
  induction l with
  | nil => simp [spScan]
  | cons a l ih =>
    simp only [spScan, simulateQ_bind, simulateQ_instImpl₀_evalPub, ih, pure_bind,
      simulateQ_pure]
    congr 1
    rw [Bool.eq_iff_iff]
    simp

/-- At the table `g`, `spPub` computes VCVio's `SecondPreimageExists`. -/
theorem simulateQ_instImpl₀_spPub [Fintype M] [DecidableEq M] [DecidableEq Y] (g : CF St Blk)
    (pk : PkSeed) (t : Tweak) (m : M) :
    simulateQ (instImpl₀ g) (spPub F pk t m) =
      pure (decide (SecondPreimageExists (F.fvTh g) pk t m)) := by
  simp only [spPub, simulateQ_bind, simulateQ_instImpl₀_evalPub, pure_bind,
    simulateQ_instImpl₀_spScan]
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  simp [SecondPreimageExists, THFam.fvTh]

/-- The VCVio experiment with winning condition `win` of the second-preimage bit and the guess
(`winS`: `experiment`; `winSP`: `spExperiment`), as `realGame`. -/
theorem dspr_eq_realGame_aux [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (win : Bool → Bool → Bool) (A : DsprAdv F) (g : CF St Blk) :
    (do
      let pk ← F.seedGen
      let (privateState, gameState) ←
        (simulateQ (SM_DT_DSPR_SourceFinalValidity.oracles (F.dsprProb g) pk)
          (A.inst g).choose).run .initial
      let (j, b) ← (A.inst g).guess privateState pk
      match gameState.challenges[j]? with
      | none => return false
      | some (t, m) =>
          return gameState.valid &&
            win (decide (SecondPreimageExists (F.dsprProb g).th pk t m)) b : ProbComp Bool) =
      (do
        let seed ← F.seedGen
        let x ← simulateQ (ans₁ g (keyedChain F.IV F.sb g seed)) (dsprProg₁ A)
        simulateQ (instImpl₀ g) (dsprP₂ win A seed x)) := by
  simp only [DsprAdv.inst, dsprProg₁]
  refine bind_congr fun seed => ?_
  refine (congrArg (· >>= _) (simulateQ_run_simulateQ_eq_of_step (instImpl g) _ (fvGameM F)
    (ans₁ g (keyedChain F.IV F.sb g seed)) (dspr_step g seed) A.choose .initial)).trans ?_
  refine bind_congr fun x => ?_
  obtain ⟨st, qs, tw, v⟩ := x
  simp only [dsprP₂, simulateQ_bind]
  refine bind_congr fun jb => ?_
  obtain ⟨j, b⟩ := jb
  cases qs[j]? with
  | none => simp
  | some tm =>
    cases v
    · simp
    · simp only [simulateQ_instImpl₀_spPub, THFam.dsprProb,
        SM_DT_DSPR_SourceFinalValidity.Problem.standalone, ite_true, simulateQ_bind,
        simulateQ_pure, pure_bind, Bool.true_and]
      congr!

theorem dsprSuccessI_eq_realGame [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (A : DsprAdv F) :
    dsprSuccessI F A =
      𝒟[realGame F.IV F.sb F.seedGen (dsprProg₁ A) (dsprP₂ winS A)] {true} := by
  unfold dsprSuccessI idealAdv realGame
  congr 2
  refine bind_congr fun g => ?_
  rw [← dspr_eq_realGame_aux winS A g]
  simp only [SM_DT_DSPR_SourceFinalValidity.experiment, winS]
  refine bind_congr fun pk => bind_congr fun x => bind_congr fun jb => ?_
  cases x.2.challenges[jb.1]? with
  | none => rfl
  | some tm => simp

theorem dsprSPI_eq_realGame [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (A : DsprAdv F) :
    dsprSPI F A =
      𝒟[realGame F.IV F.sb F.seedGen (dsprProg₁ A) (dsprP₂ winSP A)] {true} := by
  unfold dsprSPI idealAdv realGame
  congr 2
  refine bind_congr fun g => ?_
  rw [← dspr_eq_realGame_aux winSP A g]
  rfl

theorem dsprProg₁_pubBound [DecidableEq Tweak] (A : DsprAdv F) {q : ℕ} (h : A.ChooseBound q) :
    IsQueryBoundP (dsprProg₁ A) (fun i => isPub i = true) q := by
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

theorem dsprProg₁_chainBound [DecidableEq Tweak] (A : DsprAdv F) {qch : ℕ}
    (h : A.ChalBound qch) :
    IsQueryBoundP (dsprProg₁ A) (fun i => isChain i = true) qch := by
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

theorem dsprProg₁_chainLen [DecidableEq Tweak] (A : DsprAdv F) {L : ℕ}
    (hT : ∀ t m, (F.tch t m).2.length ≤ L) :
    AllQueriesSatisfy (dsprProg₁ A) (chainLenLe L) := by
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

#print axioms Ideal.simulateQ_instImpl₀_spPub
#print axioms Ideal.dsprSuccessI_eq_realGame
#print axioms Ideal.dsprSPI_eq_realGame
#print axioms Ideal.dsprProg₁_pubBound
#print axioms Ideal.dsprProg₁_chainBound
#print axioms Ideal.dsprProg₁_chainLen
