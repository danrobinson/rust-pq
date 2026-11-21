import Reduction.SufHarness
import Reduction.PRFMsgHop

/-!
# The `PRF_msg` hop for an arbitrary final check

`bPrfMsgW w A` is `bPrfMsg A` with the harness `runForgerSig` and the final check `w`.
Real world = `expW tableAlg w A`; ideal world = `g2W w A`: game `G2` (secrets from a uniform
table, lazily sampled randomizer) whose final check is `w` on the public key, the forger's output
and the returned pairs `(M, idealSign tbl M pk R)` read off the `G2` transcript.

The auxiliary lemmas are those of `Reduction.PRFMsgHop` (private there), restated.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- The returned `(message, signature)` pairs of a `G2` transcript: the oracle answered the query
`M` with `idealSign tbl M pk R` and recorded `(M, opt_rand, R)`. -/
def sigLogOf (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core) (log : G2Log prims) :
    SigLog vp prims :=
  log.map fun e => ⟨e.1, idealSign vp prims tbl e.1 pk e.2.2⟩

/-- Game `G2` with final check `w`. -/
noncomputable def g2W (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    ProbComp Bool :=
  pkSeedDist >>= fun pkSeed => sampleTable vp prims >>= fun tbl =>
    g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z =>
      pure (w (idealPk vp prims tbl pkSeed) z.1 (sigLogOf tbl (idealPk vp prims tbl pkSeed) z.2))

/-- The `PRF_msg` distinguisher built from a forger and a final check `w`: `bPrfMsg` with the
returned signatures recorded and `w` as output bit.  Explicit whenever `w` is. -/
noncomputable def bPrfMsgW (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    MsgPrfAdv prims :=
  ((do
    let pkSeed ← (monadLift pkSeedDist :
      OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.PkSeed)
    let tbl ← (monadLift (sampleTable vp prims) :
      OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) (SecretTable vp prims))
    let pk := idealPk vp prims tbl pkSeed
    let z ← runForgerSig A pk fun m => do
      let addrnd ← (monadLift (optRand pk) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.Y)
      let R ← (PRFScheme.functionQuery (addrnd, m) :
        OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.Y)
      return idealSign vp prims tbl m pk R
    return w pk z.1 z.2) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) Bool)

/-- The signing procedure `bPrfMsgW` hands to the harness. -/
private noncomputable def bSign (pk : PublicKeyCore prims.core) (tbl : SecretTable vp prims)
    (m : List Byte) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y)
      (GeneralScheme.SignatureCore vp prims.core) := do
  let addrnd ← (monadLift (optRand pk) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.Y)
  let R ← (PRFScheme.functionQuery (addrnd, m) :
    OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.Y)
  return idealSign vp prims tbl m pk R

private theorem realRun_eq (A : Forger vp prims optRand pkSeedDist)
    (pk : PublicKeyCore prims.core) (tbl : SecretTable vp prims) (k : prims.SkPrf) :
    simulateQ ((msgPrf vp prims).prfRealQueryImpl k)
        (runForgerSig A pk (bSign (optRand := optRand) pk tbl)) =
      (tableAlg vp prims optRand pkSeedDist).runWithSigningOracle pk (tbl, k) (A.main pk) := by
  rw [runWithSigningOracle_eq_appendLog]
  unfold runForgerSig
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  have hH : ((msgPrf vp prims).prfRealQueryImpl k).mapStateTBase
      (QueryImpl.liftTarget (StateT (SigLog vp prims)
          (OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y)))
        (QueryImpl.ofLift unifSpec
          (OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y))) +
        sigSignOracle (bSign (optRand := optRand) pk tbl)) =
      (QueryImpl.liftTarget (StateT (SigLog vp prims) ProbComp)
          (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
        appendLog ((tableAlg vp prims optRand pkSeedDist).sign pk (tbl, k))) := by
    funext t
    cases t with
    | inl n =>
      refine StateT.ext fun s => ?_
      simp [QueryImpl.mapStateTBase]
      exact PRFScheme.simulateQ_prfRealQueryImpl_liftComp _ k (liftM (unifSpec.query n))
    | inr m =>
      refine StateT.ext fun s => ?_
      simp [QueryImpl.mapStateTBase, sigSignOracle, appendLog, bSign, tableAlg]
      rw [show simulateQ ((msgPrf vp prims).prfRealQueryImpl k)
          (monadLift (optRand pk) :
            OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.Y) =
          optRand pk from PRFScheme.simulateQ_prfRealQueryImpl_liftComp _ k (optRand pk)]
      rfl
  rw [hH]

/-- Real world of the `PRF_msg` game at `bPrfMsgW w A`: the chosen-message experiment against
`tableAlg` with final check `w`. -/
theorem prfReal_bPrfMsgW (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    𝒟[(msgPrf vp prims).prfRealExperiment (bPrfMsgW w A)] {true} =
      prTrue (expW (tableAlg vp prims optRand pkSeedDist) w A) := by
  have hL : (msgPrf vp prims).prfRealExperiment (bPrfMsgW w A) = (do
      let k ← $ᵗ prims.SkPrf
      let pkSeed ← pkSeedDist
      let tbl ← sampleTable vp prims
      let z ← (tableAlg vp prims optRand pkSeedDist).runWithSigningOracle
        (idealPk vp prims tbl pkSeed) (tbl, k) (A.main (idealPk vp prims tbl pkSeed))
      pure (w (idealPk vp prims tbl pkSeed) z.1 z.2)) := by
    unfold PRFScheme.prfRealExperiment bPrfMsgW
    refine bind_congr fun k => ?_
    simp only [simulateQ_bind, simulateQ_pure]
    have hlift : ∀ {β : Type} (ob : ProbComp β),
        simulateQ ((msgPrf vp prims).prfRealQueryImpl k)
          (monadLift ob :
            OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) β) = ob :=
      fun ob => PRFScheme.simulateQ_prfRealQueryImpl_liftComp _ k ob
    rw [hlift, hlift]
    refine bind_congr fun pkSeed => bind_congr fun tbl => ?_
    have h := realRun_eq A (idealPk vp prims tbl pkSeed) tbl k
    unfold bSign at h
    rw [h]
  have hR : expW (tableAlg vp prims optRand pkSeedDist) w A = (do
      let pkSeed ← pkSeedDist
      let tbl ← sampleTable vp prims
      let k ← $ᵗ prims.SkPrf
      let z ← (tableAlg vp prims optRand pkSeedDist).runWithSigningOracle
        (idealPk vp prims tbl pkSeed) (tbl, k) (A.main (idealPk vp prims tbl pkSeed))
      pure (w (idealPk vp prims tbl pkSeed) z.1 z.2)) := by
    unfold expW
    simp [tableAlg]
  rw [hL, hR, prTrue]
  congr 1
  refine (OracleComp.evalDist_bind_bind_swap _ _ _).trans ?_
  refine evalDist_bind_congr_of_support _ _ _ fun pkSeed _ => ?_
  exact OracleComp.evalDist_bind_bind_swap _ _ _

/-! ## Ideal world: the random-oracle cache is a function of the `G2` transcript -/

/-- The random-oracle cache determined by a `G2` transcript: the point `(opt_rand, M)` holds the
randomizer of the first transcript entry with that pair. -/
private def cacheOf (log : G2Log prims) : ((prims.Y × List Byte) →ₒ prims.Y).QueryCache :=
  OracleSpec.QueryCache.ofFn fun d : prims.Y × List Byte =>
    (log.find? (fun e => decide (e.1 = d.2 ∧ e.2.1 = d.1))).map (·.2.2)

private theorem cacheOf_apply (log : G2Log prims) (d : prims.Y × List Byte) :
    cacheOf log d = (log.find? (fun e => decide (e.1 = d.2 ∧ e.2.1 = d.1))).map (·.2.2) := rfl

/-- One lazy-randomizer step of `G2` is one random-oracle step on the transcript's cache. -/
private theorem lazyRandomizer_step (log : G2Log prims) (m : List Byte) (a : prims.Y) :
    (fun R => (R, cacheOf (log ++ [(m, a, R)]))) <$> lazyRandomizer log m a =
      (((prims.Y × List Byte) →ₒ prims.Y).randomOracle (a, m)).run (cacheOf log) := by
  rw [randomOracle.run_eq]
  unfold lazyRandomizer
  have hp : (fun e : List Byte × prims.Y × prims.Y => decide (e.1 = m ∧ e.2.1 = a)) =
      fun x => decide (x.1 = m) && decide (x.2.1 = a) := by funext x; simp
  rw [hp]
  cases h : log.find? (fun x => decide (x.1 = m) && decide (x.2.1 = a)) with
  | some e =>
    have hc : cacheOf log (a, m) = some e.2.2 := by simp [cacheOf_apply, h]
    simp only [hc, map_pure]
    congr 2
    refine OracleSpec.QueryCache.ext fun d => ?_
    simp only [cacheOf_apply, List.find?_append]
    by_cases hd : d = (a, m)
    · subst hd; simp [h]
    · have hn : ¬ (m = d.2 ∧ a = d.1) := fun hh => hd (Prod.ext hh.2.symm hh.1.symm)
      simp [hn]
  | none =>
    have hc : cacheOf log (a, m) = none := by simp [cacheOf_apply, h]
    simp only [hc]
    rw [map_eq_bind_pure_comp]
    refine bind_congr fun R => ?_
    simp only [Function.comp]
    congr 2
    refine OracleSpec.QueryCache.ext fun d => ?_
    by_cases hd : d = (a, m)
    · subst hd
      simp [cacheOf_apply, List.find?_append, h]
    · have hn : ¬ (m = d.2 ∧ a = d.1) := fun hh => hd (Prod.ext hh.2.symm hh.1.symm)
      rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ hd]
      simp [cacheOf_apply, List.find?_append, hn]


/-- Running the forger inside `bPrfMsgW` under the lazy random oracle is `g2Run`, with the
returned pairs and the cache read off the transcript. -/
private theorem idealRun_eq (A : Forger vp prims optRand pkSeedDist)
    (pk : PublicKeyCore prims.core) (tbl : SecretTable vp prims) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := prims.Y × List Byte) (R := prims.Y))
        (runForgerSig A pk (bSign (optRand := optRand) pk tbl))).run ∅ =
      (fun z => ((z.1, sigLogOf tbl pk z.2), cacheOf z.2)) <$> g2Run A tbl pk := by
  unfold runForgerSig g2Run g2RunWith
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have h := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
      g2SignOracle optRand pk (fun m R => idealSign vp prims tbl m pk R))
    ((PRFScheme.prfIdealQueryImpl (D := prims.Y × List Byte) (R := prims.Y)).mapStateTBase
      (QueryImpl.liftTarget (StateT (SigLog vp prims)
          (OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y)))
        (QueryImpl.ofLift unifSpec
          (OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y))) +
        sigSignOracle (bSign (optRand := optRand) pk tbl))).flattenStateT
    (fun log : G2Log prims => (sigLogOf tbl pk log, cacheOf log)) ?_ (A.main pk) []
  · refine (congrArg (Functor.map (fun z : _ × (SigLog vp prims ×
        ((prims.Y × List Byte) →ₒ prims.Y).QueryCache) => ((z.1, z.2.1), z.2.2))) h).symm.trans ?_
    simp [Functor.map_map]
  · intro t s
    have hl : ∀ {β : Type} (ob : ProbComp β),
        (simulateQ (PRFScheme.prfIdealQueryImpl (D := prims.Y × List Byte) (R := prims.Y))
          (monadLift ob :
            OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) β)).run
            (cacheOf s) = (·, cacheOf s) <$> ob :=
      fun ob => OracleSpec.simulateQ_romImpl_liftM_run ob (cacheOf s)
    cases t with
    | inl n =>
      simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase]
      refine Eq.trans ?_ (congrArg (Functor.map _) (hl (liftM (unifSpec.query n))).symm)
      simp [Functor.map_map]
    | inr m =>
      simp [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, sigSignOracle, appendLog, bSign,
        g2SignOracle, sigLogOf]
      rw [hl, bind_map_left]
      refine bind_congr fun a => ?_
      refine Eq.trans ?_ (congrArg (Functor.map _) (lazyRandomizer_step s m a))
      simp [Functor.map_map]

/-- Ideal world of the `PRF_msg` game at `bPrfMsgW w A` is `G2` with final check `w`. -/
theorem prfIdeal_bPrfMsgW (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    𝒟[PRFScheme.prfIdealExperiment (bPrfMsgW w A)] {true} = prTrue (g2W w A) := by
  have hL : PRFScheme.prfIdealExperiment (bPrfMsgW w A) = g2W w A := by
    unfold PRFScheme.prfIdealExperiment bPrfMsgW g2W
    have hl : ∀ {β : Type} (ob : ProbComp β)
        (c : ((prims.Y × List Byte) →ₒ prims.Y).QueryCache),
        (simulateQ (PRFScheme.prfIdealQueryImpl (D := prims.Y × List Byte) (R := prims.Y))
          (monadLift ob :
            OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) β)).run c =
          (·, c) <$> ob :=
      fun ob c => OracleSpec.simulateQ_romImpl_liftM_run ob c
    simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, map_bind, hl,
      bind_map_left]
    refine bind_congr fun pkSeed => bind_congr fun tbl => ?_
    have h := idealRun_eq A (idealPk vp prims tbl pkSeed) tbl
    unfold bSign at h
    rw [h]
    simp
  rw [hL, prTrue]

/-- **`PRF_msg` hop for the final check `w`.** -/
theorem stepPRFmsgW (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (expW (tableAlg vp prims optRand pkSeedDist) w A) ≤
      prTrue (g2W w A) + (msgPrf vp prims).prfAdvantage (bPrfMsgW w A) := by
  rw [← prfReal_bPrfMsgW, ← prfIdeal_bPrfMsgW, PRFScheme.prfAdvantage]
  exact MeasureTheory.Measure.apply_true_le_add_boolDist _ _

/-- Two lifted `ProbComp` prefixes make no function query. -/
private theorem queryBound_prefix {ι : Type} {hs : OracleSpec ι} {α β γ : Type}
    (x : ProbComp α) (y : ProbComp β) (f : α → β → OracleComp (unifSpec + hs) γ) (n : ℕ)
    (h : ∀ a b, IsQueryBoundP (f a b) (fun i => i.isRight = true) n) :
    IsQueryBoundP ((monadLift x : OracleComp (unifSpec + hs) α) >>= fun a =>
      (monadLift y : OracleComp (unifSpec + hs) β) >>= fun b => f a b)
      (fun i => i.isRight = true) n := by
  have key := isQueryBoundP_bind (isQueryBoundP_liftM_isRight (hs := hs) x) fun a _ =>
    isQueryBoundP_bind (isQueryBoundP_liftM_isRight (hs := hs) y) fun b _ => h a b
  simpa only [Nat.zero_add] using key

/-- A query-free continuation does not change the bound. -/
private theorem queryBound_bind_pure {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (p : ι → Prop) [DecidablePred p] (oa : OracleComp spec α) (f : α → OracleComp spec β) (n : ℕ)
    (h : IsQueryBoundP oa p n) (hf : ∀ x, ∃ b, f x = pure b) :
    IsQueryBoundP (oa >>= f) p n := by
  have key := isQueryBoundP_bind (ob := f) (m := 0) h fun x _ => by
    obtain ⟨b, hb⟩ := hf x
    rw [hb]; exact isQueryBoundP_pure _ _ _
  simpa only [Nat.add_zero] using key


/-- Resource lemma: one `PRF_msg` query per signing query. -/
theorem bPrfMsgW_queryBound (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfMsgW w A) (fun i => i.isRight = true) qs := by
  unfold bPrfMsgW
  refine queryBound_prefix _ _ _ _ fun pkSeed tbl => ?_
  refine queryBound_bind_pure _ _ _ _ ?_ (fun x => ⟨_, rfl⟩)
  unfold runForgerSig
  refine IsQueryBoundP.simulateQ_run_add_inr_of_step (fun t => by simp) (hA _) ?_ ?_ ?_ _
  · intro t s
    simp only [QueryImpl.liftTarget_apply, StateT.run_monadLift]
    refine queryBound_bind_pure _ _ _ _ ?_ (fun x => ⟨_, rfl⟩)
    exact isQueryBoundP_liftM_isRight (liftM (unifSpec.query t) : ProbComp _)
  · intro t _ s
    have key := isQueryBoundP_bind (m := 1)
      (isQueryBoundP_liftM_isRight (hs := (prims.Y × List Byte) →ₒ prims.Y)
        (optRand (idealPk vp prims tbl pkSeed))) fun a _ =>
      queryBound_bind_pure (fun i => i.isRight = true)
        (PRFScheme.functionQuery (a, t) :
          OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) prims.Y)
        (fun R => pure (idealSign vp prims tbl t (idealPk vp prims tbl pkSeed) R,
          s ++ [⟨t, idealSign vp prims tbl t (idealPk vp prims tbl pkSeed) R⟩])) 1
        (by simp [PRFScheme.functionQuery]) (fun x => ⟨_, rfl⟩)
    simpa [sigSignOracle, appendLog] using key
  · intro t ht
    simp at ht

#print axioms Reduction.prfReal_bPrfMsgW
#print axioms Reduction.prfIdeal_bPrfMsgW
#print axioms Reduction.stepPRFmsgW
#print axioms Reduction.bPrfMsgW_queryBound

end Reduction
