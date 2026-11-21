import Reduction.Gen.Resources

/-!
# Resources of the reduction adversaries around a general-spec forger, part B

Single-phase adversaries (item 3), the pre-seed phases (item 1) and the bundle (item 4).
See the header of `Reduction/Gen/Resources.lean`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction.Gen

attribute [local irreducible] arityTargets tcrTargets

set_option linter.unusedSectionVars false

/-! ## The lazy cache around general open programs -/

section LazyRes

variable {κ : Type} (ds : OracleSpec κ)
variable {ι κh : Type} {gspec : OracleSpec ι} {hspec : OracleSpec κh} {D V α : Type}
  [DecidableEq D]

/-- `Lazy.lazyRes` for an open program over the general sampling interface: the secret oracle
replaced by the lazy cache over a draw oracle (the resource-explicit program). -/
def lazyResG (P : OracleComp ((ds + unifSpec) + (gspec + ((D →ₒ V) + hspec))) α) :
    OracleComp ((ds + unifSpec) + (gspec + ((Unit →ₒ V) + hspec))) α :=
  Prod.fst <$> runGO ds Lazy.lazyImplR P []

/-- On a `ds`-free open program, `lazyResG` is `lazyRes`. -/
theorem lazyResG_embed (P : OracleComp (Lazy.RSpec gspec D V hspec) α) :
    lazyResG ds (embed ds P) = embed ds (Lazy.lazyRes P) := by
  rw [lazyResG, runGO_embed, Lazy.lazyRes, StateT.run'_eq, embed_map]

/-- `lazyRunG` is the interpretation of the resource-explicit program (a draw is a fresh uniform
sample, a hash query is evaluated by `hI`; `ds`-queries, uniform bits and game queries are
forwarded). -/
theorem lazyRunG_eq_interp [SampleableType V] (hI : QueryImpl hspec Id)
    (P : OracleComp ((ds + unifSpec) + (gspec + ((D →ₒ V) + hspec))) α) :
    lazyRunG ds hI P = wrapS ds (Lazy.interp hI) (lazyResG ds P) := by
  unfold lazyRunG lazyResG
  rw [wrapS_map, wrapS_runGO ds (Lazy.interp hI) Lazy.lazyImplR (Lazy.lazyImpl hI) (fun t s ↦ by
    have := Lazy.simulateQ_interp_lazyImplR (gspec := gspec) (D := D) (V := V) hI
      (liftM ((Lazy.RSpec gspec D V hspec).query t)) s
    rwa [simulateQ_spec_query, simulateQ_spec_query] at this)]

/-- Queries of kind `K` pass through the cache (for `K = .sec`: the draws). -/
theorem lazyResG_kindBound (K : Lazy.Kind) (hK : K ≠ .unif)
    (P : OracleComp ((ds + unifSpec) + (gspec + ((D →ₒ V) + hspec))) α) (n : ℕ)
    (h : IsQueryBoundP P (fun t ↦ kindG t = K) n) :
    IsQueryBoundP (lazyResG ds P) (fun t ↦ kindG t = K) n := by
  rw [kindG_iff_liftP ds gspec K hK] at h ⊢
  rw [lazyResG, isQueryBoundP_map_iff]
  refine runGO_queryBound ds _ _ Lazy.lazyImplR [] n n (fun t ht ↦ ?_) P h
  have := Lazy.lazyRes_bound K t n ht
  unfold Lazy.lazyRes at this
  rwa [StateT.run'_eq, isQueryBoundP_map_iff] at this

/-- Game queries of the lazy run: one per game query of the open program. -/
theorem lazyRunG_gameBound [SampleableType V] (hI : QueryImpl hspec Id)
    (P : OracleComp ((ds + unifSpec) + (gspec + ((D →ₒ V) + hspec))) α) (n : ℕ)
    (h : IsQueryBoundP P (fun t ↦ kindG t = .game) n) :
    IsQueryBoundP (lazyRunG ds hI P) (fun i ↦ i.isRight = true) n := by
  rw [kindG_iff_liftP ds gspec .game (by decide)] at h
  rw [isRight_iff_liftP, lazyRunG, isQueryBoundP_map_iff]
  refine runGO_queryBound ds _ _ (Lazy.lazyImpl hI) [] n n (fun t ht ↦ ?_) P h
  have := Lazy.lazyRun_gameBound hI t n ht
  rwa [Lazy.lazyRun_eq, StateT.run'_eq, isQueryBoundP_map_iff] at this

end LazyRes

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-! ## (3) Single-phase adversaries -/

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- **PRF queries of `bPrfCG F`**: the classical bound. -/
theorem bPrfCG_queryBound (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs) :
    IsQueryBoundP (bPrfCG ds optRand pkSeedDist F) (fun i ↦ i.isRight = true)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) := by
  refine wrapS_queryBound_isRight ds _ (fun t n h ↦ Restrict.queryBound_restrict _ h) _ _ ?_
  rw [isRight_iff_liftP]
  exact openAdv_queryBound ds (fun i ↦ i.isRight = true) _ ([], constSig default) _ _ _ _ _ qs _
    (fun A₀ hA₀ ↦ by
      have := bPrf_queryBound_exact (⟨A₀⟩ : Forger vp prims optRand pkSeedDist) qs hA₀
      rwa [bPrf_eq_pre] at this)
    F fun pk ↦ (isRight_iff_liftP ds _ _).1 (hF pk)

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- **PRF queries of `bPrfWCG w F`**: the classical bound. -/
theorem bPrfWCG_queryBound (w : WinCheck vp prims) (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs) :
    IsQueryBoundP (bPrfWCG ds optRand pkSeedDist w F) (fun i ↦ i.isRight = true)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) := by
  refine wrapS_queryBound_isRight ds _ (fun t n h ↦ Restrict.queryBound_restrict _ h) _ _ ?_
  rw [isRight_iff_liftP]
  exact openAdv_queryBound ds (fun i ↦ i.isRight = true) _ ([], constSig default) _ _ _ _ _ qs _
    (fun A₀ hA₀ ↦ by
      have := bPrfW_queryBound_exact w (⟨A₀⟩ : Forger vp prims optRand pkSeedDist) qs hA₀
      rwa [bPrfW_eq_pre] at this)
    F fun pk ↦ (isRight_iff_liftP ds _ _).1 (hF pk)

/-- The raw kind budget of the lazy open programs. -/
def openB (vp : ValidatedParams) (K : Lazy.Kind) (qs : ℕ) : ℕ :=
  Lazy.keygenB vp (Lazy.ind K .sec) (Lazy.ind K .hash) +
    qs * (Lazy.ind K .game + Lazy.signB vp (Lazy.ind K .sec) (Lazy.ind K .hash))

theorem openB_game (qs : ℕ) : openB vp .game qs ≤ qs := by
  simp [openB, Lazy.ind, Lazy.keygenB_game, Lazy.signB_game]

theorem openB_sec (qs : ℕ) :
    openB vp .sec qs ≤ 2 ^ vp.params.hp * vp.params.len + qs * signReads vp :=
  Nat.add_le_add Lazy.keygenB_sec (Nat.mul_le_mul_left _ (by
    simpa [Lazy.ind] using Lazy.signB_sec (vp := vp)))

theorem openB_hash (qs : ℕ) :
    openB vp .hash qs ≤ Lazy.keygenHashes vp + qs * Lazy.signHashes vp :=
  Nat.add_le_add Lazy.keygenB_hash (Nat.mul_le_mul_left _ (by
    simpa [Lazy.ind] using Lazy.signB_hash (vp := vp)))

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- Queries of kind `K` of `msgOpenG F`. -/
theorem msgOpenG_kindBound (K : Lazy.Kind) (hK : K ≠ .unif) (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs) :
    IsQueryBoundP (msgOpenG ds optRand pkSeedDist F) (fun t ↦ kindG t = K) (openB vp K qs) := by
  rw [kindG_iff_liftP ds (Lazy.msgG prims) K hK]
  exact openShape2_queryBound ds (fun i ↦ i.isRight = true) _ ([], constSig default) _ _
    (fun pkSeed root ↦ (⟨pkSeed, root⟩ : PublicKeyCore prims.core)) _ [] _ qs _
    (fun A₀ hA₀ ↦ Lazy.msgOpen_kindBound (⟨A₀⟩ : Forger vp prims optRand pkSeedDist) K hK qs hA₀)
    F fun pk ↦ (isRight_iff_liftP ds _ _).1 (hF pk)

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- Queries of kind `K` of `msgOpenWG w F`. -/
theorem msgOpenWG_kindBound (w : WinCheck vp prims) (K : Lazy.Kind) (hK : K ≠ .unif)
    (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs) :
    IsQueryBoundP (msgOpenWG ds optRand pkSeedDist w F) (fun t ↦ kindG t = K)
      (openB vp K qs) := by
  rw [kindG_iff_liftP ds (Lazy.msgG prims) K hK]
  exact openShape2_queryBound ds (fun i ↦ i.isRight = true) _ ([], constSig default) _ _
    (fun pkSeed root ↦ (⟨pkSeed, root⟩ : PublicKeyCore prims.core)) _ [] _ qs _
    (fun A₀ hA₀ ↦ Lazy.msgOpenW_kindBound w (⟨A₀⟩ : Forger vp prims optRand pkSeedDist) K hK qs
      hA₀)
    F fun pk ↦ (isRight_iff_liftP ds _ _).1 (hF pk)

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- Queries of kind `K` of `itsrOpenG F`. -/
theorem itsrOpenG_kindBound (K : Lazy.Kind) (hK : K ≠ .unif) (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs) :
    IsQueryBoundP (itsrOpenG ds optRand pkSeedDist F) (fun t ↦ kindG t = K) (openB vp K qs) := by
  rw [kindG_iff_liftP ds (Lazy.itsrG prims) K hK]
  exact openShape2_queryBound ds (fun i ↦ i.isRight = true) _ ([], constSig default) _ _
    (fun pkSeed root ↦ (⟨pkSeed, root⟩ : PublicKeyCore prims.core)) _ [] _ qs _
    (fun A₀ hA₀ ↦ Lazy.itsrOpen_kindBound (⟨A₀⟩ : Forger vp prims optRand pkSeedDist) K hK qs hA₀)
    F fun pk ↦ (isRight_iff_liftP ds _ _).1 (hF pk)

/-! ## (1) The pre-seed phases are the classical programs -/

variable {optRand pkSeedDist}

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
/-- A forger that makes no query satisfies every signing-query bound. -/
theorem dummyForger_queryBound (qs : ℕ) (pk : PublicKeyCore prims.core) :
    IsQueryBoundP ((dummyForger (optRand := optRand) (pkSeedDist := pkSeedDist)).main pk)
      (fun i ↦ i.isRight = true) qs :=
  isQueryBoundP_pure _ _ _

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem chooseArM_eq (n : ℕ) (A₀ : Forger vp prims optRand pkSeedDist) :
    chooseArM optRand pkSeedDist n = (bTcrArM n A₀).choose := by
  unfold chooseArM bTcrArM
  rfl

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem udPickW_eq (A₀ : Forger vp prims optRand pkSeedDist) :
    udPickW optRand pkSeedDist = (rUd pkSeedDist (Lazy.bWotsS A₀)).pick := by
  unfold udPickW rUd
  rfl

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem preChooseW_eq (A₀ : Forger vp prims optRand pkSeedDist) :
    preChooseW optRand pkSeedDist = (rPre pkSeedDist (Lazy.bWotsS A₀)).choose := by
  unfold preChooseW rPre
  rfl

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
theorem tcrChooseW_eq (A₀ : Forger vp prims optRand pkSeedDist) :
    tcrChooseW optRand pkSeedDist = (rTcrT pkSeedDist (Lazy.bWotsS A₀)).choose := by
  unfold tcrChooseW rTcrT
  rfl

-- the statements unify the state/spec types of the two adversary structures (slow, not deep)
set_option maxHeartbeats 1600000 in
theorem bTcrArMG_choose (n : ℕ) (F : GFam ds vp prims) (A₀ : Forger vp prims optRand pkSeedDist) :
    (bTcrArMG ds optRand pkSeedDist n F).choose = embed ds (bTcrArM n A₀).choose :=
  congrArg (embed ds) (chooseArM_eq n A₀)

theorem toDsprG_choose (F : GFam ds vp prims) (A₀ : Forger vp prims optRand pkSeedDist) :
    (toDsprG ds optRand pkSeedDist F).choose = embed ds (toDspr (Lazy.bOpenPreS A₀)).choose := rfl

theorem toTcrG_choose (F : GFam ds vp prims) (A₀ : Forger vp prims optRand pkSeedDist) :
    (toTcrG ds optRand pkSeedDist F).choose = embed ds (toTcr (Lazy.bOpenPreS A₀)).choose := rfl

theorem rUdG_pick (F : GFam ds vp prims) (A₀ : Forger vp prims optRand pkSeedDist) :
    (rUdG ds optRand pkSeedDist F).pick = embed ds (rUd pkSeedDist (Lazy.bWotsS A₀)).pick :=
  congrArg (embed ds) (udPickW_eq A₀)

set_option maxHeartbeats 1600000 in
theorem rPreG_choose (F : GFam ds vp prims) (A₀ : Forger vp prims optRand pkSeedDist) :
    (rPreG ds optRand pkSeedDist F).choose =
      embed ds (rPre pkSeedDist (Lazy.bWotsS A₀)).choose :=
  congrArg (embed ds) (preChooseW_eq A₀)

set_option maxHeartbeats 1600000 in
theorem rTcrTG_choose (F : GFam ds vp prims) (A₀ : Forger vp prims optRand pkSeedDist) :
    (rTcrTG ds optRand pkSeedDist F).choose =
      embed ds (rTcrT pkSeedDist (Lazy.bWotsS A₀)).choose :=
  congrArg (embed ds) (tcrChooseW_eq A₀)

variable (optRand pkSeedDist)

/-- The pre-seed programs of the six two-phase adversaries around `F` are the embedded pre-seed
programs of the classical adversaries around `A₀`. -/
structure Phase1Eq (F : GFam ds vp prims) (A₀ : Forger vp prims optRand pkSeedDist) : Prop where
  memo : ∀ n, (bTcrArMG ds optRand pkSeedDist n F).choose = embed ds (bTcrArM n A₀).choose
  dspr : (toDsprG ds optRand pkSeedDist F).choose = embed ds (toDspr (Lazy.bOpenPreS A₀)).choose
  tcr : (toTcrG ds optRand pkSeedDist F).choose = embed ds (toTcr (Lazy.bOpenPreS A₀)).choose
  ud : (rUdG ds optRand pkSeedDist F).pick = embed ds (rUd pkSeedDist (Lazy.bWotsS A₀)).pick
  pre : (rPreG ds optRand pkSeedDist F).choose =
    embed ds (rPre pkSeedDist (Lazy.bWotsS A₀)).choose
  wtcr : (rTcrTG ds optRand pkSeedDist F).choose =
    embed ds (rTcrT pkSeedDist (Lazy.bWotsS A₀)).choose

variable {optRand pkSeedDist} in
theorem phase1Eq (F : GFam ds vp prims) (A₀ : Forger vp prims optRand pkSeedDist) :
    Phase1Eq ds optRand pkSeedDist F A₀ :=
  ⟨fun n ↦ bTcrArMG_choose ds n F A₀, toDsprG_choose ds F A₀, toTcrG_choose ds F A₀,
    rUdG_pick ds F A₀, rPreG_choose ds F A₀, rTcrTG_choose ds F A₀⟩

variable {optRand pkSeedDist} in
/-- **(1) Phase 1 (pre-seed).**  For every classical forger `A₀` with at most `qs` signing
queries: the classical bundle for `A₀`, and for EVERY general forger family `F` the pre-seed
programs of the two-phase adversaries around `F` are the embedded pre-seed programs of the
classical adversaries around `A₀`.  So the classical phase-1 facts of the bundle (targets exactly
the cap, collection counts, closed forms of the runs, sample counts) are facts about the
pre-seed programs of the general adversaries; their runs in the wrapper games are the lifted
classical runs (`runG_embed`). -/
theorem phase1_resourcesG (hS : Structural vp prims) (A₀ : Forger vp prims optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A₀.main pk) (fun i ↦ i.isRight = true) qs) :
    FinalResourcesFinal A₀ qs (Resources2.directCounts vp qs)
        (Lazy.keygenHashes vp + qs * Lazy.signHashes vp +
          (1 + Resources2.verifyHashes vp * 2)) ∧
      ∀ F : GFam ds vp prims, Phase1Eq ds optRand pkSeedDist F A₀ :=
  ⟨final_resources_final hS A₀ qs hA, fun F ↦ phase1Eq ds F A₀⟩

/-- **(1), forger-free form**: the classical bundle of the query-free `dummyForger` holds at
every budget `qs`, and the pre-seed programs of the general adversaries are those of the classical
adversaries around `dummyForger`. -/
theorem phase1_resourcesG_dummy (hS : Structural vp prims) (qs : ℕ) :
    FinalResourcesFinal (dummyForger (optRand := optRand) (pkSeedDist := pkSeedDist)) qs
        (Resources2.directCounts vp qs)
        (Lazy.keygenHashes vp + qs * Lazy.signHashes vp +
          (1 + Resources2.verifyHashes vp * 2)) ∧
      ∀ F : GFam ds vp prims, Phase1Eq ds optRand pkSeedDist F dummyForger :=
  phase1_resourcesG ds hS dummyForger qs fun pk ↦ dummyForger_queryBound qs pk

/-! ## (4) The bundle -/

/-- **Resources of the general-spec reduction adversaries** around a forger family `F` with at
most `qs` signing queries on every path (`ds`- and uniform queries of the forger are its own and
are not counted).  `c` are the closed forms of `Resources2.directCounts`, `memoP2` the bound on
the own post-seed hash evaluations of each class adversary.  "Open program" =
`OracleComp ((ds + unifSpec) + (gspec + (secret oracle + hash oracle)))`; `kindG` classifies its
queries (`ds`- and uniform queries: `.unif`); it is interpreted by
`wrapS ds (Lazy.tblImpl (PublicHash.impl prims) tbl)` (secret reads from the table, hash queries
evaluated by `prims`, `ds`-queries forwarded), the lazy programs by `wrapS ds (Lazy.interp …)`
after the cache `lazyResG`. -/
structure FinalResourcesG (F : GFam ds vp prims) (qs : ℕ) (c : Resources2.DirectCounts)
    (memoP2 : ℕ) : Prop where
  /-- Phase 1: the classical bundle of the query-free forger … -/
  phase1 : FinalResourcesFinal (dummyForger (optRand := optRand) (pkSeedDist := pkSeedDist)) qs c
    memoP2
  /-- … whose pre-seed programs are those of the adversaries around `F`. -/
  phase1_eq : Phase1Eq ds optRand pkSeedDist F dummyForger
  prf : IsQueryBoundP (bPrfCG ds optRand pkSeedDist F) (fun i ↦ i.isRight = true) c.secretReads
  prfSuf : IsQueryBoundP (bPrfWCG ds optRand pkSeedDist sufCheck F) (fun i ↦ i.isRight = true)
    c.secretReads
  msg : IsQueryBoundP (bPrfMsgLG ds optRand pkSeedDist F) (fun i ↦ i.isRight = true) qs
  msg_interp : bPrfMsgLG ds optRand pkSeedDist F =
    wrapS ds (Lazy.interp (PublicHash.impl prims)) (lazyResG ds (msgOpenG ds optRand pkSeedDist F))
  msg_draws : IsQueryBoundP (lazyResG ds (msgOpenG ds optRand pkSeedDist F))
    (fun t ↦ kindG t = .sec) c.secretReads
  msg_hashes : IsQueryBoundP (lazyResG ds (msgOpenG ds optRand pkSeedDist F))
    (fun t ↦ kindG t = .hash) c.lazyHashes
  msgSuf : IsQueryBoundP (bPrfMsgWLG ds optRand pkSeedDist sufCheck F)
    (fun i ↦ i.isRight = true) qs
  msgSuf_interp : bPrfMsgWLG ds optRand pkSeedDist sufCheck F =
    wrapS ds (Lazy.interp (PublicHash.impl prims))
      (lazyResG ds (msgOpenWG ds optRand pkSeedDist sufCheck F))
  msgSuf_draws : IsQueryBoundP (lazyResG ds (msgOpenWG ds optRand pkSeedDist sufCheck F))
    (fun t ↦ kindG t = .sec) c.secretReads
  msgSuf_hashes : IsQueryBoundP (lazyResG ds (msgOpenWG ds optRand pkSeedDist sufCheck F))
    (fun t ↦ kindG t = .hash) c.lazyHashes
  itsr : IsQueryBoundP (bItsrLG ds optRand pkSeedDist F).main (fun i ↦ i.isRight = true) qs
  itsr_interp : (bItsrLG ds optRand pkSeedDist F).main =
    wrapS ds (Lazy.interp (PublicHash.impl prims))
      (lazyResG ds (itsrOpenG ds optRand pkSeedDist F))
  itsr_draws : IsQueryBoundP (lazyResG ds (itsrOpenG ds optRand pkSeedDist F))
    (fun t ↦ kindG t = .sec) c.secretReads
  itsr_hashes : IsQueryBoundP (lazyResG ds (itsrOpenG ds optRand pkSeedDist F))
    (fun t ↦ kindG t = .hash) c.lazyHashes
  fors_tcr_phase2 : ∀ (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y))
      (ys : List prims.Y) (pk : prims.PkSeed),
    (toTcrG ds optRand pkSeedDist F).forge (tbl, tg, ys) pk =
      runG ds (SM_DT_OpenPRE_SourceFinalValidity.findOracles tg)
        (wrapS ds (Lazy.tblImpl (PublicHash.impl prims) tbl)
          (findOpenFullG ds optRand F pk ys)) [] >>= fun z ↦ pure z.1
  fors_dspr_phase2 : ∀ (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y))
      (ys : List prims.Y) (pk : prims.PkSeed),
    (toDsprG ds optRand pkSeedDist F).guess (tbl, tg, ys) pk =
      runG ds (SM_DT_OpenPRE_SourceFinalValidity.findOracles tg)
        (wrapS ds (Lazy.tblImpl (PublicHash.impl prims) tbl)
          (findOpenFullG ds optRand F pk ys)) [] >>= fun z ↦ pure (z.1.1,
            decide ((tg[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2))
  fors_phase2_hashes : ∀ pk ys, IsQueryBoundP (findOpenFullG ds optRand F pk ys)
    (fun t ↦ kindG t = .hash) c.forsP2
  fors_phase2_openings : ∀ pk ys, IsQueryBoundP (findOpenFullG ds optRand F pk ys)
    (fun t ↦ kindG t = .game) c.openings
  memo_phase2 : ∀ {ι : Type} (gspec : OracleSpec ι) (n : ℕ) (tbl : SecretTable vp prims)
      (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed),
    liftG ds (G := gspec) ((bTcrArMG ds optRand pkSeedDist n F).forge (tbl, L) pk) =
      wrapS ds (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (memoForgeOpenG ds optRand gspec F L pk) >>= fun jm ↦ pure (classOut prims n L jm)
  memo_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι)
      (L : List (prims.AdrsKey × List prims.Y)) (pk : prims.PkSeed),
    IsQueryBoundP (memoForgeOpenG ds optRand gspec F L pk) (fun t ↦ kindG t = .hash) memoP2
  ud_phase2 : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    liftG ds (G := gspec)
        ((rUdG ds optRand pkSeedDist F).distinguish ((tbl, hist, root), hist2) pk) =
      wrapS ds (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2OG ds optRand gspec F tbl hist root pk
          fun x ↦ Resources2.wotsWinO pk hist2 x.1 x.2.1 x.2.2)
  ud_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    IsQueryBoundP (wotsPhase2OG ds optRand gspec F tbl hist root pk
      fun x ↦ Resources2.wotsWinO pk hist2 x.1 x.2.1 x.2.2) (fun t ↦ kindG t = .hash) c.udP2
  pre_phase2 : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    liftG ds (G := gspec)
        ((rPreG ds optRand pkSeedDist F).invert ((tbl, hist, root), hist2) pk) =
      wrapS ds (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2OG ds optRand gspec F tbl hist root pk
          fun x ↦ Resources2.wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2)
  pre_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    IsQueryBoundP (wotsPhase2OG ds optRand gspec F tbl hist root pk
      fun x ↦ Resources2.wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2) (fun t ↦ kindG t = .hash) c.preP2
  wtcr_phase2 : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    liftG ds (G := gspec)
        ((rTcrTG ds optRand pkSeedDist F).forge ((tbl, hist, root), hist2) pk) =
      wrapS ds (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2OG ds optRand gspec F tbl hist root pk
          fun x ↦ Resources2.wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2)
  wtcr_phase2_hashes : ∀ {ι : Type} (gspec : OracleSpec ι) (tbl : SecretTable vp prims)
      (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed),
    IsQueryBoundP (wotsPhase2OG ds optRand gspec F tbl hist root pk
      fun x ↦ Resources2.wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2) (fun t ↦ kindG t = .hash)
      c.wtcrP2

/-- **The resource theorem for the general-spec adversaries.** -/
theorem final_resourcesG (hS : Structural vp prims) (F : GFam ds vp prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs) :
    FinalResourcesG ds optRand pkSeedDist F qs (Resources2.directCounts vp qs)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp +
        (1 + Resources2.verifyHashes vp * 2)) where
  phase1 := (phase1_resourcesG_dummy ds optRand pkSeedDist hS qs).1
  phase1_eq := phase1Eq ds F dummyForger
  prf := bPrfCG_queryBound ds optRand pkSeedDist F qs hF
  prfSuf := bPrfWCG_queryBound ds optRand pkSeedDist sufCheck F qs hF
  msg := lazyRunG_gameBound ds _ _ qs
    ((msgOpenG_kindBound ds optRand pkSeedDist .game (by decide) F qs hF).mono (openB_game qs))
  msg_interp := lazyRunG_eq_interp ds _ _
  msg_draws := lazyResG_kindBound ds .sec (by decide) _ _
    ((msgOpenG_kindBound ds optRand pkSeedDist .sec (by decide) F qs hF).mono (openB_sec qs))
  msg_hashes := lazyResG_kindBound ds .hash (by decide) _ _
    ((msgOpenG_kindBound ds optRand pkSeedDist .hash (by decide) F qs hF).mono (openB_hash qs))
  msgSuf := lazyRunG_gameBound ds _ _ qs
    ((msgOpenWG_kindBound ds optRand pkSeedDist sufCheck .game (by decide) F qs hF).mono
      (openB_game qs))
  msgSuf_interp := lazyRunG_eq_interp ds _ _
  msgSuf_draws := lazyResG_kindBound ds .sec (by decide) _ _
    ((msgOpenWG_kindBound ds optRand pkSeedDist sufCheck .sec (by decide) F qs hF).mono
      (openB_sec qs))
  msgSuf_hashes := lazyResG_kindBound ds .hash (by decide) _ _
    ((msgOpenWG_kindBound ds optRand pkSeedDist sufCheck .hash (by decide) F qs hF).mono
      (openB_hash qs))
  itsr := lazyRunG_gameBound ds _ _ qs
    ((itsrOpenG_kindBound ds optRand pkSeedDist .game (by decide) F qs hF).mono (openB_game qs))
  itsr_interp := lazyRunG_eq_interp ds _ _
  itsr_draws := lazyResG_kindBound ds .sec (by decide) _ _
    ((itsrOpenG_kindBound ds optRand pkSeedDist .sec (by decide) F qs hF).mono (openB_sec qs))
  itsr_hashes := lazyResG_kindBound ds .hash (by decide) _ _
    ((itsrOpenG_kindBound ds optRand pkSeedDist .hash (by decide) F qs hF).mono (openB_hash qs))
  fors_tcr_phase2 := fun tbl tg ys pk ↦ toTcrG_forge_full ds F tbl tg ys pk
  fors_dspr_phase2 := fun tbl tg ys pk ↦ toDsprG_guess_full ds F tbl tg ys pk
  fors_phase2_hashes := fun pk ys ↦
    findOpenFullG_hashes (pkSeedDist := pkSeedDist) ds F qs hF pk ys
  fors_phase2_openings := fun pk ys ↦
    findOpenFullG_openings (pkSeedDist := pkSeedDist) ds F qs hF pk ys
  memo_phase2 := fun gspec n tbl L pk ↦ bTcrArMG_forge_open ds gspec n F tbl L pk
  memo_phase2_hashes := fun gspec L pk ↦
    memoForgeOpenG_hashes (pkSeedDist := pkSeedDist) ds gspec F qs hF L pk
  ud_phase2 := fun gspec tbl hist hist2 root pk ↦ rUdG_phase2 ds gspec F tbl hist hist2 root pk
  ud_phase2_hashes := fun gspec tbl hist hist2 root pk ↦
    rUdG_phase2_hashes (pkSeedDist := pkSeedDist) ds gspec F qs hF tbl hist hist2 root pk
  pre_phase2 := fun gspec tbl hist hist2 root pk ↦ rPreG_phase2 ds gspec F tbl hist hist2 root pk
  pre_phase2_hashes := fun gspec tbl hist hist2 root pk ↦
    rPreG_phase2_hashes (pkSeedDist := pkSeedDist) ds gspec F qs hF tbl hist hist2 root pk
  wtcr_phase2 := fun gspec tbl hist hist2 root pk ↦
    rTcrTG_phase2 ds gspec F tbl hist hist2 root pk
  wtcr_phase2_hashes := fun gspec tbl hist hist2 root pk ↦
    rTcrTG_phase2_hashes (pkSeedDist := pkSeedDist) ds gspec F qs hF tbl hist hist2 root pk

/-! ## Wrapped forgers -/

variable {optRand pkSeedDist} in
/-- Resources for an external (pure-interface) general-spec forger: `toInternalG A` makes at most
`qs` signing queries and the bundle holds for it. -/
theorem final_resourcesG_external (hS : Structural vp prims)
    (A : GExtForger ds vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) :
    FinalResourcesG ds optRand pkSeedDist (toInternalG ds A).main qs
      (Resources2.directCounts vp qs)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp +
        (1 + Resources2.verifyHashes vp * 2)) :=
  final_resourcesG ds optRand pkSeedDist hS _ qs (toInternalG_queryBound ds A qs hA)

variable {optRand pkSeedDist} in
/-- Resources for a byte-level internal-interface general-spec forger. -/
theorem final_resourcesG_bytes {codec : CoreWireCodec vp.params prims.core}
    (hS : Structural vp prims)
    (A : GBytesForger ds vp prims codec optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) :
    FinalResourcesG ds optRand pkSeedDist (bytesToTypedG ds A).main qs
      (Resources2.directCounts vp qs)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp +
        (1 + Resources2.verifyHashes vp * 2)) :=
  final_resourcesG ds optRand pkSeedDist hS _ qs (bytesToTypedG_queryBound ds A qs hA)

variable {optRand pkSeedDist} in
/-- Resources for a byte-level external (pure-interface) general-spec forger. -/
theorem final_resourcesG_pureBytes {codec : CoreWireCodec vp.params prims.core}
    (hS : Structural vp prims)
    (A : GPureBytesForger ds vp prims codec optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i ↦ i.isRight = true) qs) :
    FinalResourcesG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main qs
      (Resources2.directCounts vp qs)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp +
        (1 + Resources2.verifyHashes vp * 2)) :=
  final_resourcesG ds optRand pkSeedDist hS _ qs
    (toInternalG_pureBytesToTypedG_queryBound ds A qs hA)

end Reduction.Gen

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction.Gen

/-- **Resources of the general-spec adversaries at SLH-DSA-SHA2-128s, as numerals**
(`Resources2.directCounts128s qs`; class adversaries `≤ 269824 + qs·2007385 + 7857` own hash
evaluations after the seed reveal). -/
theorem final_resourcesG_128s {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)]
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (F : GFam ds Link.vp Link.prims) (qs : ℕ)
    (hF : ∀ pk, IsQueryBoundP (F pk) (fun i ↦ i.isRight = true) qs) :
    FinalResourcesG ds optRand pkSeedDist F qs (Resources2.directCounts128s qs)
      (269824 + qs * 2007385 + 7857) := by
  have h := final_resourcesG ds optRand pkSeedDist structural_128s F qs hF
  rw [Resources2.directCounts_128s, keygenHashes_128s, signHashes_128s,
    Resources2.verifyHashes_128s] at h
  exact h

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms final_resourcesG
#print axioms final_resourcesG_external
#print axioms final_resourcesG_bytes
#print axioms final_resourcesG_pureBytes
#print axioms final_resourcesG_128s
#print axioms phase1_resourcesG
#print axioms phase1_resourcesG_dummy
end Axioms
