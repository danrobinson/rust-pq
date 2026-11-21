import Reduction.Final
import Reduction.SufCollision
import Reduction.SufHopPrf
import Reduction.SufHopMsg

/-!
# Strong unforgeability (SUF-CMA) of SLH-DSA in the standard model

A strong forgery is a valid pair `(M, σ*)` that the signing oracle never returned (VCVio's
`SignatureAlg.strongUnforgeableExperiment`).  **Result** (`slhdsa_suf_cma`): for every strong
forger `S` against `internalAlg vp prims optRand pkSeedDist`,

`Adv^{SUF-CMA}(S) ≤ bound (bPrfW sufCheck A) (bPrfMsgW sufCheck A) (bItsr A) (bOpenPre A) (bTcr A)
    (rUd (bWots A)) (rPre (bWots A)) (rTcr (bWots A))`,   `A := S.toUnforgeableAdversary`,

i.e. the *same eight assumption terms* as the EUF-CMA theorem `slhdsa_euf_cma`, with the *same*
six adversaries after the PRF hops; only the two PRF distinguishers output the strong-forgery bit
instead of the EUF-CMA bit.  No extra assumption and no extra target is needed.

Why.  In game `G2` (secrets from a uniform table, lazily sampled randomizer) every answer of the
signing oracle on `(M, R)` is the *reference signature* `idealSign tbl M pk R`, so a strong
forgery is of one of two kinds:

* **fresh randomizer** — `(M, σ*.R)` is not a signed `(message, randomizer)` pair.  This is all
  the EUF-CMA case analysis ever uses about freshness (the ITSR game is pair-based):
  `g2Fresh_le`.
* **same randomizer** — `(M, σ*.R)` was signed and `σ* ≠ idealSign tbl M pk σ*.R`.  Two different
  signatures with the same randomizer verify to the same root, so
  (`Reduction.sameRandomizer_collision`, deterministic) either some layer WOTS+-signs different
  messages with the same chain ends — the WOTS+ event `evWots` — or two verification hash calls
  at the same tweak on different inputs collide; the reference signature's calls are all targets
  of `bTcr` (`verifyCalls_idealSign_subset`: its targets are *all* hash calls of the key
  structure, including `F` at every FORS leaf secret and at every WOTS+ chain position), so this
  is the event `evColl` in which `bTcr` wins.

The transfer from the real scheme to `G2` is `stepPRFW`/`stepPRFmsgW` (`Reduction.SufHopPrf`,
`Reduction.SufHopMsg`): the two PRF hops for an arbitrary final check on the returned signatures.

Modular forms: `suf_le_prf_add_g2` (hops only; any bound on `Pr[g2W sufCheck A]` can be plugged
in) and `slhdsa_suf_cma_of_euf` (any EUF-CMA bound `∀ B, Adv B ≤ β B` plus the same-message
residual `slhdsa_sameMessage_le`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## `G2` with an arbitrary winning predicate -/

/-- A sample of the forger's run in `G2`: the forgery and the transcript. -/
abbrev G2Out (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  (List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims

/-- Game `G2` with the final check replaced by `win`, a function of the seed, the table, the
forgery and the transcript.  `g2With A g2ValidWin` is `g2 A` (`g2With_g2Valid`). -/
noncomputable def g2With (A : Forger vp prims optRand pkSeedDist)
    (win : prims.PkSeed → SecretTable vp prims → G2Out vp prims → Bool) : ProbComp Bool :=
  pkSeedDist >>= fun pkSeed => sampleTable vp prims >>= fun tbl =>
    g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z => pure (win pkSeed tbl z)

/-- The reference signature of a forgery: the honest signature on the forged message under the
forgery's own randomizer. -/
def refSig (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) :
    GeneralScheme.SignatureCore vp prims.core :=
  idealSign vp prims tbl z.1.1 (idealPk vp prims tbl pkSeed) z.1.2.randomness

/-- The forgery verifies. -/
def verifies (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) : Bool :=
  GeneralScheme.verifyInternal vp prims z.1.1 z.1.2 (idealPk vp prims tbl pkSeed)

/-- The forged `(message, randomizer)` pair was not signed. -/
def pairFresh (z : G2Out vp prims) : Bool :=
  decide ((z.1.1, z.1.2.randomness) ∉ G2Log.signed z.2)

/-- The EUF-CMA check of `G2`. -/
def g2ValidWin (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) : Bool :=
  g2Valid (idealPk vp prims tbl pkSeed) z.2 z.1.1 z.1.2

/-- **Fresh-randomizer forgery**: valid, and the `(message, randomizer)` pair was not signed.
Every EUF-CMA forgery is one (`g2ValidWin_le_freshWin`). -/
def freshWin (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) : Bool :=
  pairFresh z && verifies pkSeed tbl z

/-- The `(message, signature)` pairs the signing oracle of `G2` returned along a transcript:
`g2SignOracle` answers the query `M` with `idealSign tbl M pk R` and records `(M, opt_rand, R)`. -/
def g2Returned (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (log : G2Log prims) :
    List (List Byte × GeneralScheme.SignatureCore vp prims.core) :=
  log.map fun e => (e.1, idealSign vp prims tbl e.1 (idealPk vp prims tbl pkSeed) e.2.2)

open scoped Classical in
/-- **Strong forgery in `G2`**: valid, and the pair was never returned by the signing oracle. -/
noncomputable def sufWin (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims)
    (z : G2Out vp prims) : Bool :=
  decide (z.1 ∉ g2Returned pkSeed tbl z.2) && verifies pkSeed tbl z

open scoped Classical in
/-- **Same-randomizer residual**: valid, the `(message, randomizer)` pair *was* signed, and the
forged signature differs from the reference signature (which is what the oracle returned for
that pair). -/
noncomputable def sameWin (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims)
    (z : G2Out vp prims) : Bool :=
  !pairFresh z && decide (z.1.2 ≠ refSig pkSeed tbl z) && verifies pkSeed tbl z

/-! ## The four chargeable events -/

/-- ITSR event: pair-fresh and every opened FORS leaf was opened by a signing query. -/
def evItsr (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) : Bool :=
  pairFresh z &&
    decide (g2ClassOf tbl (idealPk vp prims tbl pkSeed) z.2 z.1.1 z.1.2 = .itsr)

/-- Open-preimage event (no validity or freshness condition is needed). -/
def evOpen (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) : Bool :=
  decide (g2ClassOf tbl (idealPk vp prims tbl pkSeed) z.2 z.1.1 z.1.2 = .openpre)

/-- WOTS+ event: valid, and at some layer the forgery and the reference signature sign different
messages and recover the same chain ends (no freshness condition). -/
def evWots (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) : Bool :=
  verifies pkSeed tbl z &&
    (wotsLayer? (idealPk vp prims tbl pkSeed)
      (digestParts (idealPk vp prims tbl pkSeed) z.1.2.randomness z.1.1) z.1.2
      (refSig pkSeed tbl z)).isSome

/-- Collision event: verification of the forgery makes a hash call that collides with a call of
the honest structure — exactly the event in which `bTcr` wins. -/
noncomputable def evColl (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) : Bool :=
  (findCollision pkSeed (honestCalls tbl pkSeed)
    (verifyCalls (idealPk vp prims tbl pkSeed) z.1.1 z.1.2)).isSome

/-! ## Bookkeeping -/

theorem g2With_mono (A : Forger vp prims optRand pkSeedDist)
    (p q : prims.PkSeed → SecretTable vp prims → G2Out vp prims → Bool)
    (h : ∀ pkSeed tbl z, p pkSeed tbl z = true → q pkSeed tbl z = true) :
    prTrue (g2With A p) ≤ prTrue (g2With A q) :=
  prTrue_bind_mono _ _ _ fun pkSeed _ => prTrue_bind_mono _ _ _ fun tbl _ =>
    prTrue_bind_pure_mono _ _ _ fun z _ => h pkSeed tbl z

theorem g2With_le_add (A : Forger vp prims optRand pkSeedDist)
    (p q r : prims.PkSeed → SecretTable vp prims → G2Out vp prims → Bool)
    (h : ∀ pkSeed tbl z, p pkSeed tbl z = true → q pkSeed tbl z = true ∨ r pkSeed tbl z = true) :
    prTrue (g2With A p) ≤ prTrue (g2With A q) + prTrue (g2With A r) :=
  prTrue_bind_le_add _ _ _ _ fun pkSeed _ => prTrue_bind_le_add _ _ _ _ fun tbl _ =>
    prTrue_bind_pure_le_add _ _ _ _ fun z _ => h pkSeed tbl z

/-- `g2With` at the EUF-CMA check is `G2`. -/
theorem g2With_g2Valid (A : Forger vp prims optRand pkSeedDist) :
    g2With A g2ValidWin = g2 A := rfl

/-- An EUF-CMA forgery is a fresh-randomizer forgery. -/
theorem g2ValidWin_le_freshWin (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims)
    (z : G2Out vp prims) (h : g2ValidWin pkSeed tbl z = true) : freshWin pkSeed tbl z = true := by
  unfold g2ValidWin g2Valid at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold freshWin pairFresh verifies
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun hmem => h.1 ?_, h.2⟩
  unfold G2Log.signed at hmem
  obtain ⟨e, he, heq⟩ := List.mem_map.1 hmem
  exact List.mem_map.2 ⟨e, he, congrArg Prod.fst heq⟩

/-- `Pr[G2] ≤ Pr[G2 with the fresh-randomizer check]`. -/
theorem g2_le_g2Fresh (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2 A) ≤ prTrue (g2With A freshWin) := by
  rw [← g2With_g2Valid]
  exact g2With_mono A _ _ g2ValidWin_le_freshWin

/-! ## Branch bounds, without message freshness -/

/-- A pair-fresh forgery of class `itsr` wins ITSR (the game's freshness condition is on the
`(randomizer, input)` pair). -/
theorem wins_of_itsr_pair (pk : PublicKeyCore prims.core) (log : G2Log prims) (msg : List Byte)
    (sig ref : GeneralScheme.SignatureCore vp prims.core)
    (hcov : LogCovered pk.pkSeed pk.pkRoot log)
    (hfresh : (msg, sig.randomness) ∉ G2Log.signed log)
    (hc : classify pk (G2Log.signed log) msg sig ref = .itsr) :
    (itsrProblem vp prims).Wins (targetsOf pk.pkSeed pk.pkRoot log)
      (sig.randomness, (pk.pkSeed, pk.pkRoot, msg)) := by
  refine ⟨fun hmem => ?_, fun i hi => ?_⟩
  · obtain ⟨e, he, heq⟩ := mem_targetsOf _ _ _ _ hmem
    have h1 : msg = e.1 := congrArg (fun x => x.2.2.2) heq
    have h2 : sig.randomness = e.2.2 := congrArg (fun x => x.1) heq
    refine hfresh ?_
    unfold G2Log.signed
    exact List.mem_map.2 ⟨e, he, by rw [h1, h2]⟩
  · have h := classify_itsr pk _ msg sig ref hc i hi
    unfold openedLeaves G2Log.signed at h
    rw [List.mem_flatMap] at h
    obtain ⟨e', he', hi'⟩ := h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    exact List.mem_flatMap.2 ⟨_, hcov e he, hi'⟩

/-- **ITSR branch, pair-fresh form.** -/
theorem br_itsr (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2With A evItsr) ≤ KeyedHash.ITSRAdvantage (bItsr A) := by
  have hR : KeyedHash.ITSRExperiment (bItsr A) = g2Joint A >>= fun w =>
      pure (decide ((itsrProblem vp prims).Wins
        (targetsOf w.1 (idealPk vp prims w.2.1 w.1).pkRoot w.2.2.2)
        (w.2.2.1.2.randomness, (w.1, (idealPk vp prims w.2.1 w.1).pkRoot, w.2.2.1.1)))) := by
    simp [KeyedHash.ITSRExperiment, bItsr_run, g2Joint]
  have hL : g2With A evItsr = g2Joint A >>= fun w => pure (evItsr w.1 w.2.1 w.2.2) := by
    simp [g2With, g2Joint]
  rw [KeyedHash.ITSRAdvantage_eq_evalDist_experiment, hR, hL]
  change prTrue _ ≤ prTrue _
  rw [prTrue_bind_pure, prTrue_bind_pure]
  refine prEvent_mono_of_support _ _ _ fun w hw h => ?_
  unfold evItsr pairFresh at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact wins_of_itsr_pair (idealPk vp prims w.2.1 w.1) w.2.2.2 w.2.2.1.1 w.2.2.1.2 _
    (g2Joint_covered A w hw) h.1 h.2

/-- Open-preimage branch over an abstract table sampler (as `op_main`, without validity). -/
theorem br_open_main (hS : Structural vp prims) (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist)
    (hmy : ∀ f : SecretTable vp prims → ProbComp Bool,
      prTrue (my >>= fun tbl => Tables.sampleList prims.Y (forsSkIdx vp).length >>= fun xs =>
        f (Tables.updateList tbl (forsSkIdx vp) xs)) = prTrue (my >>= f)) :
    prTrue (pkSeedDist >>= fun pkSeed => my >>= fun tbl =>
      g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z => pure (evOpen pkSeed tbl z)) ≤
      prTrue (TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.experiment (bOpenPreWith my A)) := by
  rw [op_experiment hS my A]
  refine le_trans (prTrue_bind_mono _ _ _ fun pkSeed _ => prTrue_bind_mono my _ _ fun tbl _ =>
    prTrue_bind_pure_mono _ _ (opW pkSeed tbl) fun z _ h =>
      op_win hS pkSeed tbl z (of_decide_eq_true h)) ?_
  refine le_of_eq (prTrue_bind_congr _ _ _ fun pkSeed _ => ?_)
  refine (hmy (fun T => g2Run A T (idealPk vp prims T pkSeed) >>= fun z =>
    pure (opW pkSeed T z))).symm.trans ?_
  refine prTrue_bind_congr my _ _ fun tbl _ => prTrue_bind_congr _ _ _ fun xs hxs => ?_
  rw [op_tail hS my A pkSeed tbl xs (Tables.length_of_mem_support_sampleList hxs)]

/-- **Open-preimage branch, without validity or freshness.** -/
theorem br_open (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2With A evOpen) ≤
      TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre A) :=
  br_open_main hS (sampleTable vp prims) A (fun f =>
    prTrue_congr (evalDist_sampleTable_extract_list (forsSkIdx_nodup hS) (fun _ => f)))

/-- **Collision branch**: whenever verification of the forger's output collides with an honest
call, `bTcr` wins.  No validity, freshness or class condition. -/
theorem br_coll (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2With A evColl) ≤ TweakableHash.SM_DT_TCR_Advantage (bTcr A) := by
  unfold TweakableHash.SM_DT_TCR_Advantage prTrue
  rw [tcrExperiment_bTcr hS A, g2With]
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pkSeed => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun tbl => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
  obtain ⟨⟨msg, sig⟩, log⟩ := r
  unfold evColl
  dsimp only
  by_cases hv : (findCollision pkSeed (honestCalls tbl pkSeed)
      (verifyCalls (idealPk vp prims tbl pkSeed) msg sig)).isSome = true
  · obtain ⟨⟨j, m⟩, hjm⟩ := Option.isSome_iff_exists.mp hv
    obtain ⟨t, ht, hne, heq⟩ := findCollision_sound _ _ _ j m hjm
    rw [hjm]
    simp only [Option.getD_some, ht]
    simp [hne, heq]
  · rw [Bool.not_eq_true] at hv
    rw [hv]
    simp

/-- Against the empty transcript, a forgery whose comparison with `ref` has a WOTS+ layer is of
class `wots` (no FORS leaf is opened, and there are `k > 0` of them). -/
theorem classify_nil_wots (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig ref : GeneralScheme.SignatureCore vp prims.core)
    (h : (wotsLayer? pk (digestParts pk sig.randomness msg) sig ref).isSome = true) :
    classify pk [] msg sig ref = .wots := by
  have h1 : ¬ ∀ x ∈ forsIndices vp (digestParts pk sig.randomness msg),
      x ∈ openedLeaves pk ([] : List (List Byte × prims.Y)) := by
    intro hall
    have hmem := hall _ (List.mem_map.2 ⟨0, List.mem_range.2 vp.valid.k_pos, rfl⟩)
    simp [openedLeaves] at hmem
  unfold classify
  dsimp only
  simp only [h1, h, ↓reduceIte]

/-- WOTS+ branch, deterministic half (as `table_step`, without freshness). -/
theorem wots_table_step (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pk : prims.PkSeed) (tbl : SecretTable vp prims) :
    prTrue (g2Run A tbl (idealPk vp prims tbl pk) >>= fun z => pure (evWots pk tbl z)) ≤
      prTrue (simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
        (qGame A pk tbl)) := by
  rw [simulateQ_qGame A pk tbl _ (fun _ => rfl) (fun ob => Tables.simulateQ_fnImpl_liftM _ ob)]
  obtain ⟨hist, hrun, hg⟩ := chooseBody_run hS tbl pk
  change _ ≤ prTrue ((simulateQ (tblOracles tbl pk) ((chooseBody tbl).run [])).run [] >>=
    finish A pk tbl)
  rw [hrun, pure_bind, finish]
  have hsign : signFromHist tbl hist (idealPk vp prims tbl pk) =
      fun m R => idealSign vp prims tbl m (idealPk vp prims tbl pk) R :=
    funext fun m => funext fun R => signFromHist_eq_idealSign hS tbl hist _ hg m R
  change _ ≤ prTrue (g2RunWith A (idealPk vp prims tbl pk)
    (signFromHist tbl hist (idealPk vp prims tbl pk)) >>= fun z => pure (WotsGame.win pk hist
      (wotsAnswer tbl hist (idealPk vp prims tbl pk) z.1.1 z.1.2).1
      (wotsAnswer tbl hist (idealPk vp prims tbl pk) z.1.1 z.1.2).2.1
      (wotsAnswer tbl hist (idealPk vp prims tbl pk) z.1.1 z.1.2).2.2))
  rw [hsign]
  refine prTrue_bind_pure_mono _ _ _ fun z _ hz => ?_
  unfold evWots verifies refSig at hz
  rw [Bool.and_eq_true] at hz
  refine wotsAnswer_wins hS tbl hist (idealPk vp prims tbl pk) [] z.1.1 z.1.2 hg ?_ ?_
  · unfold g2Valid
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true (by simp), hz.1⟩
  · exact classify_nil_wots _ _ _ _ hz.2

/-- **WOTS+ branch, without freshness.** -/
theorem br_wots (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2With A evWots) ≤ prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) 0 (bWots A)) := by
  rw [hyb_bWots_eq]
  calc prTrue (g2With A evWots)
      ≤ prTrue (pkSeedDist >>= fun pk => sampleTable vp prims >>= fun tbl =>
          simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
            (qGame A pk tbl)) :=
        prTrue_bind_bind_mono pkSeedDist (sampleTable vp prims) _ _ (wots_table_step hS A)
    _ = _ := prTrue_bind_congr _ _ _ fun pk _ => prTrue_congr (fresh_eq_table hS A pk).symm

/-! ## The `G2`-level bound -/

/-- The six terms of `bound` that remain after the two PRF hops, at the adversaries of `A`. -/
noncomputable def g2Bound (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  KeyedHash.ITSRAdvantage (bItsr A) +
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre A) +
    TweakableHash.SM_DT_TCR_Advantage (bTcr A) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
      TweakableHash.SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
    TweakableHash.SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
    TweakableHash.SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A))

/-- `bound` is the two PRF terms plus `g2Bound`. -/
theorem bound_eq_prf_add_g2Bound (A : Forger vp prims optRand pkSeedDist) :
    bound pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A)) =
      (skPrf vp prims).prfAdvantage (bPrf A) + (msgPrf vp prims).prfAdvantage (bPrfMsg A) +
        g2Bound A := by
  unfold bound g2Bound
  ring

/-- **Union bound over the four chargeable events.**  Any winning predicate of `G2` that implies
one of `evItsr`, `evOpen`, `evWots`, `evColl` is bounded by `g2Bound A`, with the reduction
adversaries of the EUF-CMA proof. -/
theorem g2With_le_g2Bound (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (win : prims.PkSeed → SecretTable vp prims → G2Out vp prims → Bool)
    (hwin : ∀ pkSeed tbl z, win pkSeed tbl z = true →
      evItsr pkSeed tbl z = true ∨ evOpen pkSeed tbl z = true ∨
        evColl pkSeed tbl z = true ∨ evWots pkSeed tbl z = true) :
    prTrue (g2With A win) ≤ g2Bound A := by
  have h1 := g2With_le_add A win evItsr
    (fun pkSeed tbl z => evOpen pkSeed tbl z || (evColl pkSeed tbl z || evWots pkSeed tbl z))
    (fun pkSeed tbl z h => by
      rcases hwin pkSeed tbl z h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h]; rfl)
      · exact Or.inr (by rw [h]; simp)
      · exact Or.inr (by rw [h]; simp))
  have h2 := g2With_le_add A
    (fun pkSeed tbl z => evOpen pkSeed tbl z || (evColl pkSeed tbl z || evWots pkSeed tbl z))
    evOpen (fun pkSeed tbl z => evColl pkSeed tbl z || evWots pkSeed tbl z)
    (fun pkSeed tbl z h => by simpa [Bool.or_eq_true] using h)
  have h3 := g2With_le_add A
    (fun pkSeed tbl z => evColl pkSeed tbl z || evWots pkSeed tbl z) evColl evWots
    (fun pkSeed tbl z h => by simpa [Bool.or_eq_true] using h)
  have hud := stepWotsUD hS pkSeedDist (bWots A)
  have hfin := stepWotsFinal hS pkSeedDist (bWots A)
  unfold StepWotsUD at hud
  unfold StepWotsFinal at hfin
  have hw := (br_wots hS A).trans (hud.trans (add_le_add_left hfin _))
  unfold g2Bound
  calc prTrue (g2With A win)
      ≤ prTrue (g2With A evItsr) + (prTrue (g2With A evOpen) +
          (prTrue (g2With A evColl) + prTrue (g2With A evWots))) :=
        h1.trans (add_le_add_right (h2.trans (add_le_add_right h3 _)) _)
    _ ≤ KeyedHash.ITSRAdvantage (bItsr A) +
          (TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre A) +
          (TweakableHash.SM_DT_TCR_Advantage (bTcr A) +
          (TweakableHash.SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
              TweakableHash.SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A)) +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
              TweakableHash.SM_DT_UD_Advantage (rUd pkSeedDist (bWots A))))) :=
        add_le_add (br_itsr A) (add_le_add (br_open hS A) (add_le_add (br_coll hS A) hw))
    _ = _ := by ring

/-! ## The fresh-randomizer half (proved) -/

/-- A collision between the verification calls of the forgery and of the reference signature is
a collision with the honest structure. -/
theorem evColl_of_coll (hS : Structural vp prims) (pkSeed : prims.PkSeed)
    (tbl : SecretTable vp prims) (z : G2Out vp prims)
    (h : col_Coll pkSeed (verifyCalls (idealPk vp prims tbl pkSeed) z.1.1 z.1.2)
      (verifyCalls (idealPk vp prims tbl pkSeed) z.1.1 (refSig pkSeed tbl z))) :
    evColl pkSeed tbl z = true := by
  obtain ⟨c, hc, c', hc', hkey, hne, hcol⟩ := h
  have hmem := verifyCalls_idealSign_subset hS tbl pkSeed z.1.1 z.1.2.randomness c' hc'
  unfold evColl findCollision
  rw [List.findSome?_isSome_iff]
  refine ⟨c, hc, ?_⟩
  have hlt : (honestCalls tbl pkSeed).findIdx (fun t =>
      decide (t.1 = c.1 ∧ c.2 ≠ t.2 ∧ prims.Thash pkSeed c.1 c.2 = prims.Thash pkSeed t.1 t.2)) <
      (honestCalls tbl pkSeed).length :=
    List.findIdx_lt_length_of_exists ⟨c', hmem, decide_eq_true ⟨hkey.symm, hne, hcol⟩⟩
  simp only [hlt, ↓reduceIte]
  rfl

/-- Every fresh-randomizer forgery falls into one of the four chargeable events. -/
theorem freshWin_cases (hS : Structural vp prims) (pkSeed : prims.PkSeed)
    (tbl : SecretTable vp prims) (z : G2Out vp prims) (h : freshWin pkSeed tbl z = true) :
    evItsr pkSeed tbl z = true ∨ evOpen pkSeed tbl z = true ∨
      evColl pkSeed tbl z = true ∨ evWots pkSeed tbl z = true := by
  unfold freshWin at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hf, hv⟩ := h
  cases hc : g2ClassOf tbl (idealPk vp prims tbl pkSeed) z.2 z.1.1 z.1.2 with
  | itsr =>
    left
    unfold evItsr
    rw [hf, hc]
    rfl
  | openpre =>
    right; left
    unfold evOpen
    rw [hc]
    rfl
  | wots =>
    right; right; right
    unfold evWots
    rw [hv, Bool.true_and]
    unfold g2ClassOf classify at hc
    dsimp only at hc
    split_ifs at hc with h1 h2 h3
    exact h2
  | tcr =>
    right; right; left
    refine evColl_of_coll hS pkSeed tbl z ?_
    have hR := col_idealSign_randomness tbl pkSeed z.1.1 z.1.2.randomness
    have hv' := col_verifyInternal_idealSign hS tbl pkSeed z.1.1 z.1.2.randomness
    unfold verifies at hv
    rw [GeneralScheme.verifyInternal_eq_decide] at hv hv'
    have h1 := of_decide_eq_true hv
    have h2 := of_decide_eq_true hv'
    rw [hR] at h2
    exact col_collision_of_classify (idealPk vp prims tbl pkSeed) (G2Log.signed z.2) z.1.1 z.1.2
      (idealSign vp prims tbl z.1.1 (idealPk vp prims tbl pkSeed) z.1.2.randomness) hR
      (h1.trans h2.symm) hc

/-- **Fresh-randomizer forgeries in `G2` (proved, unconditional).**  The probability that the
forger outputs a valid signature whose `(message, randomizer)` pair was never signed — this
includes every forgery on a new message *and* every forgery on a signed message under a
randomizer different from all those used for it — is bounded by the six `G2`-terms of the
EUF-CMA bound, with the same reduction adversaries. -/
theorem g2Fresh_le (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2With A freshWin) ≤ g2Bound A :=
  g2With_le_g2Bound hS A freshWin (freshWin_cases hS)

/-! ## The split of a strong forgery in `G2` (proved) -/

/-- A strong forgery is a fresh-randomizer forgery or a same-randomizer residual. -/
theorem sufWin_cases (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims)
    (h : sufWin pkSeed tbl z = true) :
    freshWin pkSeed tbl z = true ∨ sameWin pkSeed tbl z = true := by
  classical
  unfold sufWin at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hnew, hv⟩ := h
  by_cases hf : pairFresh z = true
  · left
    unfold freshWin
    rw [hf, hv]
    rfl
  · right
    unfold sameWin
    rw [Bool.not_eq_true] at hf
    rw [hf, hv, Bool.and_true, Bool.not_false, Bool.true_and, decide_eq_true_eq]
    intro heq
    unfold pairFresh at hf
    have hmem : (z.1.1, z.1.2.randomness) ∈ G2Log.signed z.2 := by
      by_contra hcon
      rw [decide_eq_true hcon] at hf
      exact Bool.noConfusion hf
    unfold G2Log.signed at hmem
    obtain ⟨e, he, hpair⟩ := List.mem_map.1 hmem
    have he1 : e.1 = z.1.1 := congrArg Prod.fst hpair
    have he2 : e.2.2 = z.1.2.randomness := congrArg Prod.snd hpair
    refine hnew ?_
    unfold g2Returned
    refine List.mem_map.2 ⟨e, he, ?_⟩
    rw [he1, he2]
    exact Prod.ext rfl heq.symm

/-- **`G2`: strong forgery ≤ fresh-randomizer forgery + same-randomizer residual (proved).** -/
theorem g2Suf_le_fresh_add_same (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2With A sufWin) ≤ prTrue (g2With A freshWin) + prTrue (g2With A sameWin) :=
  g2With_le_add A _ _ _ sufWin_cases

/-- Corollary of `g2Fresh_le` (proved): only the same-randomizer residual is left unbounded. -/
theorem g2Suf_le_g2Bound_add_same (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2With A sufWin) ≤ g2Bound A + prTrue (g2With A sameWin) :=
  (g2Suf_le_fresh_add_same A).trans (add_le_add_left (g2Fresh_le hS A) _)

/-! ## The same-randomizer residual -/

/-- The deterministic two-signature statement (proved: `sameRandomizerCollision_holds`).  Two
*different* signatures with the same randomizer that both verify for the same message under the
same public key either sign different messages with the same recovered chain ends at some WOTS+
layer, or make two verification hash calls at the same tweak on different inputs with the same
output. -/
def SameRandomizerCollision (vp : ValidatedParams) (prims : Primitives vp.params)
    [DecidableEq prims.Y] : Prop :=
  ∀ (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig ref : GeneralScheme.SignatureCore vp prims.core),
    ref.randomness = sig.randomness → sig ≠ ref →
    GeneralScheme.verifyInternal vp prims msg sig pk = true →
    GeneralScheme.verifyInternal vp prims msg ref pk = true →
    (wotsLayer? pk (digestParts pk sig.randomness msg) sig ref).isSome = true ∨
      col_Coll pk.pkSeed (verifyCalls pk msg sig) (verifyCalls pk msg ref)

/-- `SameRandomizerCollision` holds (`Reduction.SufCollision`). -/
theorem sameRandomizerCollision_holds : SameRandomizerCollision vp prims :=
  fun pk msg sig ref hR hne hv hv' => sameRandomizer_collision pk msg sig ref hR hne hv hv'

/-- A same-randomizer residual is a WOTS+ or a collision event. -/
theorem sameWin_cases (hS : Structural vp prims)
    (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims)
    (h : sameWin pkSeed tbl z = true) :
    evItsr pkSeed tbl z = true ∨ evOpen pkSeed tbl z = true ∨
      evColl pkSeed tbl z = true ∨ evWots pkSeed tbl z = true := by
  classical
  unfold sameWin at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, hne⟩, hv⟩ := h
  have hR := col_idealSign_randomness tbl pkSeed z.1.1 z.1.2.randomness
  have hv' := col_verifyInternal_idealSign hS tbl pkSeed z.1.1 z.1.2.randomness
  rcases sameRandomizerCollision_holds (idealPk vp prims tbl pkSeed) z.1.1 z.1.2
    (refSig pkSeed tbl z) hR hne hv hv' with hw | hcoll
  · right; right; right
    unfold evWots
    rw [hv, Bool.true_and]
    exact hw
  · right; right; left
    exact evColl_of_coll hS pkSeed tbl z hcoll

/-- **Strong forgeries in `G2`.**  The strong-forgery event of `G2` is bounded by the six
`G2`-terms of the EUF-CMA bound with the same reduction adversaries (in particular one SM-TCR
term on `Thash` at `bTcr A`, with its existing target set). -/
theorem g2Suf_le (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2With A sufWin) ≤ g2Bound A :=
  g2With_le_g2Bound hS A sufWin fun pkSeed tbl z h =>
    (sufWin_cases pkSeed tbl z h).elim (freshWin_cases hS pkSeed tbl z)
      (sameWin_cases hS pkSeed tbl z)

/-! ## Explicit final checks -/

/-- Decidable equality of FORS tree signatures, from that of nodes (choice-free). -/
def forsTreeDecEq : DecidableEq (ForsTreeSigCore vp.params prims.core) := fun a b =>
  decidable_of_iff (a.sk = b.sk ∧ a.auth = b.auth)
    ⟨fun h => suf_forsTree_ext a b h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- Decidable equality of XMSS signatures, from that of nodes (choice-free). -/
def xmssSigDecEq : DecidableEq (XmssSig vp.params prims.core) := fun a b =>
  decidable_of_iff (a.wots = b.wots ∧ a.auth = b.auth)
    ⟨fun h => suf_xmssSig_ext a b h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- Decidable equality of signatures, from that of nodes (choice-free). -/
def sigDecEq : DecidableEq (GeneralScheme.SignatureCore vp prims.core) := fun a b =>
  letI := forsTreeDecEq (vp := vp) (prims := prims)
  letI := xmssSigDecEq (vp := vp) (prims := prims)
  decidable_of_iff (a.randomness = b.randomness ∧ a.fors = b.fors ∧ a.hypertree = b.hypertree)
    ⟨fun h => suf_sig_ext a b h.1 h.2.1 h.2.2, fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩

/-- The strong-unforgeability check: the pair was never returned, and it verifies. -/
def sufCheck : WinCheck vp prims := fun pk f log =>
  letI := sigDecEq (vp := vp) (prims := prims)
  !SignatureAlg.signingLogContains log f.1 f.2 && GeneralScheme.verifyInternal vp prims f.1 f.2 pk

/-- The same-message check: the message was queried, the pair was never returned, and it
verifies. -/
def sameCheck : WinCheck vp prims := fun pk f log =>
  letI := sigDecEq (vp := vp) (prims := prims)
  log.wasQueried f.1 && !SignatureAlg.signingLogContains log f.1 f.2 &&
    GeneralScheme.verifyInternal vp prims f.1 f.2 pk

theorem sameCheck_sufCheck (pk : PublicKeyCore prims.core)
    (f : List Byte × GeneralScheme.SignatureCore vp prims.core) (log : SigLog vp prims)
    (h : sameCheck pk f log = true) : sufCheck pk f log = true := by
  unfold sameCheck at h
  unfold sufCheck
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  rw [Bool.and_eq_true]
  exact ⟨h.1.2, h.2⟩

/-- The SUF-CMA advantage is the success probability of the chosen-message experiment with final
check `sufCheck`. -/
theorem strongAdvantage_eq_expW
    (S : SignatureAlg.StrongUnforgeableAdversary (realAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S =
      prTrue (expW (realAlg vp prims optRand pkSeedDist) sufCheck S.toUnforgeableAdversary) := by
  have h : SignatureAlg.strongUnforgeableExperiment S =
      expW (realAlg vp prims optRand pkSeedDist) sufCheck S.toUnforgeableAdversary := by
    unfold SignatureAlg.strongUnforgeableExperiment expW sufCheck
    simp [internalAlg, SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary,
      SignatureAlg.signingLogContains]
    refine bind_congr fun pkSeed => bind_congr fun k => bind_congr fun skPrf => ?_
    congr!
  simp [SignatureAlg.strongUnforgeableAdvantage, prTrue, ProbCompRuntime.probComp_evalDist, h]

/-- The same-message advantage is the success probability of the chosen-message experiment with
final check `sameCheck`. -/
theorem sameMessageAdvantage_eq_expW
    (S : SignatureAlg.StrongUnforgeableAdversary (realAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp S =
      prTrue (expW (realAlg vp prims optRand pkSeedDist) sameCheck S.toUnforgeableAdversary) := by
  have h : SignatureAlg.sameMessageStrongUnforgeableExperiment S =
      expW (realAlg vp prims optRand pkSeedDist) sameCheck S.toUnforgeableAdversary := by
    unfold SignatureAlg.sameMessageStrongUnforgeableExperiment expW sameCheck
    simp [internalAlg, SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary,
      SignatureAlg.signingLogContains]
    refine bind_congr fun pkSeed => bind_congr fun k => bind_congr fun skPrf => ?_
    congr!
  simp [SignatureAlg.sameMessageStrongUnforgeableAdvantage, prTrue,
    ProbCompRuntime.probComp_evalDist, h]

/-! ## From the real scheme to `G2` -/

/-- `g2W` is `g2With` at the check read off the transcript. -/
theorem g2W_eq_g2With (w : WinCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    g2W w A = g2With A (fun pkSeed tbl z => w (idealPk vp prims tbl pkSeed) z.1
      (sigLogOf tbl (idealPk vp prims tbl pkSeed) z.2)) := rfl

/-- **Both PRF hops, for any final check** (modular form: no statement about `G2` is used).
`Pr[real game with check w] ≤ Adv^PRF(bPrfW w A) + Adv^PRF_msg(bPrfMsgW w A) + Pr[g2W w A]`. -/
theorem expW_le_prf_add_g2 (hS : Structural vp prims) (w : WinCheck vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prTrue (expW (realAlg vp prims optRand pkSeedDist) w A) ≤
      (skPrf vp prims).prfAdvantage (bPrfW w A) + (msgPrf vp prims).prfAdvantage (bPrfMsgW w A) +
        prTrue (g2W w A) := by
  have h1 := stepPRFW hS w A
  have h2 := stepPRFmsgW w A
  calc prTrue (expW (realAlg vp prims optRand pkSeedDist) w A)
      ≤ (prTrue (g2W w A) + (msgPrf vp prims).prfAdvantage (bPrfMsgW w A)) +
          (skPrf vp prims).prfAdvantage (bPrfW w A) := h1.trans (add_le_add h2 le_rfl)
    _ = _ := by ring

/-- A strong forgery of `G2` in the sense of `sufCheck` is one in the sense of `sufWin`. -/
theorem sufWin_of_sufCheck (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims)
    (z : G2Out vp prims)
    (h : sufCheck (idealPk vp prims tbl pkSeed) z.1
      (sigLogOf tbl (idealPk vp prims tbl pkSeed) z.2) = true) : sufWin pkSeed tbl z = true := by
  classical
  unfold sufCheck at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hnew, hv⟩ := h
  unfold sufWin verifies
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun hmem => ?_, hv⟩
  unfold g2Returned at hmem
  obtain ⟨e, he, heq⟩ := List.mem_map.1 hmem
  unfold SignatureAlg.signingLogContains at hnew
  rw [Bool.not_eq_true', decide_eq_false_iff_not] at hnew
  refine hnew ?_
  unfold sigLogOf
  refine List.mem_map.2 ⟨e, he, ?_⟩
  rw [← heq]

/-- Any final check that implies `sufCheck` is bounded in `G2` by the six `G2`-terms. -/
theorem g2W_le_g2Bound (hS : Structural vp prims) (w : WinCheck vp prims)
    (hw : ∀ pk f log, w pk f log = true → sufCheck pk f log = true)
    (A : Forger vp prims optRand pkSeedDist) : prTrue (g2W w A) ≤ g2Bound A := by
  rw [g2W_eq_g2With]
  exact g2With_le_g2Bound hS A _ fun pkSeed tbl z h =>
    (sufWin_cases pkSeed tbl z (sufWin_of_sufCheck pkSeed tbl z (hw _ _ _ h))).elim
      (freshWin_cases hS pkSeed tbl z) (sameWin_cases hS pkSeed tbl z)

/-- The real game with any final check that implies `sufCheck` is bounded by `bound`, at the
PRF distinguishers of that check and the six `G2` adversaries of the EUF-CMA proof. -/
theorem expW_le_bound (hS : Structural vp prims) (w : WinCheck vp prims)
    (hw : ∀ pk f log, w pk f log = true → sufCheck pk f log = true)
    (A : Forger vp prims optRand pkSeedDist) :
    prTrue (expW (realAlg vp prims optRand pkSeedDist) w A) ≤
      bound pkSeedDist (bPrfW w A) (bPrfMsgW w A) (bItsr A) (bOpenPre A) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A)) := by
  have h := (expW_le_prf_add_g2 hS w A).trans (add_le_add_right (g2W_le_g2Bound hS w hw A) _)
  refine h.trans (le_of_eq ?_)
  unfold bound g2Bound
  ring

/-! ## The theorems -/

/-- **Modular form (hops only).**  The SUF-CMA advantage is at most the two PRF advantages of the
strong-forgery distinguishers plus the probability of a strong forgery in `G2`; any bound on the
latter can be plugged in (`g2W_le_g2Bound` is the one proved here). -/
theorem suf_le_prf_add_g2 (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (realAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      (skPrf vp prims).prfAdvantage (bPrfW sufCheck S.toUnforgeableAdversary) +
        (msgPrf vp prims).prfAdvantage (bPrfMsgW sufCheck S.toUnforgeableAdversary) +
        prTrue (g2W sufCheck S.toUnforgeableAdversary) := by
  rw [strongAdvantage_eq_expW]
  exact expW_le_prf_add_g2 hS sufCheck _

/-- **Standard-model SUF-CMA security of SLH-DSA (FIPS 205 internal algorithms).**
(Stated with the phase-1 games and eager-table adversaries; superseded by
`Reduction.slhdsa_suf_cma_final_split`, `Reduction/HeadlineSplit.lean`.)

For every strong forger `S` against `internalAlg vp prims optRand pkSeedDist` — it wins by
outputting a valid `(message, signature)` pair that the signing oracle never returned, so a new
signature on a signed message counts — with `A := S.toUnforgeableAdversary` (the same program):

`Adv^{SUF-CMA}(S) ≤ Adv^{PRF}_{PRF}(bPrfW sufCheck A) + Adv^{PRF}_{PRF_msg}(bPrfMsgW sufCheck A)
   + Adv^{ITSR}_{H_msg}(bItsr A) + Adv^{SM-OpenPRE}_{F}(bOpenPre A) + Adv^{SM-TCR}_{Thash}(bTcr A)
   + (w-2)·Adv^{SM-UD}_{F}(rUd (bWots A)) + Adv^{SM-PRE}_{F}(rPre (bWots A))
   + Adv^{SM-TCR}_{F}(rTcr (bWots A))`.

The games and the last six adversaries are those of `slhdsa_euf_cma`; the two PRF distinguishers
are `bPrf`, `bPrfMsg` with the returned signatures recorded and the strong-forgery bit `sufCheck`
as output (same queries: `bPrfW_queryBound_exact`, `bPrfMsgW_queryBound`).  No assumption is
added: a same-message strong forgery with a new randomizer is covered by the pair-based ITSR
game and the EUF-CMA case analysis, and one with a reused randomizer is a WOTS+ forgery or a
collision with a hash call of the honest key structure, all of which are already targets of
`bTcr` (including `F` at revealed FORS secrets and at revealed WOTS+ chain values).  Holds for
every `optRand` (deterministic and hedged signing) and every `pkSeedDist`. -/
theorem slhdsa_suf_cma (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (realAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      bound pkSeedDist (bPrfW sufCheck S.toUnforgeableAdversary)
        (bPrfMsgW sufCheck S.toUnforgeableAdversary)
        (bItsr S.toUnforgeableAdversary) (bOpenPre S.toUnforgeableAdversary)
        (bTcr S.toUnforgeableAdversary)
        (rUd pkSeedDist (bWots S.toUnforgeableAdversary))
        (rPre pkSeedDist (bWots S.toUnforgeableAdversary))
        (rTcr pkSeedDist (bWots S.toUnforgeableAdversary)) := by
  rw [strongAdvantage_eq_expW]
  exact expW_le_bound hS sufCheck (fun _ _ _ h => h) _

/-- **The same-message residual.**  The probability that the forger outputs a valid, never
returned signature on a message it *did* query is bounded by `bound` at the PRF distinguishers
of `sameCheck` and the six `G2` adversaries.  (All six terms are needed: a new randomizer on a
signed message is a new `H_msg` input.) -/
theorem slhdsa_sameMessage_le (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (realAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      bound pkSeedDist (bPrfW sameCheck S.toUnforgeableAdversary)
        (bPrfMsgW sameCheck S.toUnforgeableAdversary)
        (bItsr S.toUnforgeableAdversary) (bOpenPre S.toUnforgeableAdversary)
        (bTcr S.toUnforgeableAdversary)
        (rUd pkSeedDist (bWots S.toUnforgeableAdversary))
        (rPre pkSeedDist (bWots S.toUnforgeableAdversary))
        (rTcr pkSeedDist (bWots S.toUnforgeableAdversary)) := by
  rw [sameMessageAdvantage_eq_expW]
  exact expW_le_bound hS sameCheck sameCheck_sufCheck _

/-- **Modular form over any EUF-CMA bound.**  If `β` bounds the EUF-CMA advantage of every
forger, then `Adv^{SUF-CMA}(S) ≤ β (S as EUF forger) + same-message residual`.  (Looser than
`slhdsa_suf_cma` when `β` is itself `bound`: the six `G2` terms then occur twice.) -/
theorem slhdsa_suf_cma_of_euf (hS : Structural vp prims)
    (β : Forger vp prims optRand pkSeedDist → ℝ≥0∞)
    (hβ : ∀ B : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp B ≤ β B)
    (S : SignatureAlg.StrongUnforgeableAdversary (realAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      β S.toUnforgeableAdversary +
        bound pkSeedDist (bPrfW sameCheck S.toUnforgeableAdversary)
          (bPrfMsgW sameCheck S.toUnforgeableAdversary)
          (bItsr S.toUnforgeableAdversary) (bOpenPre S.toUnforgeableAdversary)
          (bTcr S.toUnforgeableAdversary)
          (rUd pkSeedDist (bWots S.toUnforgeableAdversary))
          (rPre pkSeedDist (bWots S.toUnforgeableAdversary))
          (rTcr pkSeedDist (bWots S.toUnforgeableAdversary)) := by
  rw [SignatureAlg.strongUnforgeableAdvantage_eq_euf_add_sameMessage]
  exact add_le_add (hβ _) (slhdsa_sameMessage_le hS S)

/-- **The SUF-CMA bound with the `qs`-dependent resources of the reductions**: the same counts as
in `slhdsa_euf_cma_resources`. -/
theorem slhdsa_suf_cma_resources (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (realAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (S.main pk) (fun i => i.isRight = true) qs) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        bound pkSeedDist (bPrfW sufCheck S.toUnforgeableAdversary)
          (bPrfMsgW sufCheck S.toUnforgeableAdversary)
          (bItsr S.toUnforgeableAdversary) (bOpenPre S.toUnforgeableAdversary)
          (bTcr S.toUnforgeableAdversary)
          (rUd pkSeedDist (bWots S.toUnforgeableAdversary))
          (rPre pkSeedDist (bWots S.toUnforgeableAdversary))
          (rTcr pkSeedDist (bWots S.toUnforgeableAdversary)) ∧
      IsQueryBoundP (bPrfW sufCheck S.toUnforgeableAdversary) (fun i => i.isRight = true)
        (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) ∧
      IsQueryBoundP (bPrfMsgW sufCheck S.toUnforgeableAdversary) (fun i => i.isRight = true) qs ∧
      IsQueryBoundP (bItsr S.toUnforgeableAdversary).main (fun i => i.isRight = true) qs :=
  ⟨slhdsa_suf_cma hS S, bPrfW_queryBound_exact sufCheck _ qs hA,
    bPrfMsgW_queryBound sufCheck _ qs hA, bItsr_queryBound _ qs hA⟩

end Reduction

#print axioms Reduction.g2Fresh_le
#print axioms Reduction.g2Suf_le
#print axioms Reduction.suf_le_prf_add_g2
#print axioms Reduction.slhdsa_suf_cma
#print axioms Reduction.slhdsa_sameMessage_le
#print axioms Reduction.slhdsa_suf_cma_of_euf
#print axioms Reduction.slhdsa_suf_cma_resources
