import Reduction.Suf
import Reduction.Lazy.ItsrLazy
import Reduction.Lazy.OpenPreSparse
import Reduction.Lazy.TcrSparse
import Reduction.Lazy.WotsSparse

/-!
# The `G2`-level strong-unforgeability analysis at the table-free adversaries

`Reduction.Suf` bounds the strong-forgery event of `G2` by the six non-PRF terms at the
adversaries `bItsr`, `bOpenPre`, `bTcr`, `bWots` of `Reduction.Final`, all of which sample the
eager `2 ^ 256`-cell table.  This file redoes the four branch bounds at the adversaries of
`Reduction.Lazy` (`bItsrL`, `bOpenPreS`, `bTcrS`, `bWotsS`):

* `g2WithS A win` — `G2` with the sparse table of the key structure and final check `win`;
  `prTrue_g2With_eq_sparse`: equal to `g2With A win` when `win` reads only structure cells;
* `brS_itsr`, `brS_open`, `brS_coll`, `brS_wots` — the four branch bounds;
* `g2WithS_le_g2BoundS`, `g2W_le_g2BoundS` — the union bound: any final check that implies
  `sufCheck` is bounded in `G2` by `g2BoundS A`, the six terms at the table-free adversaries.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- Game `G2` with the sparse table of the key structure and the final check `win`. -/
noncomputable def g2WithS (A : Forger vp prims optRand pkSeedDist)
    (win : prims.PkSeed → SecretTable vp prims → G2Out vp prims → Bool) : ProbComp Bool :=
  pkSeedDist >>= fun pkSeed => Lazy.sparseTable vp prims >>= fun tbl =>
    g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z => pure (win pkSeed tbl z)

theorem g2WithS_le_add (A : Forger vp prims optRand pkSeedDist)
    (p q r : prims.PkSeed → SecretTable vp prims → G2Out vp prims → Bool)
    (h : ∀ pkSeed tbl z, p pkSeed tbl z = true → q pkSeed tbl z = true ∨ r pkSeed tbl z = true) :
    prTrue (g2WithS A p) ≤ prTrue (g2WithS A q) + prTrue (g2WithS A r) :=
  prTrue_bind_le_add _ _ _ _ fun pkSeed _ => prTrue_bind_le_add _ _ _ _ fun tbl _ =>
    prTrue_bind_pure_le_add _ _ _ _ fun z _ => h pkSeed tbl z

theorem idealSign_restrict_struct (hS : Structural vp prims) (tbl : SecretTable vp prims) :
    idealSign vp prims (Lazy.restrictTo (Lazy.structSecIdx vp) tbl) = idealSign vp prims tbl :=
  funext fun m => funext fun pk => funext fun R =>
    Lazy.idealSign_restrictTo hS tbl m pk R fun _ hi => hi

theorem idealPk_restrict_struct (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) :
    idealPk vp prims (Lazy.restrictTo (Lazy.structSecIdx vp) tbl) pkSeed =
      idealPk vp prims tbl pkSeed :=
  Lazy.idealPk_restrictTo hS tbl pkSeed fun _ hi => List.mem_append_right _ hi

/-- **Eager = sparse** for every final check that reads only structure cells of the table. -/
theorem prTrue_g2With_eq_sparse (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist)
    (win : prims.PkSeed → SecretTable vp prims → G2Out vp prims → Bool)
    (hwin : ∀ pkSeed tbl z,
      win pkSeed (Lazy.restrictTo (Lazy.structSecIdx vp) tbl) z = win pkSeed tbl z) :
    prTrue (g2With A win) = prTrue (g2WithS A win) := by
  unfold g2With g2WithS
  refine prTrue_congr (evalDist_bind_congr_of_support _ _ _ fun pkSeed _ => ?_)
  refine Eq.trans ?_ (Lazy.evalDist_sparseOn_bind (Lazy.structSecIdx_nodup hS)
    (fun tbl => g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z =>
      pure (win pkSeed tbl z))).symm
  have e : (fun tbl : SecretTable vp prims =>
      g2Run A (Lazy.restrictTo (Lazy.structSecIdx vp) tbl)
          (idealPk vp prims (Lazy.restrictTo (Lazy.structSecIdx vp) tbl) pkSeed) >>= fun z =>
        (pure (win pkSeed (Lazy.restrictTo (Lazy.structSecIdx vp) tbl) z) : ProbComp Bool)) =
      fun tbl => g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z =>
        pure (win pkSeed tbl z) :=
    funext fun tbl => by
      rw [idealPk_restrict_struct hS]
      unfold g2Run
      rw [idealSign_restrict_struct hS]
      simp only [hwin]
  rw [e]

/-! ## The four branches -/

theorem evItsr_restrict (hS : Structural vp prims) (pkSeed : prims.PkSeed)
    (tbl : SecretTable vp prims) (z : G2Out vp prims) :
    evItsr pkSeed (Lazy.restrictTo (Lazy.structSecIdx vp) tbl) z = evItsr pkSeed tbl z := by
  unfold evItsr g2ClassOf
  rw [idealPk_restrict_struct hS, idealSign_restrict_struct hS]

/-- **ITSR branch at the lazy adversary.** -/
theorem brS_itsr (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2WithS A evItsr) ≤ KeyedHash.ITSRAdvantage (Lazy.bItsrL A) := by
  rw [← prTrue_g2With_eq_sparse hS A evItsr (evItsr_restrict hS), Lazy.itsrAdvantage_bItsrL]
  exact br_itsr A

/-- **Open-preimage branch at the sparse adversary.** -/
theorem brS_open (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2WithS A evOpen) ≤
      TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) := by
  show _ ≤ prTrue (TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.experiment
    (bOpenPreWith (Lazy.sparseOn vp prims (Lazy.wotsSkIdx vp)) A))
  rw [op_experiment hS (Lazy.sparseOn vp prims (Lazy.wotsSkIdx vp)) A]
  refine le_trans (prTrue_bind_mono _ _ _ fun pkSeed _ =>
    prTrue_bind_mono (Lazy.sparseTable vp prims) _ _ fun tbl _ =>
      prTrue_bind_pure_mono _ _ (opW pkSeed tbl) fun z _ h =>
        op_win hS pkSeed tbl z (of_decide_eq_true h)) ?_
  refine le_of_eq (prTrue_bind_congr _ _ _ fun pkSeed _ => ?_)
  have hx := Lazy.evalDist_sparseOn_extract (vp := vp) (prims := prims)
    (is := forsSkIdx vp) (js := Lazy.wotsSkIdx vp) (Lazy.structSecIdx_nodup hS)
    (fun T => g2Run A T (idealPk vp prims T pkSeed) >>= fun z => pure (opW pkSeed T z))
  refine (prTrue_congr hx).symm.trans ?_
  refine prTrue_bind_congr _ _ _ fun tbl _ => prTrue_bind_congr _ _ _ fun xs hxs => ?_
  rw [op_tail hS (Lazy.sparseOn vp prims (Lazy.wotsSkIdx vp)) A pkSeed tbl xs
    (Tables.length_of_mem_support_sampleList hxs)]

/-- **Collision branch at the sparse adversary.** -/
theorem brS_coll (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2WithS A evColl) ≤ TweakableHash.SM_DT_TCR_Advantage (Lazy.bTcrS A) := by
  unfold TweakableHash.SM_DT_TCR_Advantage prTrue Lazy.bTcrS
  rw [Lazy.tcrExperiment_bTcrWith hS (Lazy.sparseTable vp prims) A, g2WithS]
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

/-- **WOTS+ branch at the sparse adversary.** -/
theorem brS_wots (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2WithS A evWots) ≤
      prTrue (WotsGame.hyb pkSeedDist (wotsInsts vp) 0 (Lazy.bWotsS A)) := by
  unfold Lazy.bWotsS
  rw [Lazy.hyb_bWotsWith_eq]
  calc prTrue (g2WithS A evWots)
      ≤ prTrue (pkSeedDist >>= fun pk => Lazy.sparseTable vp prims >>= fun tbl =>
          simulateQ (Tables.fnImpl fun a => Tables.readBlock tbl (wotsCells vp a))
            (qGame A pk tbl)) :=
        prTrue_bind_bind_mono pkSeedDist (Lazy.sparseTable vp prims) _ _ (wots_table_step hS A)
    _ = _ := prTrue_bind_congr _ _ _ fun pk _ => prTrue_congr (Lazy.fresh_eq_sparse hS A pk).symm

/-! ## The union bound -/

/-- The six terms that remain after the two PRF hops, at the table-free adversaries. -/
noncomputable def g2BoundS (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) +
    TweakableHash.SM_DT_TCR_Advantage (Lazy.bTcrS A) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
      TweakableHash.SM_DT_UD_Advantage (rUd pkSeedDist (Lazy.bWotsS A)) +
    TweakableHash.SM_DT_PRE_Advantage (rPre pkSeedDist (Lazy.bWotsS A)) +
    TweakableHash.SM_DT_TCR_Advantage (rTcr pkSeedDist (Lazy.bWotsS A))

/-- **Union bound over the four chargeable events, table-free adversaries.** -/
theorem g2WithS_le_g2BoundS (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (win : prims.PkSeed → SecretTable vp prims → G2Out vp prims → Bool)
    (hwin : ∀ pkSeed tbl z, win pkSeed tbl z = true →
      evItsr pkSeed tbl z = true ∨ evOpen pkSeed tbl z = true ∨
        evColl pkSeed tbl z = true ∨ evWots pkSeed tbl z = true) :
    prTrue (g2WithS A win) ≤ g2BoundS A := by
  have h1 := g2WithS_le_add A win evItsr
    (fun pkSeed tbl z => evOpen pkSeed tbl z || (evColl pkSeed tbl z || evWots pkSeed tbl z))
    (fun pkSeed tbl z h => by
      rcases hwin pkSeed tbl z h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h]; rfl)
      · exact Or.inr (by rw [h]; simp)
      · exact Or.inr (by rw [h]; simp))
  have h2 := g2WithS_le_add A
    (fun pkSeed tbl z => evOpen pkSeed tbl z || (evColl pkSeed tbl z || evWots pkSeed tbl z))
    evOpen (fun pkSeed tbl z => evColl pkSeed tbl z || evWots pkSeed tbl z)
    (fun pkSeed tbl z h => by simpa [Bool.or_eq_true] using h)
  have h3 := g2WithS_le_add A
    (fun pkSeed tbl z => evColl pkSeed tbl z || evWots pkSeed tbl z) evColl evWots
    (fun pkSeed tbl z h => by simpa [Bool.or_eq_true] using h)
  have hud := stepWotsUD hS pkSeedDist (Lazy.bWotsS A)
  have hfin := stepWotsFinal hS pkSeedDist (Lazy.bWotsS A)
  unfold StepWotsUD at hud
  unfold StepWotsFinal at hfin
  have hw := (brS_wots hS A).trans (hud.trans (add_le_add_left hfin _))
  unfold g2BoundS
  calc prTrue (g2WithS A win)
      ≤ prTrue (g2WithS A evItsr) + (prTrue (g2WithS A evOpen) +
          (prTrue (g2WithS A evColl) + prTrue (g2WithS A evWots))) :=
        h1.trans (add_le_add_right (h2.trans (add_le_add_right h3 _)) _)
    _ ≤ KeyedHash.ITSRAdvantage (Lazy.bItsrL A) +
          (TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (Lazy.bOpenPreS A) +
          (TweakableHash.SM_DT_TCR_Advantage (Lazy.bTcrS A) +
          (TweakableHash.SM_DT_PRE_Advantage (rPre pkSeedDist (Lazy.bWotsS A)) +
              TweakableHash.SM_DT_TCR_Advantage (rTcr pkSeedDist (Lazy.bWotsS A)) +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
              TweakableHash.SM_DT_UD_Advantage (rUd pkSeedDist (Lazy.bWotsS A))))) :=
        add_le_add (brS_itsr hS A) (add_le_add (brS_open hS A) (add_le_add (brS_coll hS A) hw))
    _ = _ := by ring

/-- The check of `g2W` reads only structure cells of the table. -/
theorem winOfCheck_restrict (hS : Structural vp prims) (w : WinCheck vp prims)
    (pkSeed : prims.PkSeed) (tbl : SecretTable vp prims) (z : G2Out vp prims) :
    w (idealPk vp prims (Lazy.restrictTo (Lazy.structSecIdx vp) tbl) pkSeed) z.1
        (sigLogOf (Lazy.restrictTo (Lazy.structSecIdx vp) tbl)
          (idealPk vp prims (Lazy.restrictTo (Lazy.structSecIdx vp) tbl) pkSeed) z.2) =
      w (idealPk vp prims tbl pkSeed) z.1 (sigLogOf tbl (idealPk vp prims tbl pkSeed) z.2) := by
  unfold sigLogOf
  rw [idealPk_restrict_struct hS, idealSign_restrict_struct hS]

/-- **Strong forgeries in `G2`, table-free adversaries.**  Any final check that implies
`sufCheck` is bounded in `G2` by the six `G2`-terms at `bItsrL`, `bOpenPreS`, `bTcrS`,
`rUd/rPre/rTcr (bWotsS ·)`. -/
theorem g2W_le_g2BoundS (hS : Structural vp prims) (w : WinCheck vp prims)
    (hw : ∀ pk f log, w pk f log = true → sufCheck pk f log = true)
    (A : Forger vp prims optRand pkSeedDist) : prTrue (g2W w A) ≤ g2BoundS A := by
  rw [g2W_eq_g2With, prTrue_g2With_eq_sparse hS A _ (winOfCheck_restrict hS w)]
  exact g2WithS_le_g2BoundS hS A _ fun pkSeed tbl z h =>
    (sufWin_cases pkSeed tbl z (sufWin_of_sufCheck pkSeed tbl z (hw _ _ _ h))).elim
      (freshWin_cases hS pkSeed tbl z) (sameWin_cases hS pkSeed tbl z)

#print axioms Reduction.g2W_le_g2BoundS

end Reduction
