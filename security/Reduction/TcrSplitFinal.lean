import Reduction.Final
import Reduction.TcrSplit
import Reduction.ForsTightFinal

/-!
# Splitting the SM-TCR term on `Thash` into per-arity terms

The phase-1 bound (`slhdsa_euf_cma`) has one term `Adv^{SM-TCR}_{Thash}(bTcr A)` on the
variable-arity `Thash` (`tcrProblem`), in which a collision between inputs of different arity also wins.  Here it is
replaced by four per-function terms, one per arity class
`1` (`F`), `2` (`H`: FORS and XMSS tree hash), `len` (`T_len`, WOTS+ public-key compression),
`k` (`T_k`, FORS roots compression):

* `thashArityProblem vp prims pkSeedDist n` — SM-TCR on `Thash` restricted to inputs of length
  `n` (message type `{xs // xs.length = n}`), with the whole `Thash` as collection
  (`thashColl`, as in `wotsTcrProblem`) and cap `tcrTargets vp`;
* `bTcrAr n A := TcrSplit.restrict … (bTcr A)` — the explicit restricted adversary (runs
  `bTcr A` once; arity-`n` targets go to the challenge oracle, the other hash calls of the
  structure to the collection oracle; a collision found by `bTcr A` is forwarded iff it is
  between two inputs of arity `n`).

What is proved.

* Unconditionally: `bTcrAr_advantage_eq` (the restricted adversary wins exactly when `bTcr A`
  wins by an arity-`n` collision), `bTcr_advantage_le_split_add_cross`
  (`Adv(bTcr A) ≤ Σ + Pr[bTcr A wins by a collision outside the four classes]`), and
  non-vacuity of the per-arity games (`thashArity_trivial_adv_zero`,
  `thashArityCollider_adv_one`, `toy_thashArity`).
* **Conditionally** on the named hypothesis `VerifyAritySound vp prims` (a deterministic,
  non-cryptographic statement about the hash calls of verification; not proved in this file,
  proved as `Reduction.verifyAritySound` in `Reduction/VerifyArity.lean`; the unconditional
  forms are in `Reduction/TcrSplitClosed.lean` and, for the final lazy/sparse adversaries and
  SUF-CMA, in `Reduction/HeadlineSplit.lean`):
  `stepTCR_split` (`Pr[G2 ∧ class = tcr] ≤ Σ_i Adv_i(bTcrAr nᵢ A)`),
  `slhdsa_euf_cma_tcr_split` and `slhdsa_euf_cma_fors_tight_tcr_split`.

`Adv(bTcr A) ≤ Σ_i Adv_i(bTcrAr nᵢ A)` itself is not claimed: when the forgery yields no
collision `bTcr A` answers the fixed guess `(0, [])`, which wins its own game if
`Thash pk t₀ [] = Thash pk t₀ m₀` (a cross-arity collision no restricted adversary can use).
The split is therefore made at the level of the step (`StepTCR`), which is what the final
theorem uses.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal MeasureTheory

namespace Reduction

open TweakableHash

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## The per-arity games and adversaries -/

variable (vp prims) in
/-- SM-TCR on `Thash` restricted to inputs of arity `n`, with `Thash` as collection. -/
def thashArityProblem (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ) :
    SM_DT_TCR_Problem Unit prims.PkSeed prims.AdrsKey {xs : List prims.Y // xs.length = n}
      prims.Y :=
  TcrSplit.classProblem (thashList vp prims pkSeedDist) (fun xs => xs.length = n) (tcrTargets vp)

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
theorem thashArityProblem_thColl (n : ℕ) :
    (thashArityProblem vp prims pkSeedDist n).thColl = thashColl vp prims := rfl

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [Inhabited prims.Y] in
theorem thashArityProblem_eval (n : ℕ) (pk : prims.PkSeed) (t : prims.AdrsKey)
    (m : {xs : List prims.Y // xs.length = n}) :
    (thashArityProblem vp prims pkSeedDist n).th.eval pk t m = prims.Thash pk t m.1 := rfl

/-- A fixed input of arity `n`. -/
def arityDefault (prims : Primitives vp.params) [Inhabited prims.Y] (n : ℕ) :
    {xs : List prims.Y // xs.length = n} :=
  ⟨List.replicate n default, List.length_replicate⟩

/-- The arity-`n` SM-TCR adversary derived from `bTcr A`. -/
noncomputable def bTcrAr (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Adversary (thashArityProblem vp prims pkSeedDist n) :=
  TcrSplit.restrict (fun xs => xs.length = n) (arityDefault prims n) (bTcr A)

/-- The four arities of `Thash` in SLH-DSA: `F`, `H`, `T_len`, `T_k`. -/
def arities (vp : ValidatedParams) : Fin 4 → ℕ := ![1, 2, vp.params.len, vp.params.k]

/-- **The restricted adversary wins exactly when `bTcr A` wins by an arity-`n` collision.** -/
theorem bTcrAr_advantage_eq (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Advantage (bTcrAr n A) =
      𝒟[TcrSplit.winIn (thashList vp prims pkSeedDist) (fun xs => xs.length = n) <$>
        TcrSplit.raw (bTcr A)] {true} :=
  TcrSplit.restrict_advantage_eq _ _ _

/-- **Unconditional split with the exact correction term.** -/
theorem bTcr_advantage_le_split_add_cross (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_Advantage (bTcr A) ≤
      ∑ i, SM_DT_TCR_Advantage (bTcrAr (arities vp i) A) +
        𝒟[TcrSplit.winCross (fun (i : Fin 4) (xs : List prims.Y) => xs.length = arities vp i)
          (thashList vp prims pkSeedDist) <$> TcrSplit.raw (bTcr A)] {true} :=
  TcrSplit.advantage_le_sum_add_cross
    (fun (i : Fin 4) (xs : List prims.Y) => xs.length = arities vp i)
    (fun i => arityDefault prims (arities vp i)) (bTcr A)

/-! ## The named hypothesis -/

variable (vp prims) in
/-- **Named hypothesis (not proved in this file; proved from `Structural` alone as
`Reduction.verifyAritySound`, `Reduction/VerifyArity.lean`).**  Under the structural side
conditions, whenever a hash call of the verification of an arbitrary signature has the same
tweak as a hash call of the honest structure, the two inputs have the same arity, and that arity
is one of `1, 2, len, k`.

Deterministic and non-cryptographic: the tweak is the encoding of an address, the address type
(and, for `FORS_TREE`, whether the height is `0`) determines which of `F`, `H`, `T_len`, `T_k`
is called at it, both in the honest structure and in verification, and the encoding is injective
on in-range addresses (`Structural.keyInj`). -/
def VerifyAritySound : Prop :=
  Structural vp prims → ∀ (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core),
    ∀ c ∈ verifyCalls (idealPk vp prims tbl pkSeed) msg sig, ∀ t ∈ honestCalls tbl pkSeed,
      t.1 = c.1 → c.2.length = t.2.length ∧ ∃ i : Fin 4, t.2.length = arities vp i

/-! ## The step -/

omit [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.PkSeed] [Inhabited prims.Y] in
/-- What `findCollision` returns: a call of `calls` and the target it collides with. -/
theorem findCollision_spec (pk : prims.PkSeed)
    (targets calls : List (prims.AdrsKey × List prims.Y)) (j : ℕ) (m : List prims.Y)
    (h : findCollision pk targets calls = some (j, m)) :
    ∃ c ∈ calls, ∃ t, targets[j]? = some t ∧ m = c.2 ∧ t.1 = c.1 ∧ c.2 ≠ t.2 ∧
      prims.Thash pk t.1 c.2 = prims.Thash pk t.1 t.2 := by
  unfold findCollision at h
  obtain ⟨c, hcm, hc⟩ := List.exists_of_findSome?_eq_some h
  dsimp only at hc
  split_ifs at hc with hlt
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
  refine ⟨c, hcm, _, List.getElem?_eq_getElem hlt, rfl, ?_⟩
  have := List.findIdx_getElem (w := hlt)
  simp only [decide_eq_true_eq] at this
  obtain ⟨h1, h2, h3⟩ := this
  exact ⟨h1, h2, (congrArg (fun k => prims.Thash pk k c.2) h1).trans h3⟩

/-- The common experiment of the split at `bTcr A`, with the `choose` phase evaluated. -/
theorem raw_bTcr (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    TcrSplit.raw (bTcr A) = (do
      let pkSeed ← pkSeedDist
      let tbl ← sampleTable vp prims
      let r ← g2Run A tbl (idealPk vp prims tbl pkSeed)
      pure (pkSeed, honestCalls tbl pkSeed,
        (findCollision pkSeed (honestCalls tbl pkSeed)
          (verifyCalls (idealPk vp prims tbl pkSeed) r.1.1 r.1.2)).getD (0, []))) := by
  unfold TcrSplit.raw
  refine bind_congr fun pkSeed => ?_
  have h := bTcr_choose_run hS A pkSeed
  refine (congrArg (· >>= _) h).trans ?_
  rw [map_eq_bind_pure_comp]
  refine (bind_assoc _ _ _).trans ?_
  refine bind_congr fun tbl => ?_
  refine (pure_bind _ _).trans ?_
  refine (bind_assoc (g2Run A tbl (idealPk vp prims tbl pkSeed)) _ _).trans ?_
  refine bind_congr fun r => ?_
  exact pure_bind _ _

/-- **Step 6, split (conditional on `VerifyAritySound`).**
`Pr[G2 ∧ class = tcr] ≤ Σ_{n ∈ {1, 2, len, k}} Adv^{SM-TCR}_{Thash|arity n}(bTcrAr n A)`. -/
theorem stepTCR_split (hS : Structural vp prims) (hAr : VerifyAritySound vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    prTrue (g2Class A .tcr) ≤ ∑ i, SM_DT_TCR_Advantage (bTcrAr (arities vp i) A) := by
  let E : TcrSplit.Raw prims.PkSeed prims.AdrsKey prims.Y → Bool := fun r =>
    decide (∃ i : Fin 4, TcrSplit.winIn (thashList vp prims pkSeedDist)
      (fun xs => xs.length = arities vp i) r = true)
  have hsum := TcrSplit.prEvent_le_sum_restrict
    (fun (i : Fin 4) (xs : List prims.Y) => xs.length = arities vp i)
    (fun i => arityDefault prims (arities vp i)) (bTcr A) E (fun r hr => by simpa [E] using hr)
  refine le_trans ?_ hsum
  rw [raw_bTcr hS A]
  unfold prTrue g2Class
  simp only [map_bind, map_pure]
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun pkSeed => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun tbl => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun r => ?_
  obtain ⟨⟨msg, sig⟩, log⟩ := r
  dsimp only
  by_cases hv : (g2Valid (idealPk vp prims tbl pkSeed) log msg sig &&
      decide (g2ClassOf tbl (idealPk vp prims tbl pkSeed) log msg sig = .tcr)) = true
  · rw [Bool.and_eq_true, decide_eq_true_eq] at hv
    have hsome := findCollision_isSome_of_tcr hS tbl pkSeed log msg sig hv.1 hv.2
    obtain ⟨⟨j, m⟩, hjm⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨c, hc, t, ht, rfl, hkey, hne, heq⟩ := findCollision_spec _ _ _ j m hjm
    obtain ⟨hlen, i, hi⟩ := hAr hS tbl pkSeed msg sig c hc t (List.mem_of_getElem? ht) hkey
    have hE : E (pkSeed, honestCalls tbl pkSeed,
        (findCollision pkSeed (honestCalls tbl pkSeed)
          (verifyCalls (idealPk vp prims tbl pkSeed) msg sig)).getD (0, [])) = true := by
      rw [hjm]
      simp only [E, decide_eq_true_eq]
      refine ⟨i, ?_⟩
      simp only [TcrSplit.winIn, Option.getD_some, ht, decide_eq_true_eq]
      exact ⟨hi, hlen.trans hi, hne, heq⟩
    rw [hE]
    simp [hv.1, hv.2]
  · rw [Bool.not_eq_true] at hv
    rw [hv]
    simp

/-! ## The final theorems -/

/-- The four per-arity SM-TCR terms: `F`, `H`, `T_len`, `T_k`. -/
noncomputable def tcrSplitSum (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  SM_DT_TCR_Advantage (bTcrAr 1 A) + SM_DT_TCR_Advantage (bTcrAr 2 A) +
    SM_DT_TCR_Advantage (bTcrAr vp.params.len A) + SM_DT_TCR_Advantage (bTcrAr vp.params.k A)

theorem sum_arities_eq (A : Forger vp prims optRand pkSeedDist) :
    ∑ i, SM_DT_TCR_Advantage (bTcrAr (arities vp i) A) = tcrSplitSum A := by
  rw [Fin.sum_univ_four]
  rfl

/-- **`final_of_steps` with the collision branch bounded by an arbitrary quantity `X`.**
Same composition as `Reduction.final_of_steps`; the lead can instantiate the other slots with
any adversaries satisfying the step statements (for instance package A's lazy ones). -/
theorem final_of_steps_tcr (A : Forger vp prims optRand pkSeedDist)
    (B₁ : SkPrfAdv prims) (B₂ : MsgPrfAdv prims)
    (B₃ : KeyedHash.ITSRAdversary (itsrProblem vp prims))
    (B₄ : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsOpenPreProblem vp prims pkSeedDist))
    (W : WotsGame.Adversary prims)
    (B₆ : SM_DT_UD_Adversary (wotsUdProblem vp prims pkSeedDist))
    (B₇ : SM_DT_PRE_Adversary (wotsPreProblem vp prims pkSeedDist))
    (B₈ : SM_DT_TCR_Adversary (wotsTcrProblem vp prims pkSeedDist)) (X : ℝ≥0∞)
    (h₁ : StepPRF A B₁) (h₂ : StepPRFmsg A B₂) (h₃ : StepSplit A)
    (h₄ : StepITSR A B₃) (h₅ : StepOpenPRE A B₄) (h₆ : prTrue (g2Class A .tcr) ≤ X)
    (h₇ : StepWotsEmbed A W) (h₈ : StepWotsUD pkSeedDist W B₆)
    (h₉ : StepWotsFinal pkSeedDist W B₇ B₈) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      (skPrf vp prims).prfAdvantage B₁ + (msgPrf vp prims).prfAdvantage B₂ +
        KeyedHash.ITSRAdvantage B₃ +
        SM_DT_OpenPRE_SourceFinalValidity.advantage B₄ + X +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage B₆ +
        SM_DT_PRE_Advantage B₇ + SM_DT_TCR_Advantage B₈ := by
  rw [unforgeableAdvantage_eq_prTrue_g0]
  unfold StepPRF at h₁; unfold StepPRFmsg at h₂; unfold StepSplit at h₃
  unfold StepITSR at h₄; unfold StepOpenPRE at h₅
  unfold StepWotsEmbed at h₇; unfold StepWotsUD at h₈; unfold StepWotsFinal at h₉
  have hw := h₇.trans (h₈.trans (add_le_add_left h₉ _))
  calc prTrue (g0 A) ≤ prTrue (g1 A) + _ := h₁
    _ ≤ (prTrue (g2 A) + _) + _ := by gcongr
    _ ≤ ((prTrue (g2Class A .itsr) + prTrue (g2Class A .openpre) +
          prTrue (g2Class A .tcr) + prTrue (g2Class A .wots)) + _) + _ := by gcongr
    _ ≤ ((KeyedHash.ITSRAdvantage B₃ +
          SM_DT_OpenPRE_SourceFinalValidity.advantage B₄ + X +
          (SM_DT_PRE_Advantage B₇ + SM_DT_TCR_Advantage B₈ +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage B₆)) +
          (msgPrf vp prims).prfAdvantage B₂) + (skPrf vp prims).prfAdvantage B₁ := by gcongr
    _ = _ := by ring

/-- **The phase-1 bound with the `Thash` SM-TCR term split per arity — conditional on the
named hypothesis `VerifyAritySound vp prims`** (which is proved: `Reduction.verifyAritySound`;
unconditional form `slhdsa_euf_cma_tcr_split'`, `Reduction/TcrSplitClosed.lean`).

`Adv^{EUF-CMA}(A) ≤ Adv^{PRF}(bPrf A) + Adv^{PRF_msg}(bPrfMsg A) + Adv^{ITSR}(bItsr A)
   + Adv^{SM-OpenPRE}_F(bOpenPre A)
   + [Adv^{SM-TCR}_F(bTcrAr 1 A) + Adv^{SM-TCR}_H(bTcrAr 2 A)
      + Adv^{SM-TCR}_{T_len}(bTcrAr len A) + Adv^{SM-TCR}_{T_k}(bTcrAr k A)]
   + (w−2)·Adv^{SM-UD}_F(rUd (bWots A)) + Adv^{SM-PRE}_F(rPre (bWots A))
   + Adv^{SM-TCR}_F(rTcr (bWots A))`. -/
theorem slhdsa_euf_cma_tcr_split (hS : Structural vp prims) (hAr : VerifyAritySound vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      (skPrf vp prims).prfAdvantage (bPrf A) + (msgPrf vp prims).prfAdvantage (bPrfMsg A) +
        KeyedHash.ITSRAdvantage (bItsr A) +
        SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre A) + tcrSplitSum A +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A)) :=
  final_of_steps_tcr A (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bWots A)
    (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A))
    (tcrSplitSum A)
    (stepPRF hS A) (stepPRFmsg A) (stepSplit A) (stepITSR A) (stepOpenPRE hS A)
    ((stepTCR_split hS hAr A).trans (sum_arities_eq A).le)
    (stepWotsEmbed hS A) (stepWotsUD hS pkSeedDist (bWots A))
    (stepWotsFinal hS pkSeedDist (bWots A))

/-- **Both strengthenings: tight FORS term (unconditional) and per-arity TCR terms (conditional
on `VerifyAritySound vp prims`).**  The right-hand side has the shape of Hülsing–Kudinov
Theorem 1 / EasyCrypt `EUFCMA_SPHINCS_PLUS`, except that FORS-tree and XMSS-tree `H` share one
term and an `F` term appears in the collision branch. -/
theorem slhdsa_euf_cma_fors_tight_tcr_split [Fintype prims.Y] (hS : Structural vp prims)
    (hAr : VerifyAritySound vp prims) (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      (skPrf vp prims).prfAdvantage (bPrf A) + (msgPrf vp prims).prfAdvantage (bPrfMsg A) +
        KeyedHash.ITSRAdvantage (bItsr A) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPre A)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPre A))) + tcrSplitSum A +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A)) := by
  refine (slhdsa_euf_cma_tcr_split hS hAr A).trans ?_
  have h := forsOpenPre_le (bOpenPre A)
  gcongr

/-! ## Non-vacuity of the per-arity games -/

/-- The arity-`n` game can be lost: no target, advantage `0`. -/
theorem thashArity_trivial_adv_zero (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ) :
    SM_DT_TCR_Advantage (prob := thashArityProblem vp prims pkSeedDist n)
      ⟨Unit, pure (), fun _ _ => pure (0, arityDefault prims n)⟩ = 0 := by
  apply prTrue_eq_zero_of_support
  intro x hx
  simp [SM_DT_TCR_Experiment] at hx
  exact hx.2

/-- The arity-`n` adversary that commits to the target `(t, x)` and answers `y`. -/
def thashArityCollider (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ) (t : prims.AdrsKey)
    (x y : {xs : List prims.Y // xs.length = n}) :
    SM_DT_TCR_Adversary (thashArityProblem vp prims pkSeedDist n) where
  State := Unit
  choose := do
    let _ ← (unifSpec + (SM_DT_TCR_challengeSpec prims.AdrsKey
        {xs : List prims.Y // xs.length = n} prims.Y +
      collectionSpec (thashArityProblem vp prims pkSeedDist n).thColl)).query
        (Sum.inr (Sum.inl (t, x)))
    pure ()
  forge := fun _ _ => pure (0, y)

/-- The arity-`n` game can be won: a seed-independent collision between two inputs of arity `n`
at some tweak gives advantage `1`. -/
theorem thashArityCollider_adv_one (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ)
    (h0 : 0 < tcrTargets vp) (t : prims.AdrsKey) (x y : {xs : List prims.Y // xs.length = n})
    (hne : y ≠ x) (hcol : ∀ pk, prims.Thash pk t y.1 = prims.Thash pk t x.1) :
    SM_DT_TCR_Advantage (thashArityCollider (vp := vp) pkSeedDist n t x y) = 1 := by
  apply prTrue_eq_one_of_support
  intro b hb
  have hrun : ∀ pk, (SM_DT_TCR_challengeOracle (thashArityProblem vp prims pkSeedDist n) pk
      (t, x)).run (([], []) : SM_DT_TCR_State prims.AdrsKey
        {xs : List prims.Y // xs.length = n}) = _ :=
    fun pk => SM_DT_TCR_challengeOracle_run_of_fresh (by exact h0)
      (by simp [TweakFresh, TweakReserved])
  simp [SM_DT_TCR_Experiment, thashArityCollider, SM_DT_TCR_oracles, hrun] at hb
  obtain ⟨pk, -, rfl⟩ := hb
  have h : (thashArityProblem vp prims pkSeedDist n).th.eval pk t y =
      (thashArityProblem vp prims pkSeedDist n).th.eval pk t x := hcol pk
  simp [hne, h]

/-- On the constant toy bundle the arity-`1` game is won with probability `1`. -/
theorem toy_thashArity (vp : ValidatedParams)
    (pkSeedDist : ProbComp (toyPrims vp.params).PkSeed) :
    ∃ B : SM_DT_TCR_Adversary (thashArityProblem vp (toyPrims vp.params) pkSeedDist 1),
      SM_DT_TCR_Advantage B = 1 :=
  ⟨_, thashArityCollider_adv_one (prims := toyPrims vp.params) pkSeedDist 1 (tcrTargets_pos vp)
    (default : Adrs) ⟨[false], rfl⟩ ⟨[true], rfl⟩
    (fun h => absurd (List.cons.inj (congrArg Subtype.val h)).1
      (show (true : Bool) ≠ false by decide)) fun _ => rfl⟩

#print axioms thashArityCollider_adv_one
#print axioms toy_thashArity

#print axioms bTcrAr_advantage_eq
#print axioms bTcr_advantage_le_split_add_cross
#print axioms stepTCR_split
#print axioms slhdsa_euf_cma_tcr_split
#print axioms slhdsa_euf_cma_fors_tight_tcr_split

end Reduction
