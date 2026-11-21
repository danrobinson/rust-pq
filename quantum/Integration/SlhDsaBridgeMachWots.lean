import Integration.SlhDsaBridgeMach
import Reduction.Open.Wots
import Reduction.Open.Phase1Wots

/-!
# The WOTS reduction machines (`qrTcrT`, `qrUd`, `qrPre`) as `PUE` families

NOT part of the default target; compiled by hand like `scripts/check-integration.sh` step 3.

Same recipe as the class-TCR machine (`SlhDsaBridgeMach.lean`).  The three WOTS second phases
share `qWotsForge` (forger run against the history-based signing oracle, `wotsAnswer`
extraction) and differ by a post-processing (`tcrAnswer`, `preAnswer`, `WotsGame.win`), each with
an open form in `security/` (`wotsTcrAnswerO`, `wotsPreAnswerO`, `wotsWinO`).

* `qmSignG`, `qmSignG_ideal`: the signing oracle with an arbitrary open signer (per-query lemma
  as hypothesis); `qmWotsMach` (generic in `prims` and in the open post-processing `post`);
  `qWotsForge_post_eq` (Part A).
* `wotsMach`, `wotsMach_encΩ`, `pue_wotsMach` (generic in the post-processing).
* Delivered per machine: `wotsTcrT_mach_exists`, `wotsTcrT_hModel`, `qmWotsTcrTHashes_openCounts128s`;
  the same for `Ud` (`qrUd`, `distinguish`) and `Pre` (`qrPre`, `invert`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Reduction

open Resources2 Open

section generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {W : Type} [Fintype W]

/-- The `G2` signing oracle with an arbitrary OPEN signer `signO`, interpreted by `qmImpl`. -/
noncomputable def qmSignG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (ans : QueryImpl (publicHashSpec prims.core) Id) (tbl : SecretTable vp prims)
    (pk : PublicKeyCore prims.core)
    (signO : List Byte → prims.Y →
      OracleComp (Lazy.OSpec prims []ₒ) (GeneralScheme.SignatureCore vp prims.core)) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
    fun msg => StateT.mk fun log => do
      let addrnd ← optRand pk
      let R ← lazyRandomizer log msg addrnd
      let sig ← simulateQ (qmImpl ans tbl) (signO msg R)
      pure (sig, log ++ [(msg, addrnd, R)])

theorem qmSignG_ideal (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core)
    (signO : List Byte → prims.Y →
      OracleComp (Lazy.OSpec prims []ₒ) (GeneralScheme.SignatureCore vp prims.core))
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core)
    (h : ∀ m R, simulateQ (Lazy.tblImpl (gspec := []ₒ) (PublicHash.impl prims) tbl) (signO m R) =
      pure (signR m R)) :
    qmSignG optRand (PublicHash.impl prims) tbl pk signO =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
        g2SignOracle optRand pk signR := by
  unfold qmSignG
  congr 1
  funext msg
  refine StateT.ext fun log => ?_
  have h' : ∀ R, simulateQ (qmImpl (PublicHash.impl prims) tbl) (signO msg R) =
      pure (signR msg R) := fun R ↦ by rw [qmImpl_bridge, h, simulateQ_qmToProb_pure]
  simp only [StateT.run_mk]
  simp [g2SignOracle, h']

/-- **The WOTS second phase in open form**, generic in the open post-processing `post`. -/
noncomputable def qmWotsMach (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (ans : QueryImpl (publicHashSpec prims.core) Id)
    (main : PublicKeyCore prims.core →
      QOC W (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
        (List Byte × GeneralScheme.SignatureCore vp prims.core))
    (st : SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) (pkSeed : prims.PkSeed)
    {β : Type} (post : ℕ × prims.Y × WotsSig vp.params prims.core →
      OracleComp (Lazy.OSpec prims []ₒ) β) : Closed W β :=
  close (qmSignG optRand ans st.1 ⟨pkSeed, st.2.2⟩ (wotsSignFromHistO st.2.1 ⟨pkSeed, st.2.2⟩))
      (main ⟨pkSeed, st.2.2⟩) [] >>= fun r ↦
    liftU (simulateQ (qmImpl ans st.1)
      (wotsAnswerOpen st.2.1 ⟨pkSeed, st.2.2⟩ r.1.1 r.1.2 >>= post))

/-- **Part A (WOTS).** -/
theorem qWotsForge_post_eq (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    {pkSeedDist : ProbComp prims.PkSeed}
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y) (pkSeed : prims.PkSeed)
    {β : Type} (P : ℕ × prims.Y × WotsSig vp.params prims.core → β)
    (post : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims []ₒ) β)
    (hpost : ∀ x, simulateQ (Lazy.tblImpl (gspec := []ₒ) (PublicHash.impl prims) st.1) (post x) =
      pure (P x)) :
    qWotsForge Q st pkSeed >>= (fun x ↦ liftU (pure (P x))) =
      qmWotsMach optRand (PublicHash.impl prims) Q.main st pkSeed post := by
  unfold qmWotsMach qWotsForge
  rw [qmSignG_ideal optRand st.1 _ _ _ (fun m R ↦ wotsSignFromHistO_tbl st.1 st.2.1 _ m R)]
  rw [bind_assoc]
  refine bind_congr fun r ↦ ?_
  rw [liftU_pure, pure_bind, qmImpl_bridge, simulateQ_bind, wotsAnswerOpen_tbl, pure_bind,
    hpost, simulateQ_qmToProb_pure]

end generic

section mach

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- The WOTS second-phase family for the fixed world `ω₀`, state `st`, seed `pk` and open
post-processing `post`, as a function of the port function. -/
noncomputable def wotsMach (ω₀ : Ω128 c)
    (st : SecretTable Link.vp (primsΩ ω₀) × List (WotsGame.Entry (primsΩ ω₀)) × (primsΩ ω₀).Y)
    (pk : (primsΩ ω₀).PkSeed) {β : Type}
    (post : ℕ × (primsΩ ω₀).Y × WotsSig Link.vp.params (primsΩ ω₀).core →
      OracleComp (Lazy.OSpec (primsΩ ω₀) []ₒ) β) (H : EncX c → EncY) :
    Closed (WS (EncX c) EncY E) β :=
  qmWotsMach (optRandOf c optRand₀ ω₀) (hashH c ω₀ H) (qmForger c F ω₀ H) st pk post

theorem evalCost_qmSignG (ω₀ : Ω128 c) (tbl : SecretTable Link.vp (primsΩ ω₀))
    (pk : PublicKeyCore (primsΩ ω₀).core)
    (signO : List Byte → (primsΩ ω₀).Y →
      OracleComp (Lazy.OSpec (primsΩ ω₀) []ₒ) (GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core))
    (k : ℕ) (hk : ∀ m R, IsQueryBoundP (signO m R) (fun t ↦ Lazy.kind t = .hash) k)
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core)).Domain)
    (s : G2Log (primsΩ ω₀)) :
    EvalCost (fun H ↦ (qmSignG (optRandOf c optRand₀ ω₀) (hashH c ω₀ H) tbl pk signO t).run s)
      (sgnW k t) := by
  rcases t with n | msg
  · exact EvalCost.const _
  · change EvalCost (fun H ↦ optRandOf c optRand₀ ω₀ pk >>= fun addrnd ↦
      lazyRandomizer s msg addrnd >>= fun R ↦
        simulateQ (qmImpl (hashH c ω₀ H) tbl) (signO msg R) >>= fun sig ↦
          (pure (sig, s ++ [(msg, addrnd, R)]) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := EncX c) (Y := EncY)
        (optRandOf c optRand₀ ω₀ pk)) fun addrnd ↦
      EvalCost.bind (EvalCost.const (X := EncX c) (Y := EncY) (lazyRandomizer s msg addrnd))
        fun R ↦ EvalCost.bind (evalCost_open c ω₀ tbl _ _ (hk msg R))
          fun sig ↦ EvalCost.const (X := EncX c) (Y := EncY)
            (pure (sig, s ++ [(msg, addrnd, R)]) : ProbComp _)
    exact h.mono (by simp)

/-- **`PUE` for the WOTS family**, any post-processing with at most `cp` hash queries. -/
theorem pue_wotsMach (ω₀ : Ω128 c)
    (st : SecretTable Link.vp (primsΩ ω₀) × List (WotsGame.Entry (primsΩ ω₀)) × (primsΩ ω₀).Y)
    (pk : (primsΩ ω₀).PkSeed) {β : Type}
    (post : ℕ × (primsΩ ω₀).Y × WotsSig Link.vp.params (primsΩ ω₀).core →
      OracleComp (Lazy.OSpec (primsΩ ω₀) []ₒ) β) (cp : ℕ)
    (hpost : ∀ x, IsQueryBoundP (post x) (fun t ↦ Lazy.kind t = .hash) cp) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (wotsMach c optRand₀ F ω₀ st pk post)
      (q + (qs * wotsSignHistHashes Link.vp + (wotsAnswerHashes Link.vp + cp))) := by
  unfold wotsMach qmWotsMach
  have hS : ∀ m R, IsQueryBoundP (wotsSignFromHistO (gspec := []ₒ) st.2.1
      (⟨pk, st.2.2⟩ : PublicKeyCore (primsΩ ω₀).core) m R) (fun t ↦ Lazy.kind t = .hash)
      (wotsSignHistHashes Link.vp) := fun m R ↦
    (wotsSignFromHistO_kindBound .hash st.2.1 _ m R).mono wotsSignHistB_ind_hash
  have h := PUE.bind (PUE.close _ (evalCost_qmSignG c optRand₀ ω₀ st.1 ⟨pk, st.2.2⟩ _ _ hS)
      (pue_qmForger c F ω₀ q qs _ hq hqs ⟨pk, st.2.2⟩) []) fun r ↦ by
    have h := PUE.liftU_bind (E := E) (B := fun o _ ↦ (pure o : Closed (WS (EncX c) EncY E) β))
      (q := 0)
      (evalCost_open c ω₀ st.1 _ _ (Lazy.qb_bind _ (wotsAnswerOpen_hashes (gspec := []ₒ) st.2.1
        ⟨pk, st.2.2⟩ r.1.1 r.1.2) hpost)) fun o ↦ PUE.pure o 0
    simp only [bind_pure] at h
    exact h
  refine h.mono ?_
  omega

end mach

/-! ## Delivered statements -/

section deliver

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- The state of the three WOTS reduction adversaries. -/
abbrev WotsSt (ω₀ : Ω128 c) : Type :=
  (SecretTable Link.vp (primsΩ ω₀) × List (WotsGame.Entry (primsΩ ω₀)) × (primsΩ ω₀).Y) ×
    List (WotsGame.Entry (primsΩ ω₀))

/-! ### `qrTcrT` (field `tcrT`) -/

/-- Own hash evaluations of the second phase of `qrTcrT` (`wotsTcrT_phase2_open_hashes`). -/
def qmWotsTcrTHashes (vp : ValidatedParams) (qs : ℕ) : ℕ :=
  qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsTcrHashes vp)

theorem qmWotsTcrTHashes_openCounts128s (qs : ℕ) :
    qmWotsTcrTHashes Link.vp qs = (openCounts128s qs).tcrT := by
  unfold qmWotsTcrTHashes
  have h : wotsTcrHashes Link.vp = 16800 := by decide
  rw [wotsSignHistHashes_128s, wotsAnswerHashes_128s, h]
  simp only [openCounts128s]

theorem wotsTcrT_mach_eq (ω₀ : Ω128 c) (st : WotsSt c ω₀) (pk : (primsΩ ω₀).PkSeed) (T) :
    wotsMach c optRand₀ F ω₀ st.1 pk
        (fun x ↦ wotsTcrAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2)
        (encΩ { ω₀ with thash := T }) =
      (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).forge st pk := by
  have h1 := qWotsForge_post_eq (optRandOf c optRand₀ { ω₀ with thash := T })
    (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T }) st.1 pk
    (fun x ↦ tcrAnswer (prims := primsΩ { ω₀ with thash := T }) pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsTcrAnswerO (gspec := []ₒ) (prims := primsΩ { ω₀ with thash := T })
      pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsTcrAnswerO_tbl (prims := primsΩ { ω₀ with thash := T }) (gspec := []ₒ) st.1.1
      pk st.2 x.1 x.2.1 x.2.2)
  rw [internalΩ_main_withThash, impl_primsΩ_withThash] at h1
  refine Eq.trans ?_ h1.symm
  unfold wotsMach
  qm_kernel_rfl

/-- **`qrTcrT`, primitive form.** -/
theorem wotsTcrT_mach_exists (ω₀ : Ω128 c) (st : WotsSt c ω₀) (pk : (primsΩ ω₀).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (EncX c → EncY) → Closed (WS (EncX c) EncY E) (ℕ × (primsΩ ω₀).Y),
      PUE (spec := unifSpec) cnt0 Mach (q + qmWotsTcrTHashes Link.vp qs) ∧
      ∀ T, Mach (encΩ { ω₀ with thash := T }) =
        (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).forge st pk := by
  refine ⟨wotsMach c optRand₀ F ω₀ st.1 pk
      (fun x ↦ wotsTcrAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2), ?_,
    fun T ↦ wotsTcrT_mach_eq c optRand₀ pkSeedDist₀ F ω₀ st pk T⟩
  have h := pue_wotsMach c optRand₀ F ω₀ st.1 pk _ (wotsTcrHashes Link.vp)
    (fun x ↦ (wotsTcrAnswerO_kindBound .hash pk st.2 x.1 x.2.1 x.2.2).mono (by
      have h1 : Lazy.ind Lazy.Kind.hash Lazy.Kind.hash = 1 := rfl
      rw [h1, wotsTcrHashes]
      exact le_of_eq (by ring))) q qs hq hqs
  unfold qmWotsTcrTHashes
  exact h

/-- **`qrTcrT`, model form** (`tcr_hModel` shape, state = the adversary's `ρ₀ = F.ρ₀`). -/
theorem wotsTcrT_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : Ω128 c) (st : WotsSt c ω₀) (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n)
          (q + qmWotsTcrTHashes Link.vp qs),
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mach, hP, hE⟩ := wotsTcrT_mach_exists c optRand₀ pkSeedDist₀ F ω₀ st pk q qs hq hqs
  obtain ⟨Mo, hMo⟩ := hP.exists_model ρ
  exact ⟨Mo, fun T Ev _ ↦ by rw [hMo, hE, hρ]⟩

/-! ### `qrUd` (field `ud`) -/

/-- Own hash evaluations of the second phase of `qrUd` (`wotsUd_phase2_open_hashes`). -/
def qmWotsUdHashes (vp : ValidatedParams) (qs : ℕ) : ℕ :=
  qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsWinHashes vp)

theorem qmWotsUdHashes_openCounts128s (qs : ℕ) :
    qmWotsUdHashes Link.vp qs = (openCounts128s qs).ud := by
  unfold qmWotsUdHashes
  have h : wotsWinHashes Link.vp = 525 := by decide
  rw [wotsSignHistHashes_128s, wotsAnswerHashes_128s, h]
  simp only [openCounts128s]

theorem wotsUd_mach_eq (ω₀ : Ω128 c) (st : WotsSt c ω₀) (pk : (primsΩ ω₀).PkSeed) (T) :
    wotsMach c optRand₀ F ω₀ st.1 pk
        (fun x ↦ wotsWinO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2)
        (encΩ { ω₀ with thash := T }) =
      (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).distinguish st pk := by
  have h1 := qWotsForge_post_eq (optRandOf c optRand₀ { ω₀ with thash := T })
    (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T }) st.1 pk
    (fun x ↦ WotsGame.win (prims := primsΩ { ω₀ with thash := T }) pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsWinO (gspec := []ₒ) (prims := primsΩ { ω₀ with thash := T })
      pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsWinO_tbl (prims := primsΩ { ω₀ with thash := T }) (gspec := []ₒ) st.1.1
      pk st.2 x.1 x.2.1 x.2.2)
  rw [internalΩ_main_withThash, impl_primsΩ_withThash] at h1
  refine Eq.trans ?_ h1.symm
  unfold wotsMach
  qm_kernel_rfl

/-- **`qrUd`, primitive form.** -/
theorem wotsUd_mach_exists (ω₀ : Ω128 c) (st : WotsSt c ω₀) (pk : (primsΩ ω₀).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (EncX c → EncY) → Closed (WS (EncX c) EncY E) (Bool),
      PUE (spec := unifSpec) cnt0 Mach (q + qmWotsUdHashes Link.vp qs) ∧
      ∀ T, Mach (encΩ { ω₀ with thash := T }) =
        (qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).distinguish st pk := by
  refine ⟨wotsMach c optRand₀ F ω₀ st.1 pk
      (fun x ↦ wotsWinO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2), ?_,
    fun T ↦ wotsUd_mach_eq c optRand₀ pkSeedDist₀ F ω₀ st pk T⟩
  have h := pue_wotsMach c optRand₀ F ω₀ st.1 pk _ (wotsWinHashes Link.vp)
    (fun x ↦ (wotsWinO_kindBound .hash pk st.2 x.1 x.2.1 x.2.2).mono (by
      simp [Lazy.ind, wotsWinHashes])) q qs hq hqs
  unfold qmWotsUdHashes
  exact h

/-- **`qrUd`, model form** (`tcr_hModel` shape, state = the adversary's `ρ₀ = F.ρ₀`). -/
theorem wotsUd_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : Ω128 c) (st : WotsSt c ω₀) (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (Bool) (q + qmWotsUdHashes Link.vp qs),
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : Bool → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrUd (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).distinguish st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mach, hP, hE⟩ := wotsUd_mach_exists c optRand₀ pkSeedDist₀ F ω₀ st pk q qs hq hqs
  obtain ⟨Mo, hMo⟩ := hP.exists_model ρ
  exact ⟨Mo, fun T Ev _ ↦ by rw [hMo, hE, hρ]⟩

/-! ### `qrPre` (field `pre`) -/

/-- Own hash evaluations of the second phase of `qrPre` (`wotsPre_phase2_open_hashes`). -/
def qmWotsPreHashes (vp : ValidatedParams) (qs : ℕ) : ℕ :=
  qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + Resources2.wotsPreHashes vp)

theorem qmWotsPreHashes_openCounts128s (qs : ℕ) :
    qmWotsPreHashes Link.vp qs = (openCounts128s qs).pre := by
  unfold qmWotsPreHashes
  have h : Resources2.wotsPreHashes Link.vp = 560 := by decide
  rw [wotsSignHistHashes_128s, wotsAnswerHashes_128s, h]
  simp only [openCounts128s]

theorem wotsPre_mach_eq (ω₀ : Ω128 c) (st : WotsSt c ω₀) (pk : (primsΩ ω₀).PkSeed) (T) :
    wotsMach c optRand₀ F ω₀ st.1 pk
        (fun x ↦ wotsPreAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2)
        (encΩ { ω₀ with thash := T }) =
      (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).invert st pk := by
  have h1 := qWotsForge_post_eq (optRandOf c optRand₀ { ω₀ with thash := T })
    (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T }) st.1 pk
    (fun x ↦ preAnswer (prims := primsΩ { ω₀ with thash := T }) pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsPreAnswerO (gspec := []ₒ) (prims := primsΩ { ω₀ with thash := T })
      pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsPreAnswerO_tbl (prims := primsΩ { ω₀ with thash := T }) (gspec := []ₒ) st.1.1
      pk st.2 x.1 x.2.1 x.2.2)
  rw [internalΩ_main_withThash, impl_primsΩ_withThash] at h1
  refine Eq.trans ?_ h1.symm
  unfold wotsMach
  qm_kernel_rfl

/-- **`qrPre`, primitive form.** -/
theorem wotsPre_mach_exists (ω₀ : Ω128 c) (st : WotsSt c ω₀) (pk : (primsΩ ω₀).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (EncX c → EncY) → Closed (WS (EncX c) EncY E) (ℕ × Bytes Link.vp.params.n),
      PUE (spec := unifSpec) cnt0 Mach (q + qmWotsPreHashes Link.vp qs) ∧
      ∀ T, Mach (encΩ { ω₀ with thash := T }) =
        (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).invert st pk := by
  refine ⟨wotsMach c optRand₀ F ω₀ st.1 pk
      (fun x ↦ wotsPreAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2), ?_,
    fun T ↦ wotsPre_mach_eq c optRand₀ pkSeedDist₀ F ω₀ st pk T⟩
  have h := pue_wotsMach c optRand₀ F ω₀ st.1 pk _ (Resources2.wotsPreHashes Link.vp)
    (fun x ↦ (wotsPreAnswerO_kindBound .hash pk st.2 x.1 x.2.1 x.2.2).mono (by
      simp [Lazy.ind, Resources2.wotsPreHashes])) q qs hq hqs
  unfold qmWotsPreHashes
  exact h

/-- **`qrPre`, model form** (`tcr_hModel` shape, state = the adversary's `ρ₀ = F.ρ₀`). -/
theorem wotsPre_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : Ω128 c) (st : WotsSt c ω₀) (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n) (q + qmWotsPreHashes Link.vp qs),
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).invert st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mach, hP, hE⟩ := wotsPre_mach_exists c optRand₀ pkSeedDist₀ F ω₀ st pk q qs hq hqs
  obtain ⟨Mo, hMo⟩ := hP.exists_model ρ
  exact ⟨Mo, fun T Ev _ ↦ by rw [hMo, hE, hρ]⟩

end deliver

end Reduction

#print axioms Reduction.qWotsForge_post_eq
#print axioms Reduction.pue_wotsMach
#print axioms Reduction.wotsTcrT_mach_exists
#print axioms Reduction.wotsTcrT_hModel
#print axioms Reduction.qmWotsTcrTHashes_openCounts128s
#print axioms Reduction.wotsUd_mach_exists
#print axioms Reduction.wotsUd_hModel
#print axioms Reduction.qmWotsUdHashes_openCounts128s
#print axioms Reduction.wotsPre_mach_exists
#print axioms Reduction.wotsPre_hModel
#print axioms Reduction.qmWotsPreHashes_openCounts128s

namespace Reduction

section consumer

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- **The hypothesis `hModel` of `tcrT_term` (`Integration/SlhDsaBridgeTcrT.lean`), verbatim**,
with `q' = q + qmWotsTcrTHashes Link.vp qs` (`= q + (openCounts128s qs).tcrT`). -/
theorem tcrT_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : Ω128 c) (st : Open.RState Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n)
          (q + qmWotsTcrTHashes Link.vp qs),
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀ :=
  fun ω₀ st pk ↦ wotsTcrT_hModel c optRand₀ pkSeedDist₀ F q qs hq hqs ω₀ st pk

end consumer

end Reduction

#print axioms Reduction.tcrT_hModel
