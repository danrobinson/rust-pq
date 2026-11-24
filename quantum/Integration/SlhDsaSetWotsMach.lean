import Integration.SlhDsaSetTcrMach
namespace Reduction.SetOracle
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open Resources2 Open
open scoped ComplexOrder Kronecker
set_option linter.unusedSectionVars false
variable (S : Sha2Set)
section mach

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

noncomputable def wotsMach (ω₀ : FinFns S.vp.params c)
    (st : SecretTable S.vp (worldPrims ω₀) × List (WotsGame.Entry (worldPrims ω₀)) × (worldPrims ω₀).Y)
    (pk : (worldPrims ω₀).PkSeed) {β : Type}
    (post : ℕ × (worldPrims ω₀).Y × WotsSig S.vp.params (worldPrims ω₀).core →
      OracleComp (Lazy.OSpec (worldPrims ω₀) []ₒ) β) (H : Input S c → (Output S)) :
    Closed (WS (Input S c) (Output S) E) β :=
  qmWotsMach (signRand S optRand₀ ω₀) (hashH S c ω₀ H) (qmForger S c F ω₀ H) st pk post

theorem evalCost_qmSignG (ω₀ : FinFns S.vp.params c) (tbl : SecretTable S.vp (worldPrims ω₀))
    (pk : PublicKeyCore (worldPrims ω₀).core)
    (signO : List Byte → (worldPrims ω₀).Y →
      OracleComp (Lazy.OSpec (worldPrims ω₀) []ₒ) (GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core))
    (k : ℕ) (hk : ∀ m R, IsQueryBoundP (signO m R) (fun t ↦ Lazy.kind t = .hash) k)
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core)).Domain)
    (s : G2Log (worldPrims ω₀)) :
    EvalCost (fun H ↦ (qmSignG (signRand S optRand₀ ω₀) (hashH S c ω₀ H) tbl pk signO t).run s)
      (sgnW k t) := by
  rcases t with n | msg
  · exact EvalCost.const _
  · change EvalCost (fun H ↦ signRand S optRand₀ ω₀ pk >>= fun addrnd ↦
      lazyRandomizer s msg addrnd >>= fun R ↦
        simulateQ (qmImpl (hashH S c ω₀ H) tbl) (signO msg R) >>= fun sig ↦
          (pure (sig, s ++ [(msg, addrnd, R)]) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := Input S c) (Y := (Output S))
        (signRand S optRand₀ ω₀ pk)) fun addrnd ↦
      EvalCost.bind (EvalCost.const (X := Input S c) (Y := (Output S)) (lazyRandomizer s msg addrnd))
        fun R ↦ EvalCost.bind (evalCost_open S c ω₀ tbl _ _ (hk msg R))
          fun sig ↦ EvalCost.const (X := Input S c) (Y := (Output S))
            (pure (sig, s ++ [(msg, addrnd, R)]) : ProbComp _)
    exact h.mono (by simp)

theorem pue_wotsMach (ω₀ : FinFns S.vp.params c)
    (st : SecretTable S.vp (worldPrims ω₀) × List (WotsGame.Entry (worldPrims ω₀)) × (worldPrims ω₀).Y)
    (pk : (worldPrims ω₀).PkSeed) {β : Type}
    (post : ℕ × (worldPrims ω₀).Y × WotsSig S.vp.params (worldPrims ω₀).core →
      OracleComp (Lazy.OSpec (worldPrims ω₀) []ₒ) β) (cp : ℕ)
    (hpost : ∀ x, IsQueryBoundP (post x) (fun t ↦ Lazy.kind t = .hash) cp) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (wotsMach S c optRand₀ F ω₀ st pk post)
      (q + (qs * wotsSignHistHashes S.vp + (wotsAnswerHashes S.vp + cp))) := by
  unfold wotsMach qmWotsMach
  have hS : ∀ m R, IsQueryBoundP (wotsSignFromHistO (gspec := []ₒ) st.2.1
      (⟨pk, st.2.2⟩ : PublicKeyCore (worldPrims ω₀).core) m R) (fun t ↦ Lazy.kind t = .hash)
      (wotsSignHistHashes S.vp) := fun m R ↦
    (wotsSignFromHistO_kindBound .hash st.2.1 _ m R).mono wotsSignHistB_ind_hash
  have h := PUE.bind (PUE.close _ (evalCost_qmSignG S c optRand₀ ω₀ st.1 ⟨pk, st.2.2⟩ _ _ hS)
      (pue_qmForger S c F ω₀ q qs _ hq hqs ⟨pk, st.2.2⟩) []) fun r ↦ by
    have h := PUE.liftU_bind (E := E) (B := fun o _ ↦ (pure o : Closed (WS (Input S c) (Output S) E) β))
      (q := 0)
      (evalCost_open S c ω₀ st.1 _ _ (Lazy.qb_bind _ (wotsAnswerOpen_hashes (gspec := []ₒ) st.2.1
        ⟨pk, st.2.2⟩ r.1.1 r.1.2) hpost)) fun o ↦ PUE.pure o 0
    simp only [bind_pure] at h
    exact h
  refine h.mono ?_
  omega

end mach

/-! ## Delivered statements -/

section deliver

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

abbrev WotsSt (ω₀ : FinFns S.vp.params c) : Type :=
  (SecretTable S.vp (worldPrims ω₀) × List (WotsGame.Entry (worldPrims ω₀)) × (worldPrims ω₀).Y) ×
    List (WotsGame.Entry (worldPrims ω₀))

/-! ### `qrTcrT` (field `tcrT`) -/

theorem wotsTcrT_mach_eq (ω₀ : FinFns S.vp.params c) (st : WotsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed) (T) :
    wotsMach S c optRand₀ F ω₀ st.1 pk
        (fun x ↦ wotsTcrAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2)
        (oracle S { ω₀ with thash := T }) =
      (qrTcrT (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).forge st pk := by
  have h1 := qWotsForge_post_eq (signRand S optRand₀ { ω₀ with thash := T })
    (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T }) st.1 pk
    (fun x ↦ tcrAnswer (prims := worldPrims { ω₀ with thash := T }) pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsTcrAnswerO (gspec := []ₒ) (prims := worldPrims { ω₀ with thash := T })
      pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsTcrAnswerO_tbl (prims := worldPrims { ω₀ with thash := T }) (gspec := []ₒ) st.1.1
      pk st.2 x.1 x.2.1 x.2.2)
  rw [internal_main_withThash, impl_worldPrims_withThash] at h1
  refine Eq.trans ?_ h1.symm
  unfold wotsMach
  qm_kernel_rfl

theorem wotsTcrT_mach_exists (ω₀ : FinFns S.vp.params c) (st : WotsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Input S c → (Output S)) → Closed (WS (Input S c) (Output S) E) (ℕ × (worldPrims ω₀).Y),
      PUE (spec := unifSpec) cnt0 Mach (q + qmWotsTcrTHashes S.vp qs) ∧
      ∀ T, Mach (oracle S { ω₀ with thash := T }) =
        (qrTcrT (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).forge st pk := by
  refine ⟨wotsMach S c optRand₀ F ω₀ st.1 pk
      (fun x ↦ wotsTcrAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2), ?_,
    fun T ↦ wotsTcrT_mach_eq S c optRand₀ pkSeedDist₀ F ω₀ st pk T⟩
  have h := pue_wotsMach S c optRand₀ F ω₀ st.1 pk _ (wotsTcrHashes S.vp)
    (fun x ↦ (wotsTcrAnswerO_kindBound .hash pk st.2 x.1 x.2.1 x.2.2).mono (by
      have h1 : Lazy.ind Lazy.Kind.hash Lazy.Kind.hash = 1 := rfl
      rw [h1, wotsTcrHashes]
      exact le_of_eq (by ring))) q qs hq hqs
  unfold qmWotsTcrTHashes
  exact h

theorem wotsTcrT_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : FinFns S.vp.params c) (st : WotsSt S c ω₀) (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × S.Node)
          (q + qmWotsTcrTHashes S.vp qs),
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × S.Node → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrTcrT (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mach, hP, hE⟩ := wotsTcrT_mach_exists S c optRand₀ pkSeedDist₀ F ω₀ st pk q qs hq hqs
  obtain ⟨Mo, hMo⟩ := hP.exists_model ρ
  exact ⟨Mo, fun T Ev _ ↦ by rw [hMo, hE, hρ]⟩

/-! ### `qrUd` (field `ud`) -/

theorem wotsUd_mach_eq (ω₀ : FinFns S.vp.params c) (st : WotsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed) (T) :
    wotsMach S c optRand₀ F ω₀ st.1 pk
        (fun x ↦ wotsWinO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2)
        (oracle S { ω₀ with thash := T }) =
      (qrUd (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).distinguish st pk := by
  have h1 := qWotsForge_post_eq (signRand S optRand₀ { ω₀ with thash := T })
    (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T }) st.1 pk
    (fun x ↦ WotsGame.win (prims := worldPrims { ω₀ with thash := T }) pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsWinO (gspec := []ₒ) (prims := worldPrims { ω₀ with thash := T })
      pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsWinO_tbl (prims := worldPrims { ω₀ with thash := T }) (gspec := []ₒ) st.1.1
      pk st.2 x.1 x.2.1 x.2.2)
  rw [internal_main_withThash, impl_worldPrims_withThash] at h1
  refine Eq.trans ?_ h1.symm
  unfold wotsMach
  qm_kernel_rfl

theorem wotsUd_mach_exists (ω₀ : FinFns S.vp.params c) (st : WotsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Input S c → (Output S)) → Closed (WS (Input S c) (Output S) E) (Bool),
      PUE (spec := unifSpec) cnt0 Mach (q + qmWotsUdHashes S.vp qs) ∧
      ∀ T, Mach (oracle S { ω₀ with thash := T }) =
        (qrUd (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).distinguish st pk := by
  refine ⟨wotsMach S c optRand₀ F ω₀ st.1 pk
      (fun x ↦ wotsWinO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2), ?_,
    fun T ↦ wotsUd_mach_eq S c optRand₀ pkSeedDist₀ F ω₀ st pk T⟩
  have h := pue_wotsMach S c optRand₀ F ω₀ st.1 pk _ (wotsWinHashes S.vp)
    (fun x ↦ (wotsWinO_kindBound .hash pk st.2 x.1 x.2.1 x.2.2).mono (by
      simp [Lazy.ind, wotsWinHashes])) q qs hq hqs
  unfold qmWotsUdHashes
  exact h

theorem wotsUd_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : FinFns S.vp.params c) (st : WotsSt S c ω₀) (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (Bool) (q + qmWotsUdHashes S.vp qs),
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : Bool → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrUd (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).distinguish st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mach, hP, hE⟩ := wotsUd_mach_exists S c optRand₀ pkSeedDist₀ F ω₀ st pk q qs hq hqs
  obtain ⟨Mo, hMo⟩ := hP.exists_model ρ
  exact ⟨Mo, fun T Ev _ ↦ by rw [hMo, hE, hρ]⟩

/-! ### `qrPre` (field `pre`) -/

theorem wotsPre_mach_eq (ω₀ : FinFns S.vp.params c) (st : WotsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed) (T) :
    wotsMach S c optRand₀ F ω₀ st.1 pk
        (fun x ↦ wotsPreAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2)
        (oracle S { ω₀ with thash := T }) =
      (qrPre (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).invert st pk := by
  have h1 := qWotsForge_post_eq (signRand S optRand₀ { ω₀ with thash := T })
    (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T }) st.1 pk
    (fun x ↦ preAnswer (prims := worldPrims { ω₀ with thash := T }) pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsPreAnswerO (gspec := []ₒ) (prims := worldPrims { ω₀ with thash := T })
      pk st.2 x.1 x.2.1 x.2.2)
    (fun x ↦ wotsPreAnswerO_tbl (prims := worldPrims { ω₀ with thash := T }) (gspec := []ₒ) st.1.1
      pk st.2 x.1 x.2.1 x.2.2)
  rw [internal_main_withThash, impl_worldPrims_withThash] at h1
  refine Eq.trans ?_ h1.symm
  unfold wotsMach
  qm_kernel_rfl

theorem wotsPre_mach_exists (ω₀ : FinFns S.vp.params c) (st : WotsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Input S c → (Output S)) → Closed (WS (Input S c) (Output S) E) (ℕ × S.Node),
      PUE (spec := unifSpec) cnt0 Mach (q + qmWotsPreHashes S.vp qs) ∧
      ∀ T, Mach (oracle S { ω₀ with thash := T }) =
        (qrPre (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).invert st pk := by
  refine ⟨wotsMach S c optRand₀ F ω₀ st.1 pk
      (fun x ↦ wotsPreAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2), ?_,
    fun T ↦ wotsPre_mach_eq S c optRand₀ pkSeedDist₀ F ω₀ st pk T⟩
  have h := pue_wotsMach S c optRand₀ F ω₀ st.1 pk _ (Resources2.wotsPreHashes S.vp)
    (fun x ↦ (wotsPreAnswerO_kindBound .hash pk st.2 x.1 x.2.1 x.2.2).mono (by
      simp [Lazy.ind, Resources2.wotsPreHashes])) q qs hq hqs
  unfold qmWotsPreHashes
  exact h

theorem wotsPre_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : FinFns S.vp.params c) (st : WotsSt S c ω₀) (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × S.Node) (q + qmWotsPreHashes S.vp qs),
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × S.Node → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrPre (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).invert st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mach, hP, hE⟩ := wotsPre_mach_exists S c optRand₀ pkSeedDist₀ F ω₀ st pk q qs hq hqs
  obtain ⟨Mo, hMo⟩ := hP.exists_model ρ
  exact ⟨Mo, fun T Ev _ ↦ by rw [hMo, hE, hρ]⟩

end deliver

section consumer

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem tcrT_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : FinFns S.vp.params c) (st : Open.RState S.vp (worldPrims ω₀))
        (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × S.Node)
          (q + qmWotsTcrTHashes S.vp qs),
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × S.Node → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrTcrT (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀ :=
  fun ω₀ st pk ↦ wotsTcrT_hModel S c optRand₀ pkSeedDist₀ F q qs hq hqs ω₀ st pk

end consumer
end Reduction.SetOracle
#print axioms Reduction.SetOracle.wotsPre_hModel
#print axioms Reduction.SetOracle.wotsUd_hModel
#print axioms Reduction.SetOracle.tcrT_hModel
