import Integration.SlhDsaSetTcrMach
namespace Reduction.SetOracle
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker
set_option linter.unusedSectionVars false
variable (S : Sha2Set)
section mach

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

/-- State of the FORS first phase (table, sampled targets, leaf images). -/
abbrev ForsSt (ω₀ : FinFns S.vp.params c) : Type :=
  SecretTable S.vp (worldPrims ω₀) × List ((worldPrims ω₀).AdrsKey × (worldPrims ω₀).Y) ×
    List (worldPrims ω₀).Y

/-- **The FORS second-phase machine family** for the fixed world `ω₀`, state `st`, seed `pk`. -/
noncomputable def forsMach (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed)
    (H : Input S c → (Output S)) : Closed (WS (Input S c) (Output S) E) ((ℕ × (worldPrims ω₀).Y) × List ℕ) :=
  fRun (signRand S optRand₀ ω₀) (hashH S c ω₀ H) (qmForger S c F ω₀ H) st pk

theorem forsMach_oracle (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed) (T) :
    forsMach S c optRand₀ F ω₀ st pk (oracle S { ω₀ with thash := T }) =
      qFindRun (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T }) st pk := by
  have h1 := qFindRun_eq_fRun (signRand S optRand₀ { ω₀ with thash := T })
    (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T }) st pk
  rw [internal_main_withThash, impl_worldPrims_withThash] at h1
  refine Eq.trans ?_ h1.symm
  unfold forsMach
  qm_kernel_rfl

end mach
section pueFors

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

attribute [local instance] Lazy.openQ Lazy.closedQ

open Resources2

theorem evalCost_fImpl (ω₀ : FinFns S.vp.params c) (tbl : SecretTable S.vp (worldPrims ω₀))
    (tg : List ((worldPrims ω₀).AdrsKey × (worldPrims ω₀).Y))
    (t : (Lazy.OSpec (worldPrims ω₀) (forsG (worldPrims ω₀))).Domain) (s : List ℕ) :
    EvalCost (fun H ↦ (fImpl (hashH S c ω₀ H) tbl tg t).run s)
      (if Lazy.kind t = .hash then 1 else 0) := by
  rcases t with n | t | d | q
  · exact EvalCost.const _
  · exact EvalCost.const _
  · exact EvalCost.const _
  · have e : (fun H ↦ (fImpl (hashH S c ω₀ H) tbl tg (.inr (.inr (.inr q)))).run s) =
        fun H ↦ (fun y ↦ (y, s)) <$> (pure (hashH S c ω₀ H q) : ProbComp _) := by
      funext H
      simp [fImpl]
    rw [e]
    exact ((evalCost_hashH S c ω₀ q).map _).mono (by simp [Lazy.kind])

theorem evalCost_fOpen (ω₀ : FinFns S.vp.params c) (tbl : SecretTable S.vp (worldPrims ω₀))
    (tg : List ((worldPrims ω₀).AdrsKey × (worldPrims ω₀).Y)) {γ : Type}
    (P : OracleComp (Lazy.OSpec (worldPrims ω₀) (forsG (worldPrims ω₀))) γ) (k : ℕ)
    (hP : IsQueryBoundP P (fun t ↦ Lazy.kind t = .hash) k) (s : List ℕ) :
    EvalCost (fun H ↦ (simulateQ (fImpl (hashH S c ω₀ H) tbl tg) P).run s) k :=
  evalCost_simulateQ_run (fun H ↦ fImpl (hashH S c ω₀ H) tbl tg) _
    (evalCost_fImpl S c ω₀ tbl tg) P k (wCount_of_isQueryBoundP _ P k hP) s

theorem fSignOpen_hashes (ω₀ : FinFns S.vp.params c) (pk : PublicKeyCore (worldPrims ω₀).core)
    (ys : List (worldPrims ω₀).Y) (m : List Byte) (R : (worldPrims ω₀).Y) :
    IsQueryBoundP (fSignOpen pk ys m R) (fun t ↦ Lazy.kind t = .hash)
      (forsSignHashes S.vp + 1) := by
  unfold fSignOpen
  refine Lazy.qb_bind _ ((forsSignOpen_kindBound .hash pk ys m R).mono ?_) fun sig ↦
    Lazy.qb_bind _ (m := 0) (Lazy.query_kindBound .hash _) fun d ↦ isQueryBoundP_pure _ _ _
  simpa [Lazy.ind] using forsSignB_hash (vp := S.vp)

theorem fAnswerO_hashes (ω₀ : FinFns S.vp.params c) (pk : PublicKeyCore (worldPrims ω₀).core)
    (ys : List (worldPrims ω₀).Y) (opened : List (Adrs × ℕ)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core) :
    IsQueryBoundP (fAnswerO pk ys opened msg sig) (fun t ↦ Lazy.kind t = .hash)
      (1 + S.vp.params.k) := by
  unfold fAnswerO
  refine (Lazy.qb_bind _ (Lazy.query_kindBound .hash _) fun digest ↦
    Lazy.qb_bind _ (m := 0) (Lazy.qb_ofFnM _ _ (Lazy.ind .hash .hash) fun i ↦
      Lazy.query_kindBound .hash _) fun imgs ↦ isQueryBoundP_pure _ _ _).mono ?_
  simp only [Lazy.ind]
  split <;> simp

theorem evalCost_fSignS (ω₀ : FinFns S.vp.params c) (tbl : SecretTable S.vp (worldPrims ω₀))
    (tg : List ((worldPrims ω₀).AdrsKey × (worldPrims ω₀).Y)) (ys : List (worldPrims ω₀).Y)
    (pkSeed : (worldPrims ω₀).PkSeed) (root : (worldPrims ω₀).Y)
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore S.vp (worldPrims ω₀).core)).Domain)
    (s : G2Log (worldPrims ω₀) × List ℕ × List (Adrs × ℕ)) :
    EvalCost (fun H ↦
      (fSignS (signRand S optRand₀ ω₀) (hashH S c ω₀ H) tbl tg ys pkSeed root t).run s)
      (sgnW (forsSignHashes S.vp + 1) t) := by
  rcases t with n | msg
  · exact EvalCost.const _
  · change EvalCost (fun H ↦ signRand S optRand₀ ω₀ ⟨pkSeed, root⟩ >>= fun addrnd ↦
      lazyRandomizer s.1 msg addrnd >>= fun R ↦
        (simulateQ (fImpl (hashH S c ω₀ H) tbl tg) (fSignOpen ⟨pkSeed, root⟩ ys msg R)).run s.2.1 >>=
          fun r ↦ (pure (r.1.1, (s.1 ++ [(msg, addrnd, R)], r.2, s.2.2 ++ r.1.2)) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := Input S c) (Y := (Output S))
        (signRand S optRand₀ ω₀ ⟨pkSeed, root⟩)) fun addrnd ↦
      EvalCost.bind (EvalCost.const (X := Input S c) (Y := (Output S)) (lazyRandomizer s.1 msg addrnd))
        fun R ↦ EvalCost.bind (evalCost_fOpen S c ω₀ tbl tg _ _
          (fSignOpen_hashes S c ω₀ ⟨pkSeed, root⟩ ys msg R) s.2.1)
          fun r ↦ EvalCost.const (X := Input S c) (Y := (Output S))
            (pure (r.1.1, (s.1 ++ [(msg, addrnd, R)], r.2, s.2.2 ++ r.1.2)) : ProbComp _)
    exact h.mono (by simp)

/-- **`PUE`.**  The FORS second-phase machine family makes at most `q + forsMHashes qs` port
calls plus evaluations on every path. -/
theorem pue_forsMach (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (forsMach S c optRand₀ F ω₀ st pk) (q + forsMHashes S.vp qs) := by
  unfold forsMach fRun
  have hB : ∀ root : (worldPrims ω₀).Y, PUE (spec := unifSpec) cnt0 (fun H ↦
      close (fSignS (signRand S optRand₀ ω₀) (hashH S c ω₀ H) st.1 st.2.1 st.2.2 pk root)
          (qmForger S c F ω₀ H ⟨pk, root⟩) ([], [], []) >>= fun z ↦
        liftU ((simulateQ (fImpl (hashH S c ω₀ H) st.1 st.2.1)
          (fAnswerO ⟨pk, root⟩ st.2.2 z.2.2.2 z.1.1 z.1.2)).run z.2.2.1))
      (q + qs * (forsSignHashes S.vp + 1) + (1 + S.vp.params.k)) := by
    intro root
    refine PUE.bind (PUE.close _ (evalCost_fSignS S c optRand₀ ω₀ st.1 st.2.1 st.2.2 pk root)
      (pue_qmForger S c F ω₀ q qs _ hq hqs ⟨pk, root⟩) _) fun z ↦ ?_
    have h := PUE.liftU_bind (E := E) (B := fun o _ ↦ (pure o : Closed (WS (Input S c) (Output S) E) _))
      (q := 0) (evalCost_fOpen S c ω₀ st.1 st.2.1 _ _
        (fAnswerO_hashes S c ω₀ ⟨pk, root⟩ st.2.2 z.2.2.2 z.1.1 z.1.2) z.2.2.1) fun o ↦ PUE.pure o 0
    simpa using h
  have h := PUE.liftU_bind (evalCost_open S c ω₀ st.1 _ _ (keygen_hashes S c ω₀ pk)) hB
  refine h.mono ?_
  unfold forsMHashes
  omega

end pueFors

/-! ## Delivered statements -/

section deliver

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

/-- The SM-TCR (FORS) second-phase machine family. -/
noncomputable def forsTcrMach (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed)
    (H : Input S c → (Output S)) : Closed (WS (Input S c) (Output S) E) (ℕ × (worldPrims ω₀).Y) :=
  forsMach S c optRand₀ F ω₀ st pk H >>= fun r ↦ liftU (pure (r.1.1, r.1.2))

/-- The SM-DSPR (FORS) second-phase machine family. -/
noncomputable def forsDsprMach (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed)
    (H : Input S c → (Output S)) : Closed (WS (Input S c) (Output S) E) (ℕ × Bool) :=
  forsMach S c optRand₀ F ω₀ st pk H >>= fun r ↦
    liftU (pure (r.1.1, decide (((st.2.1[r.1.1]?.map Prod.snd).getD default) ≠ r.1.2 ∨
      r.1.1 ∈ r.2)))

theorem forsTcrMach_oracle (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed) (T) :
    forsTcrMach S c optRand₀ F ω₀ st pk (oracle S { ω₀ with thash := T }) =
      (qToTcr (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).forge st pk := by
  unfold forsTcrMach
  rw [forsMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ st pk T]
  rfl

theorem forsDsprMach_oracle (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed) (T) :
    forsDsprMach S c optRand₀ F ω₀ st pk (oracle S { ω₀ with thash := T }) =
      (qToDspr (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).guess st pk := by
  unfold forsDsprMach
  rw [forsMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ st pk T]
  rfl

theorem pue_forsTcrMach (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (forsTcrMach S c optRand₀ F ω₀ st pk) (q + forsMHashes S.vp qs) := by
  have h := PUE.bind (q₂ := 0) (pue_forsMach S c optRand₀ F ω₀ st pk q qs hq hqs)
    (B := fun r _ ↦ (pure (r.1.1, r.1.2) : Closed (WS (Input S c) (Output S) E) _))
    fun r ↦ PUE.pure _ 0
  unfold forsTcrMach
  simpa using h

theorem pue_forsDsprMach (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (forsDsprMach S c optRand₀ F ω₀ st pk) (q + forsMHashes S.vp qs) := by
  have h := PUE.bind (q₂ := 0) (pue_forsMach S c optRand₀ F ω₀ st pk q qs hq hqs)
    (B := fun r _ ↦ (pure (r.1.1, decide (((st.2.1[r.1.1]?.map Prod.snd).getD default) ≠ r.1.2 ∨
      r.1.1 ∈ r.2)) : Closed (WS (Input S c) (Output S) E) _))
    fun r ↦ PUE.pure _ 0
  unfold forsDsprMach
  simpa using h

/-- **Machine family, `tcrFv`**: one `PUE` family in the port function equal, at the port
function of every world `{ω₀ with thash := T}`, to the second phase of `qToTcr` there. -/
theorem fors_tcr_mach_exists (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Input S c → (Output S)) → Closed (WS (Input S c) (Output S) E) (ℕ × (worldPrims ω₀).Y),
      PUE (spec := unifSpec) cnt0 Mach (q + forsMHashes S.vp qs) ∧
      ∀ T, Mach (oracle S { ω₀ with thash := T }) =
        (qToTcr (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).forge st pk :=
  ⟨forsTcrMach S c optRand₀ F ω₀ st pk, pue_forsTcrMach S c optRand₀ F ω₀ st pk q qs hq hqs,
    forsTcrMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ st pk⟩

/-- **Machine family, `dspr`.** -/
theorem fors_dspr_mach_exists (ω₀ : FinFns S.vp.params c) (st : ForsSt S c ω₀) (pk : (worldPrims ω₀).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Input S c → (Output S)) → Closed (WS (Input S c) (Output S) E) (ℕ × Bool),
      PUE (spec := unifSpec) cnt0 Mach (q + forsMHashes S.vp qs) ∧
      ∀ T, Mach (oracle S { ω₀ with thash := T }) =
        (qToDspr (internal S c optRand₀ pkSeedDist₀ F { ω₀ with thash := T })).guess st pk :=
  ⟨forsDsprMach S c optRand₀ F ω₀ st pk, pue_forsDsprMach S c optRand₀ F ω₀ st pk q qs hq hqs,
    forsDsprMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ st pk⟩

/-- **`hModel` of `qfors`, `tcrFv`**, discharged with `q' = q + forsMHashes S.vp qs`. -/
theorem forsTcr_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : FinFns S.vp.params c) (st : Open.ForsP1State S.vp (worldPrims ω₀))
      (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × S.Node)
          (q + forsMHashes S.vp qs),
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × S.Node → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToTcr (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mo, hMo⟩ := (pue_forsTcrMach S c optRand₀ F ω₀ st pk q qs hq hqs).exists_model ρ
  refine ⟨Mo, fun T Ev _ ↦ ?_⟩
  rw [hMo, forsTcrMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ st pk T, hρ]

/-- **`hModel` of `qfors`, `dspr`**, with `q' = q + forsMHashes S.vp qs`: the model is the
model `HybridModel.ofProgram` of a one-port program, hence `Additive`; its `RowsBound` is taken
from the named hypothesis `hRows` ("`RowsBound` holds for `ofProgram` models", NOT proved: it is
proved only for `ofSecondPort` models, `ofSecondPort_rowsBound`). -/
theorem forsDspr_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hRows : ∀ (x : QuantumComp LocalSig.instruments.{0} (qromSpec (Input S c) (Output S))
        (fun _ ↦ ℕ × Bool) (progReg (Input S c) (Output S) E)) (ρ : SubState ((Input S c × (Output S)) × E))
        (hx : x.IsQueryBound (fun _ ↦ q + forsMHashes S.vp qs)),
      PQ.QROM.Rows.RowsBound (fun H Ev ↦ ((PQ.QROM.HybridModel.ofProgram
        LocalSig.Interp.instruments x ρ (q + forsMHashes S.vp qs) hx Sigma.snd).prob H Ev).toReal)
        (q + forsMHashes S.vp qs)) :
    ∀ (ω₀ : FinFns S.vp.params c) (st : Open.ForsP1State S.vp (worldPrims ω₀))
      (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × Bool) (q + forsMHashes S.vp qs),
        Mo.Additive ∧
        PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) (q + forsMHashes S.vp qs) ∧
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × Bool → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToDspr (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).guess st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨x, hx, hxe⟩ := (pue_forsDsprMach S c optRand₀ F ω₀ st pk q qs hq hqs).exists_prog_qprob
  refine ⟨PQ.QROM.HybridModel.ofProgram LocalSig.Interp.instruments x ρ _ hx Sigma.snd,
    PQ.QROM.HybridModel.ofProgram_additive _ x ρ _ hx Sigma.snd, hRows x ρ hx, fun T Ev _ ↦ ?_⟩
  refine (hxe Ev _ ρ).trans ?_
  rw [forsDsprMach_oracle S c optRand₀ pkSeedDist₀ F ω₀ st pk T, hρ]

end deliver

section deliver2

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

/-- **`hModel` of `qfors`, `dspr`**, discharged with `q' = q + forsMHashes S.vp qs`. -/
theorem forsDspr_hModel' (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : FinFns S.vp.params c) (st : Open.ForsP1State S.vp (worldPrims ω₀))
      (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × Bool) (q + forsMHashes S.vp qs),
        Mo.Additive ∧
        PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) (q + forsMHashes S.vp qs) ∧
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × Bool → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToDspr (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).guess st pk) F.ρ₀ :=
  forsDspr_hModel S c optRand₀ pkSeedDist₀ F q qs hq hqs
    (fun x ρ hx ↦ PQ.QROM.Rows.ofProgram_rowsBound _ x ρ _ hx Sigma.snd)

end deliver2

end Reduction.SetOracle
#print axioms Reduction.SetOracle.forsTcr_hModel
#print axioms Reduction.SetOracle.forsDspr_hModel'
