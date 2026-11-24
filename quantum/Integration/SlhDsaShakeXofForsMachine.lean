import Integration.SlhDsaShakeXofTcrMachine
import Integration.SlhDsaCompressionForsTransport
namespace Reduction.ShakeApi
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option linter.unusedSectionVars false
variable (S : Sha2Set)
section mach

variable {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input N) (Bytes S.vp.params.m) E)

/-- State of the FORS first phase (table, sampled targets, leaf images). -/
abbrev ForsSt (ω₀ : RawTable S N) : Type :=
  SecretTable S.vp (primitives S (extend ω₀)) × List ((primitives S (extend ω₀)).AdrsKey × (primitives S (extend ω₀)).Y) ×
    List (primitives S (extend ω₀)).Y

/-- **The FORS second-phase machine family** for the fixed world `ω₀`, state `st`, seed `pk`. -/
noncomputable def forsMach (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed)
    (H : Input N → (Bytes S.vp.params.m)) : Closed (WS (Input N) (Bytes S.vp.params.m) E) ((ℕ × (primitives S (extend ω₀)).Y) × List ℕ) :=
  fRun (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) H) (qmForger S N F (extend ω₀) H) st pk

theorem forsMach_oracle (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed) (T : RawTable S N) :
    forsMach S N optRand₀ F ω₀ st pk T =
      qFindRun (rawInternal S N optRand₀ pkSeedDist₀ F T) st pk := by
  let real := primitives S (extend T)
  let r := signRand S optRand₀ (extend ω₀)
  let r' := signRand S optRand₀ (extend T)
  let B := refForger S N optRand₀ pkSeedDist₀ F ω₀ T
  have tr := QInd.qFindRun_tr (prims := refPrims S N ω₀ T) real.PRF real.PRFmsg
    (codec S (extend ω₀)) r r' (fun _ => rfl) pkSeedDist₀ B st pk
  refine Eq.trans ?_ tr.symm
  rw [qFindRun_eq_fRun]
  unfold B
  rw [refMain,← refHash]
  qm_kernel_rfl

end mach
section pueFors

variable {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input N) (Bytes S.vp.params.m) E)

attribute [local instance] Lazy.openQ Lazy.closedQ

open Resources2

theorem evalCost_fImpl (ω₀ : RawTable S N) (tbl : SecretTable S.vp (primitives S (extend ω₀)))
    (tg : List ((primitives S (extend ω₀)).AdrsKey × (primitives S (extend ω₀)).Y))
    (t : (Lazy.OSpec (primitives S (extend ω₀)) (forsG (primitives S (extend ω₀)))).Domain) (s : List ℕ) :
    EvalCost (fun H ↦ (fImpl (hashPort S N (extend ω₀) H) tbl tg t).run s)
      (if Lazy.kind t = .hash then 1 else 0) := by
  rcases t with n | t | d | q
  · exact EvalCost.const _
  · exact EvalCost.const _
  · exact EvalCost.const _
  · have e : (fun H ↦ (fImpl (hashPort S N (extend ω₀) H) tbl tg (.inr (.inr (.inr q)))).run s) =
        fun H ↦ (fun y ↦ (y, s)) <$> (pure (hashPort S N (extend ω₀) H q) : ProbComp _) := by
      funext H
      simp [fImpl]
    rw [e]
    exact ((hash_cost S N (extend ω₀) q).map _).mono (by simp [Lazy.kind])

theorem evalCost_fOpen (ω₀ : RawTable S N) (tbl : SecretTable S.vp (primitives S (extend ω₀)))
    (tg : List ((primitives S (extend ω₀)).AdrsKey × (primitives S (extend ω₀)).Y)) {γ : Type}
    (P : OracleComp (Lazy.OSpec (primitives S (extend ω₀)) (forsG (primitives S (extend ω₀)))) γ) (k : ℕ)
    (hP : IsQueryBoundP P (fun t ↦ Lazy.kind t = .hash) k) (s : List ℕ) :
    EvalCost (fun H ↦ (simulateQ (fImpl (hashPort S N (extend ω₀) H) tbl tg) P).run s) k :=
  evalCost_simulateQ_run (fun H ↦ fImpl (hashPort S N (extend ω₀) H) tbl tg) _
    (evalCost_fImpl S N ω₀ tbl tg) P k (wCount_of_isQueryBoundP _ P k hP) s

theorem fSignOpen_hashes (ω₀ : RawTable S N) (pk : PublicKeyCore (primitives S (extend ω₀)).core)
    (ys : List (primitives S (extend ω₀)).Y) (m : List SLHDSA.Byte) (R : (primitives S (extend ω₀)).Y) :
    IsQueryBoundP (fSignOpen pk ys m R) (fun t ↦ Lazy.kind t = .hash)
      (forsSignHashes S.vp + 1) := by
  unfold fSignOpen
  refine Lazy.qb_bind _ ((forsSignOpen_kindBound .hash pk ys m R).mono ?_) fun sig ↦
    Lazy.qb_bind _ (m := 0) (Lazy.query_kindBound .hash _) fun d ↦ isQueryBoundP_pure _ _ _
  simpa [Lazy.ind] using forsSignB_hash (vp := S.vp)

theorem fAnswerO_hashes (ω₀ : RawTable S N) (pk : PublicKeyCore (primitives S (extend ω₀)).core)
    (ys : List (primitives S (extend ω₀)).Y) (opened : List (Adrs × ℕ)) (msg : List SLHDSA.Byte)
    (sig : GeneralScheme.SignatureCore S.vp (primitives S (extend ω₀)).core) :
    IsQueryBoundP (fAnswerO pk ys opened msg sig) (fun t ↦ Lazy.kind t = .hash)
      (1 + S.vp.params.k) := by
  unfold fAnswerO
  refine (Lazy.qb_bind _ (Lazy.query_kindBound .hash _) fun digest ↦
    Lazy.qb_bind _ (m := 0) (Lazy.qb_ofFnM _ _ (Lazy.ind .hash .hash) fun i ↦
      Lazy.query_kindBound .hash _) fun imgs ↦ isQueryBoundP_pure _ _ _).mono ?_
  simp only [Lazy.ind]
  split <;> simp

theorem evalCost_fSignS (ω₀ : RawTable S N) (tbl : SecretTable S.vp (primitives S (extend ω₀)))
    (tg : List ((primitives S (extend ω₀)).AdrsKey × (primitives S (extend ω₀)).Y)) (ys : List (primitives S (extend ω₀)).Y)
    (pkSeed : (primitives S (extend ω₀)).PkSeed) (root : (primitives S (extend ω₀)).Y)
    (t : (unifSpec + (List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp (primitives S (extend ω₀)).core)).Domain)
    (s : G2Log (primitives S (extend ω₀)) × List ℕ × List (Adrs × ℕ)) :
    EvalCost (fun H ↦
      (fSignS (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) H) tbl tg ys pkSeed root t).run s)
      (sgnW (forsSignHashes S.vp + 1) t) := by
  rcases t with n | msg
  · exact EvalCost.const _
  · change EvalCost (fun H ↦ signRand S optRand₀ (extend ω₀) ⟨pkSeed, root⟩ >>= fun addrnd ↦
      lazyRandomizer s.1 msg addrnd >>= fun R ↦
        (simulateQ (fImpl (hashPort S N (extend ω₀) H) tbl tg) (fSignOpen ⟨pkSeed, root⟩ ys msg R)).run s.2.1 >>=
          fun r ↦ (pure (r.1.1, (s.1 ++ [(msg, addrnd, R)], r.2, s.2.2 ++ r.1.2)) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := Input N) (Y := (Bytes S.vp.params.m))
        (signRand S optRand₀ (extend ω₀) ⟨pkSeed, root⟩)) fun addrnd ↦
      EvalCost.bind (EvalCost.const (X := Input N) (Y := (Bytes S.vp.params.m)) (lazyRandomizer s.1 msg addrnd))
        fun R ↦ EvalCost.bind (evalCost_fOpen S N ω₀ tbl tg _ _
          (fSignOpen_hashes S N ω₀ ⟨pkSeed, root⟩ ys msg R) s.2.1)
          fun r ↦ EvalCost.const (X := Input N) (Y := (Bytes S.vp.params.m))
            (pure (r.1.1, (s.1 ++ [(msg, addrnd, R)], r.2, s.2.2 ++ r.1.2)) : ProbComp _)
    exact h.mono (by simp)

/-- **`PUE`.**  The FORS second-phase machine family makes at most `q + forsMHashes qs` port
calls plus evaluations on every path. -/
theorem pue_forsMach (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (forsMach S N optRand₀ F ω₀ st pk) (q + forsMHashes S.vp qs) := by
  unfold forsMach fRun
  have hB : ∀ root : (primitives S (extend ω₀)).Y, PUE (spec := unifSpec) cnt0 (fun H ↦
      close (fSignS (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) H) st.1 st.2.1 st.2.2 pk root)
          (qmForger S N F (extend ω₀) H ⟨pk, root⟩) ([], [], []) >>= fun z ↦
        liftU ((simulateQ (fImpl (hashPort S N (extend ω₀) H) st.1 st.2.1)
          (fAnswerO ⟨pk, root⟩ st.2.2 z.2.2.2 z.1.1 z.1.2)).run z.2.2.1))
      (q + qs * (forsSignHashes S.vp + 1) + (1 + S.vp.params.k)) := by
    intro root
    refine PUE.bind (PUE.close _ (evalCost_fSignS S N optRand₀ ω₀ st.1 st.2.1 st.2.2 pk root)
      (pue_qmForger S N F (extend ω₀) q qs _ hq hqs ⟨pk, root⟩) _) fun z ↦ ?_
    have h := PUE.liftU_bind (E := E) (B := fun o _ ↦ (pure o : Closed (WS (Input N) (Bytes S.vp.params.m) E) _))
      (q := 0) (evalCost_fOpen S N ω₀ st.1 st.2.1 _ _
        (fAnswerO_hashes S N ω₀ ⟨pk, root⟩ st.2.2 z.2.2.2 z.1.1 z.1.2) z.2.2.1) fun o ↦ PUE.pure o 0
    simpa using h
  have h := PUE.liftU_bind (evalCost_open S N ω₀ st.1 _ _ (keygen_hashes S N ω₀ pk)) hB
  refine h.mono ?_
  unfold forsMHashes
  omega

end pueFors

/-! ## Delivered statements -/

section deliver

variable {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input N) (Bytes S.vp.params.m) E)

/-- The SM-TCR (FORS) second-phase machine family. -/
noncomputable def forsTcrMach (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed)
    (H : Input N → (Bytes S.vp.params.m)) : Closed (WS (Input N) (Bytes S.vp.params.m) E) (ℕ × (primitives S (extend ω₀)).Y) :=
  forsMach S N optRand₀ F ω₀ st pk H >>= fun r ↦ liftU (pure (r.1.1, r.1.2))

/-- The SM-DSPR (FORS) second-phase machine family. -/
noncomputable def forsDsprMach (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed)
    (H : Input N → (Bytes S.vp.params.m)) : Closed (WS (Input N) (Bytes S.vp.params.m) E) (ℕ × Bool) :=
  forsMach S N optRand₀ F ω₀ st pk H >>= fun r ↦
    liftU (pure (r.1.1, decide (((st.2.1[r.1.1]?.map Prod.snd).getD default) ≠ r.1.2 ∨
      r.1.1 ∈ r.2)))

theorem forsTcrMach_oracle (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed) (T : RawTable S N) :
    forsTcrMach S N optRand₀ F ω₀ st pk T =
      (qToTcr (rawInternal S N optRand₀ pkSeedDist₀ F T)).forge st pk := by
  unfold forsTcrMach
  rw [forsMach_oracle S N optRand₀ pkSeedDist₀ F ω₀ st pk T]
  rfl

theorem forsDsprMach_oracle (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed) (T : RawTable S N) :
    forsDsprMach S N optRand₀ F ω₀ st pk T =
      (qToDspr (rawInternal S N optRand₀ pkSeedDist₀ F T)).guess st pk := by
  unfold forsDsprMach
  rw [forsMach_oracle S N optRand₀ pkSeedDist₀ F ω₀ st pk T]
  rfl

theorem pue_forsTcrMach (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (forsTcrMach S N optRand₀ F ω₀ st pk) (q + forsMHashes S.vp qs) := by
  have h := PUE.bind (q₂ := 0) (pue_forsMach S N optRand₀ F ω₀ st pk q qs hq hqs)
    (B := fun r _ ↦ (pure (r.1.1, r.1.2) : Closed (WS (Input N) (Bytes S.vp.params.m) E) _))
    fun r ↦ PUE.pure _ 0
  unfold forsTcrMach
  simpa using h

theorem pue_forsDsprMach (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (forsDsprMach S N optRand₀ F ω₀ st pk) (q + forsMHashes S.vp qs) := by
  have h := PUE.bind (q₂ := 0) (pue_forsMach S N optRand₀ F ω₀ st pk q qs hq hqs)
    (B := fun r _ ↦ (pure (r.1.1, decide (((st.2.1[r.1.1]?.map Prod.snd).getD default) ≠ r.1.2 ∨
      r.1.1 ∈ r.2)) : Closed (WS (Input N) (Bytes S.vp.params.m) E) _))
    fun r ↦ PUE.pure _ 0
  unfold forsDsprMach
  simpa using h

/-- A single bounded algorithm implements the FORS collision reduction
for each shared raw table. -/
theorem fors_tcr_mach_exists (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Input N → (Bytes S.vp.params.m)) → Closed (WS (Input N) (Bytes S.vp.params.m) E) (ℕ × (primitives S (extend ω₀)).Y),
      PUE (spec := unifSpec) cnt0 Mach (q + forsMHashes S.vp qs) ∧
      ∀ T : RawTable S N, Mach T =
        (qToTcr (rawInternal S N optRand₀ pkSeedDist₀ F T)).forge st pk :=
  ⟨forsTcrMach S N optRand₀ F ω₀ st pk, pue_forsTcrMach S N optRand₀ F ω₀ st pk q qs hq hqs,
    forsTcrMach_oracle S N optRand₀ pkSeedDist₀ F ω₀ st pk⟩

/-- **Machine family, `dspr`.** -/
theorem fors_dspr_mach_exists (ω₀ : RawTable S N) (st : ForsSt S N ω₀) (pk : (primitives S (extend ω₀)).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Input N → (Bytes S.vp.params.m)) → Closed (WS (Input N) (Bytes S.vp.params.m) E) (ℕ × Bool),
      PUE (spec := unifSpec) cnt0 Mach (q + forsMHashes S.vp qs) ∧
      ∀ T : RawTable S N, Mach T =
        (qToDspr (rawInternal S N optRand₀ pkSeedDist₀ F T)).guess st pk :=
  ⟨forsDsprMach S N optRand₀ F ω₀ st pk, pue_forsDsprMach S N optRand₀ F ω₀ st pk q qs hq hqs,
    forsDsprMach_oracle S N optRand₀ pkSeedDist₀ F ω₀ st pk⟩

end deliver
end Reduction.ShakeApi
#print axioms Reduction.ShakeApi.fors_tcr_mach_exists
#print axioms Reduction.ShakeApi.fors_dspr_mach_exists
