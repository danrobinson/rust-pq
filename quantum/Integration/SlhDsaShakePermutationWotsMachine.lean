import Integration.SlhDsaShakeXofWotsMachine
import Integration.SlhDsaShakePermutationSparseMemo
namespace Reduction.ShakePermutation.SparsePort.Wots
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open ShakeApi Resources2 Open
open scoped ComplexOrder Kronecker
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option linter.unusedSectionVars false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable (S : Sha2Set)
section mach

variable {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger Port Words E)

noncomputable def wotsMach (ω₀ : RawTable S N)
    (st : SecretTable S.vp (ShakeApi.primitives S (extend ω₀)) × List (WotsGame.Entry (ShakeApi.primitives S (extend ω₀))) × (ShakeApi.primitives S (extend ω₀)).Y)
    (pk : (ShakeApi.primitives S (extend ω₀)).PkSeed) {β : Type}
    (post : ℕ × (ShakeApi.primitives S (extend ω₀)).Y × WotsSig S.vp.params (ShakeApi.primitives S (extend ω₀)).core →
      OracleComp (Lazy.OSpec (ShakeApi.primitives S (extend ω₀)) []ₒ) β) (H : Port → Words) :
    Closed (WS Port Words E) β :=
  qmWotsMach (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) (SkCost.table S N H)) (SkCost.qmForger S F (extend ω₀) H) st pk post

theorem evalCost_qmSignG (ω₀ : RawTable S N) (cap : N ≤ rawCap S 67 65536) (tbl : SecretTable S.vp (ShakeApi.primitives S (extend ω₀)))
    (pk : PublicKeyCore (ShakeApi.primitives S (extend ω₀)).core)
    (signO : List SLHDSA.Byte → (ShakeApi.primitives S (extend ω₀)).Y →
      OracleComp (Lazy.OSpec (ShakeApi.primitives S (extend ω₀)) []ₒ) (GeneralScheme.SignatureCore S.vp (ShakeApi.primitives S (extend ω₀)).core))
    (k : ℕ) (hk : ∀ m R, IsQueryBoundP (signO m R) (fun t ↦ Lazy.kind t = .hash) k)
    (t : (unifSpec + (List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp (ShakeApi.primitives S (extend ω₀)).core)).Domain)
    (s : G2Log (ShakeApi.primitives S (extend ω₀))) :
    EvalCost (fun H ↦ (qmSignG (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) (SkCost.table S N H)) tbl pk signO t).run s)
      (sgnW (483*k) t) := by
  rcases t with n | msg
  · exact EvalCost.const _
  · change EvalCost (fun H ↦ signRand S optRand₀ (extend ω₀) pk >>= fun addrnd ↦
      lazyRandomizer s msg addrnd >>= fun R ↦
        simulateQ (qmImpl (hashPort S N (extend ω₀) (SkCost.table S N H)) tbl) (signO msg R) >>= fun sig ↦
          (pure (sig, s ++ [(msg, addrnd, R)]) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := Port) (Y := Words)
        (signRand S optRand₀ (extend ω₀) pk)) fun addrnd ↦
      EvalCost.bind (EvalCost.const (X := Port) (Y := Words) (lazyRandomizer s msg addrnd))
        fun R ↦ EvalCost.bind (Memo.open_cost S N ω₀ cap tbl _ _ (hk msg R))
          fun sig ↦ EvalCost.const (X := Port) (Y := Words)
            (pure (sig, s ++ [(msg, addrnd, R)]) : ProbComp _)
    exact h.mono (by simp)

theorem pue_wotsMach (ω₀ : RawTable S N) (cap : N ≤ rawCap S 67 65536)
    (st : SecretTable S.vp (ShakeApi.primitives S (extend ω₀)) × List (WotsGame.Entry (ShakeApi.primitives S (extend ω₀))) × (ShakeApi.primitives S (extend ω₀)).Y)
    (pk : (ShakeApi.primitives S (extend ω₀)).PkSeed) {β : Type}
    (post : ℕ × (ShakeApi.primitives S (extend ω₀)).Y × WotsSig S.vp.params (ShakeApi.primitives S (extend ω₀)).core →
      OracleComp (Lazy.OSpec (ShakeApi.primitives S (extend ω₀)) []ₒ) β) (cp : ℕ)
    (hpost : ∀ x, IsQueryBoundP (post x) (fun t ↦ Lazy.kind t = .hash) cp) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (wotsMach S N optRand₀ F ω₀ st pk post)
      (q + 483*(qs * wotsSignHistHashes S.vp + (wotsAnswerHashes S.vp + cp))) := by
  unfold wotsMach qmWotsMach
  have hS : ∀ m R, IsQueryBoundP (wotsSignFromHistO (gspec := []ₒ) st.2.1
      (⟨pk, st.2.2⟩ : PublicKeyCore (ShakeApi.primitives S (extend ω₀)).core) m R) (fun t ↦ Lazy.kind t = .hash)
      (wotsSignHistHashes S.vp) := fun m R ↦
    (wotsSignFromHistO_kindBound .hash st.2.1 _ m R).mono wotsSignHistB_ind_hash
  have h := PUE.bind (PUE.close _ (evalCost_qmSignG S N optRand₀ ω₀ cap st.1 ⟨pk, st.2.2⟩ _ _ hS)
      (SkCost.pue_qmForger S F (extend ω₀) q qs _ hq hqs ⟨pk, st.2.2⟩) []) fun r ↦ by
    have h := PUE.liftU_bind (E := E) (B := fun o _ ↦ (pure o : Closed (WS Port Words E) β))
      (q := 0)
      (Memo.open_cost S N ω₀ cap st.1 _ _ (Lazy.qb_bind _ (wotsAnswerOpen_hashes (gspec := []ₒ) st.2.1
        ⟨pk, st.2.2⟩ r.1.1 r.1.2) hpost)) fun o ↦ PUE.pure o 0
    simp only [bind_pure] at h
    exact h
  refine h.mono ?_
  simp only [Nat.mul_add,Nat.mul_left_comm 483 qs]
  omega

end mach

/-! ## Delivered statements -/

section deliver

variable {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger Port Words E)

abbrev WotsSt (ω₀ : RawTable S N) : Type :=
  (SecretTable S.vp (ShakeApi.primitives S (extend ω₀)) × List (WotsGame.Entry (ShakeApi.primitives S (extend ω₀))) × (ShakeApi.primitives S (extend ω₀)).Y) ×
    List (WotsGame.Entry (ShakeApi.primitives S (extend ω₀)))

set_option maxHeartbeats 2500000 in
private theorem wOracle {β : Type} (ω₀ : RawTable S N) (H : Port → Words) (st : Open.WState S.vp (ShakeApi.primitives S (extend ω₀))) (pk : S.Node)
    (post : ℕ × S.Node × WotsSig S.vp.params (ShakeApi.primitives S (extend ω₀)).core →
      OracleComp (Lazy.OSpec (ShakeApi.primitives S (extend ω₀)) []ₒ) β)
    (result : ℕ × S.Node × WotsSig S.vp.params (ShakeApi.primitives S (extend ω₀)).core → β)
    (hpost : ∀ x, simulateQ (Lazy.tblImpl (gspec := []ₒ) (PublicHash.impl (refPrims S N ω₀ (SkCost.table S N H))) st.1)
      (post x) = pure (result x)) :
    wotsMach S N optRand₀ F ω₀ st pk post H =
      (qWotsForge (qPureBytesToInternal (forgerAt S optRand₀ pkSeedDist₀ F (extend (SkCost.table S N H)) H)) st pk >>= fun x => liftU (pure (result x))) := by
  let real := ShakeApi.primitives S (extend (SkCost.table S N H))
  let r := signRand S optRand₀ (extend ω₀)
  let r' := signRand S optRand₀ (extend (SkCost.table S N H))
  let B := Memo.refForger S N optRand₀ pkSeedDist₀ F ω₀ (SkCost.table S N H) H
  let R := refPrims S N ω₀ (SkCost.table S N H)
  let postRun (v : Closed (WS Port Words E)
      (ℕ × S.Node × WotsSig S.vp.params R.core)) :=
    v >>= fun x => (liftU (pure (result x)) : Closed (WS Port Words E) β)
  have tr := QInd.qWotsForge_tr (prims := R) real.PRF real.PRFmsg
    (ShakeApi.codec S (extend ω₀)) r r' pkSeedDist₀ (fun _ => rfl) B st pk
  have h := qWotsForge_post_eq (prims := R) r (qPureBytesToInternal B) st pk result post hpost
  have rewriteMachine := congrArg₂
    (fun impl main => qmWotsMach (prims := R) r impl main st pk post)
    (refHash S N ω₀ (SkCost.table S N H)) (Memo.refMain S N optRand₀ pkSeedDist₀ F ω₀ (SkCost.table S N H) H).symm
  kexact rewriteMachine.trans (h.symm.trans (congrArg postRun tr.symm))

/-! ### `qrTcrT` (field `tcrT`) -/

theorem wotsTcrT_mach_eq (ω₀ : RawTable S N) (st : WotsSt S N ω₀) (pk : (ShakeApi.primitives S (extend ω₀)).PkSeed) (H : Port → Words) :
    wotsMach S N optRand₀ F ω₀ st.1 pk
        (fun x ↦ wotsTcrAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2)
        H =
      (qrTcrT (qPureBytesToInternal (forgerAt S optRand₀ pkSeedDist₀ F (extend (SkCost.table S N H)) H))).forge st pk := by
  kexact wOracle S N optRand₀ pkSeedDist₀ F ω₀ H st.1 pk
    (fun x => wotsTcrAnswerO (prims := refPrims S N ω₀ (SkCost.table S N H)) pk st.2 x.1 x.2.1 x.2.2)
    (fun x => tcrAnswer (prims := refPrims S N ω₀ (SkCost.table S N H)) pk st.2 x.1 x.2.1 x.2.2)
    (fun x => wotsTcrAnswerO_tbl (prims := refPrims S N ω₀ (SkCost.table S N H)) (gspec := []ₒ) st.1.1 pk st.2 x.1 x.2.1 x.2.2)

theorem wotsTcrT_mach_exists (ω₀ : RawTable S N) (cap : N ≤ rawCap S 67 65536) (st : WotsSt S N ω₀) (pk : (ShakeApi.primitives S (extend ω₀)).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Port → Words) → Closed (WS Port Words E) (ℕ × (ShakeApi.primitives S (extend ω₀)).Y),
      PUE (spec := unifSpec) cnt0 Mach (q + 483*qmWotsTcrTHashes S.vp qs) ∧
      ∀ H : Port → Words, Mach H =
        (qrTcrT (qPureBytesToInternal (forgerAt S optRand₀ pkSeedDist₀ F (extend (SkCost.table S N H)) H))).forge st pk := by
  refine ⟨wotsMach S N optRand₀ F ω₀ st.1 pk
      (fun x ↦ wotsTcrAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2), ?_,
    fun H ↦ wotsTcrT_mach_eq S N optRand₀ pkSeedDist₀ F ω₀ st pk H⟩
  have h := pue_wotsMach S N optRand₀ F ω₀ cap st.1 pk _ (wotsTcrHashes S.vp)
    (fun x ↦ (wotsTcrAnswerO_kindBound .hash pk st.2 x.1 x.2.1 x.2.2).mono (by
      have h1 : Lazy.ind Lazy.Kind.hash Lazy.Kind.hash = 1 := rfl
      rw [h1, wotsTcrHashes]
      exact le_of_eq (by ring))) q qs hq hqs
  unfold qmWotsTcrTHashes
  exact h

theorem wotsUd_mach_eq (ω₀ : RawTable S N) (st : WotsSt S N ω₀) (pk : (ShakeApi.primitives S (extend ω₀)).PkSeed) (H : Port → Words) :
    wotsMach S N optRand₀ F ω₀ st.1 pk
        (fun x ↦ wotsWinO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2)
        H =
      (qrUd (qPureBytesToInternal (forgerAt S optRand₀ pkSeedDist₀ F (extend (SkCost.table S N H)) H))).distinguish st pk := by
  kexact wOracle S N optRand₀ pkSeedDist₀ F ω₀ H st.1 pk
    (fun x => wotsWinO (prims := refPrims S N ω₀ (SkCost.table S N H)) pk st.2 x.1 x.2.1 x.2.2)
    (fun x => WotsGame.win (prims := refPrims S N ω₀ (SkCost.table S N H)) pk st.2 x.1 x.2.1 x.2.2)
    (fun x => wotsWinO_tbl (prims := refPrims S N ω₀ (SkCost.table S N H)) (gspec := []ₒ) st.1.1 pk st.2 x.1 x.2.1 x.2.2)

theorem wotsUd_mach_exists (ω₀ : RawTable S N) (cap : N ≤ rawCap S 67 65536) (st : WotsSt S N ω₀) (pk : (ShakeApi.primitives S (extend ω₀)).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Port → Words) → Closed (WS Port Words E) (Bool),
      PUE (spec := unifSpec) cnt0 Mach (q + 483*qmWotsUdHashes S.vp qs) ∧
      ∀ H : Port → Words, Mach H =
        (qrUd (qPureBytesToInternal (forgerAt S optRand₀ pkSeedDist₀ F (extend (SkCost.table S N H)) H))).distinguish st pk := by
  refine ⟨wotsMach S N optRand₀ F ω₀ st.1 pk
      (fun x ↦ wotsWinO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2), ?_,
    fun H ↦ wotsUd_mach_eq S N optRand₀ pkSeedDist₀ F ω₀ st pk H⟩
  have h := pue_wotsMach S N optRand₀ F ω₀ cap st.1 pk _ (wotsWinHashes S.vp)
    (fun x ↦ (wotsWinO_kindBound .hash pk st.2 x.1 x.2.1 x.2.2).mono (by
      simp [Lazy.ind, wotsWinHashes])) q qs hq hqs
  unfold qmWotsUdHashes
  exact h

theorem wotsPre_mach_eq (ω₀ : RawTable S N) (st : WotsSt S N ω₀) (pk : (ShakeApi.primitives S (extend ω₀)).PkSeed) (H : Port → Words) :
    wotsMach S N optRand₀ F ω₀ st.1 pk
        (fun x ↦ wotsPreAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2)
        H =
      (qrPre (qPureBytesToInternal (forgerAt S optRand₀ pkSeedDist₀ F (extend (SkCost.table S N H)) H))).invert st pk := by
  kexact wOracle S N optRand₀ pkSeedDist₀ F ω₀ H st.1 pk
    (fun x => wotsPreAnswerO (prims := refPrims S N ω₀ (SkCost.table S N H)) pk st.2 x.1 x.2.1 x.2.2)
    (fun x => preAnswer (prims := refPrims S N ω₀ (SkCost.table S N H)) pk st.2 x.1 x.2.1 x.2.2)
    (fun x => wotsPreAnswerO_tbl (prims := refPrims S N ω₀ (SkCost.table S N H)) (gspec := []ₒ) st.1.1 pk st.2 x.1 x.2.1 x.2.2)

theorem wotsPre_mach_exists (ω₀ : RawTable S N) (cap : N ≤ rawCap S 67 65536) (st : WotsSt S N ω₀) (pk : (ShakeApi.primitives S (extend ω₀)).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Port → Words) → Closed (WS Port Words E) (ℕ × S.Node),
      PUE (spec := unifSpec) cnt0 Mach (q + 483*qmWotsPreHashes S.vp qs) ∧
      ∀ H : Port → Words, Mach H =
        (qrPre (qPureBytesToInternal (forgerAt S optRand₀ pkSeedDist₀ F (extend (SkCost.table S N H)) H))).invert st pk := by
  refine ⟨wotsMach S N optRand₀ F ω₀ st.1 pk
      (fun x ↦ wotsPreAnswerO (gspec := []ₒ) pk st.2 x.1 x.2.1 x.2.2), ?_,
    fun H ↦ wotsPre_mach_eq S N optRand₀ pkSeedDist₀ F ω₀ st pk H⟩
  have h := pue_wotsMach S N optRand₀ F ω₀ cap st.1 pk _ (Resources2.wotsPreHashes S.vp)
    (fun x ↦ (wotsPreAnswerO_kindBound .hash pk st.2 x.1 x.2.1 x.2.2).mono (by
      simp [Lazy.ind, Resources2.wotsPreHashes])) q qs hq hqs
  unfold qmWotsPreHashes
  exact h

end deliver
end Reduction.ShakePermutation.SparsePort.Wots
#print axioms Reduction.ShakePermutation.SparsePort.Wots.wotsPre_mach_exists
#print axioms Reduction.ShakePermutation.SparsePort.Wots.wotsUd_mach_exists
#print axioms Reduction.ShakePermutation.SparsePort.Wots.wotsTcrT_mach_exists
