import Integration.SlhDsaShakeApiForger
import Integration.SlhDsaCompressionClassTransport

namespace Reduction.ShakeApi
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option linter.unusedSectionVars false

noncomputable abbrev rawInternal (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node)
    (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
    (F : PortForger (Input N) (Bytes S.vp.params.m) E) (H : RawTable S N) :=
  qPureBytesToInternal (rawForger S N rand seeds F H)

section mach

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input N) (Bytes S.vp.params.m) E)

noncomputable def tcrMach (ω₀ : RawTable S N) (n : ℕ)
    (st : SecretTable S.vp (primitives S (extend ω₀)) ×
      List ((primitives S (extend ω₀)).AdrsKey × List (primitives S (extend ω₀)).Y))
    (pk : (primitives S (extend ω₀)).PkSeed) (H : Input N → (Bytes S.vp.params.m)) :
    Closed (WS (Input N) (Bytes S.vp.params.m) E) (ℕ × {xs : List (primitives S (extend ω₀)).Y // xs.length = n}) :=
  qmMach (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) H) n (qmForger S N F (extend ω₀) H) st pk

/-- Keep the public hash functions of the actual table and the secret
functions of the reference core while transporting the typed forger. -/
abbrev refPrims (ω₀ T : RawTable S N) :=
  { primitives S (extend ω₀) with Thash := (primitives S (extend T)).Thash,
                                     Hmsg := (primitives S (extend T)).Hmsg }

noncomputable abbrev refForger (ω₀ T : RawTable S N) :=
  F.at T (pureBytesAlg S.vp (refPrims S N ω₀ T) (codec S (extend ω₀)) (signRand S optRand₀ (extend ω₀)) pkSeedDist₀)

theorem refMain (ω₀ T : RawTable S N) :
    (qPureBytesToInternal (refForger S N optRand₀ pkSeedDist₀ F ω₀ T)).main =
    qmForger S N F (extend ω₀) T := by
  funext pk
  simp only [refForger,qPureBytesToInternal,qToInternal,qPureBytesToTyped,QForger.wrapForger,
    PortForger.at,qmCSign_eq,qmCRead_eq,pureBytesView]
  rfl

theorem refHash (ω₀ T : RawTable S N) :
    hashPort S N (extend ω₀) T = PublicHash.impl (refPrims S N ω₀ T) := by
  funext t
  cases t <;> rfl

theorem tcrMach_oracle (ω₀ : RawTable S N) (n : ℕ)
    (st : SecretTable S.vp (primitives S (extend ω₀)) ×
      List ((primitives S (extend ω₀)).AdrsKey × List (primitives S (extend ω₀)).Y))
    (pk : (primitives S (extend ω₀)).PkSeed) (T : RawTable S N) :
    tcrMach S N optRand₀ F ω₀ n st pk T =
      (qbTcrArM n (rawInternal S N optRand₀ pkSeedDist₀ F T)).forge st pk := by
  let real := primitives S (extend T)
  let r := signRand S optRand₀ (extend ω₀)
  let r' := signRand S optRand₀ (extend T)
  let B := refForger S N optRand₀ pkSeedDist₀ F ω₀ T
  have tr := QInd.qMemoForge_tr (prims := refPrims S N ω₀ T) real.PRF real.PRFmsg
    (codec S (extend ω₀)) r r' pkSeedDist₀ (fun _ => rfl) n B st pk
  refine Eq.trans ?_ tr.symm
  rw [qMemoForge_eq_qmMach]
  unfold B
  rw [refMain,← refHash]
  qm_kernel_rfl

end mach

section pue

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input N) (Bytes S.vp.params.m) E)

attribute [local instance] Lazy.openQ

theorem evalCost_open (ω₀ : RawTable S N) (tbl : SecretTable S.vp (primitives S (extend ω₀))) {α : Type}
    (P : OracleComp (Lazy.OSpec (primitives S (extend ω₀)) []ₒ) α) (k : ℕ)
    (h : IsQueryBoundP P (fun t ↦ Lazy.kind t = .hash) k) :
    EvalCost (fun H ↦ simulateQ (qmImpl (hashPort S N (extend ω₀) H) tbl) P) k :=
  simulate_cost S N (extend ω₀) tbl P h

theorem keygen_hashes (ω₀ : RawTable S N) (pkSeed : (primitives S (extend ω₀)).PkSeed) :
    IsQueryBoundP (Lazy.openKeygen (primitives S (extend ω₀)) []ₒ pkSeed) (fun t ↦ Lazy.kind t = .hash)
      (Lazy.keygenHashes S.vp) :=
  (Lazy.openKeygen_kindBound .hash pkSeed).mono (by simpa [Lazy.ind] using Lazy.keygenB_hash)

theorem sign_hashes (ω₀ : RawTable S N) (msg : List SLHDSA.Byte) (pkSeed : (primitives S (extend ω₀)).PkSeed)
    (root R : (primitives S (extend ω₀)).Y) :
    IsQueryBoundP (Lazy.openSign (primitives S (extend ω₀)) []ₒ msg pkSeed root R)
      (fun t ↦ Lazy.kind t = .hash) (Lazy.signHashes S.vp) :=
  (Lazy.openSign_kindBound .hash msg pkSeed root R).mono
    (by simpa [Lazy.ind] using Lazy.signB_hash)

theorem tail_hashes (ω₀ : RawTable S N) (pkSeed : (primitives S (extend ω₀)).PkSeed)
    (L : List ((primitives S (extend ω₀)).AdrsKey × List (primitives S (extend ω₀)).Y)) (root : (primitives S (extend ω₀)).Y)
    (z : (List SLHDSA.Byte × GeneralScheme.SignatureCore S.vp (primitives S (extend ω₀)).core) ×
      G2Log (primitives S (extend ω₀))) :
    IsQueryBoundP (qmTail pkSeed L root z) (fun t ↦ Lazy.kind t = .hash)
      (1 + Resources2.verifyHashes S.vp * 2) := by
  have hver : ∀ (parts : DigestParts S.vp.params)
      (sig : GeneralScheme.SignatureCore S.vp (primitives S (extend ω₀)).core),
      IsQueryBoundP ((simulateQ (Resources2.collO (gspec := []ₒ) pkSeed L)
        (Resources2.verifyFree pkSeed parts sig)).run none) (fun t ↦ Lazy.kind t = .hash)
        (Resources2.verifyHashes S.vp * 2) := fun parts sig ↦
    IsQueryBoundP.simulateQ_run_of_step_le (cost := 2) (q := fun t ↦ Lazy.kind t = .hash)
      (Resources2.verifyFree_bound pkSeed parts sig)
      (fun t _ s ↦ Resources2.collO_step_bound pkSeed L .hash t s)
      (fun t ht s ↦ absurd trivial ht) none
  have hmsg : ∀ (R root : (primitives S (extend ω₀)).Y) (m : List SLHDSA.Byte),
      IsQueryBoundP (PublicHash.hmsg (primitives S (extend ω₀)).core R pkSeed root m :
        OracleComp (Lazy.OSpec (primitives S (extend ω₀)) []ₒ) (Bytes S.vp.params.m))
        (fun t ↦ Lazy.kind t = .hash) 1 :=
    fun R root m ↦ (isQueryBoundP_query_iff _ _ _).2 fun _ ↦ Nat.one_pos
  unfold qmTail
  exact Lazy.qb_bind _ (hmsg _ _ _) fun dg ↦
    Lazy.qb_bind _ (m := 0) (hver _ _) fun c ↦ isQueryBoundP_pure _ _ _

/-- Each answer of the forger's classical interface costs its weight. -/
theorem evalCost_qmImplS (ω₀ : RawTable S N) (tbl : SecretTable S.vp (primitives S (extend ω₀)))
    (pkSeed : (primitives S (extend ω₀)).PkSeed) (root : (primitives S (extend ω₀)).Y)
    (t : (unifSpec + (List SLHDSA.Byte →ₒ GeneralScheme.SignatureCore S.vp (primitives S (extend ω₀)).core)).Domain)
    (s : G2Log (primitives S (extend ω₀))) :
    EvalCost (fun H ↦ (qmImplS (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) H) tbl pkSeed root t).run s)
      (sgnW (Lazy.signHashes S.vp) t) := by
  rcases t with n | msg
  · exact EvalCost.const _
  · change EvalCost (fun H ↦ signRand S optRand₀ (extend ω₀) ⟨pkSeed, root⟩ >>= fun addrnd ↦
      lazyRandomizer s msg addrnd >>= fun R ↦
        simulateQ (qmImpl (hashPort S N (extend ω₀) H) tbl)
          (Lazy.openSign (primitives S (extend ω₀)) []ₒ msg pkSeed root R) >>= fun sig ↦
          (pure (sig, (s : List (List SLHDSA.Byte × S.Node × S.Node)) ++ [(msg, addrnd, R)]) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := Input N) (Y := (Bytes S.vp.params.m))
        (signRand S optRand₀ (extend ω₀) ⟨pkSeed, root⟩)) fun addrnd ↦
      EvalCost.bind (EvalCost.const (X := Input N) (Y := (Bytes S.vp.params.m)) (lazyRandomizer s msg addrnd))
        fun R ↦ EvalCost.bind (evalCost_open S N ω₀ tbl _ _ (sign_hashes S N ω₀ msg pkSeed root R))
          fun sig ↦ EvalCost.const (X := Input N) (Y := (Bytes S.vp.params.m))
            (pure (sig, (s : List (List SLHDSA.Byte × S.Node × S.Node)) ++ [(msg, addrnd, R)]) : ProbComp _)
    exact h.mono (by simp)

/-- The class-TCR machine family makes at most `q + tcrMHashes qs` port
calls plus evaluations on every path. -/
theorem pue_tcrMach (ω₀ : RawTable S N) (n : ℕ)
    (st : SecretTable S.vp (primitives S (extend ω₀)) ×
      List ((primitives S (extend ω₀)).AdrsKey × List (primitives S (extend ω₀)).Y))
    (pk : (primitives S (extend ω₀)).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (tcrMach S N optRand₀ F ω₀ n st pk) (q + tcrMHashes S.vp qs) := by
  unfold tcrMach qmMach
  have hB : ∀ root : (primitives S (extend ω₀)).Y, PUE (spec := unifSpec) cnt0 (fun H ↦
      close (qmImplS (signRand S optRand₀ (extend ω₀)) (hashPort S N (extend ω₀) H) st.1 pk root)
          (qmForger S N F (extend ω₀) H ⟨pk, root⟩) [] >>= fun z ↦
        liftU (classOut (primitives S (extend ω₀)) n st.2 <$>
          simulateQ (qmImpl (hashPort S N (extend ω₀) H) st.1) (qmTail pk st.2 root z)))
      (q + qs * Lazy.signHashes S.vp + (1 + Resources2.verifyHashes S.vp * 2)) := by
    intro root
    refine PUE.bind (PUE.close _ (evalCost_qmImplS S N optRand₀ ω₀ st.1 pk root)
      (pue_qmForger S N F (extend ω₀) q qs _ hq hqs ⟨pk, root⟩) []) fun z ↦ ?_
    have h := PUE.liftU_bind (E := E) (B := fun o _ ↦ (pure o : Closed (WS (Input N) (Bytes S.vp.params.m) E) _))
      (q := 0)
      ((evalCost_open S N ω₀ st.1 _ _ (tail_hashes S N ω₀ pk st.2 root z)).map
        (classOut (primitives S (extend ω₀)) n st.2)) fun o ↦ PUE.pure o 0
    simpa using h
  have h := PUE.liftU_bind (evalCost_open S N ω₀ st.1 _ _ (keygen_hashes S N ω₀ pk)) hB
  refine h.mono ?_
  unfold tcrMHashes
  omega

end pue

/-! ## Steps 3 and 5: the delivered statements -/

section deliver

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E] (N : ℕ)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input N) (Bytes S.vp.params.m) E)

/-- The class-TCR reduction uses at most `q + tcrMHashes qs` raw evaluations
for every shared table, phase-one state, and public seed. -/
theorem tcr_mach_exists (ω₀ : RawTable S N) (n : ℕ)
    (st : SecretTable S.vp (primitives S (extend ω₀)) ×
      List ((primitives S (extend ω₀)).AdrsKey × List (primitives S (extend ω₀)).Y))
    (pk : (primitives S (extend ω₀)).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (Input N → (Bytes S.vp.params.m)) →
        Closed (WS (Input N) (Bytes S.vp.params.m) E) (ℕ × {xs : List (primitives S (extend ω₀)).Y // xs.length = n}),
      PUE (spec := unifSpec) cnt0 Mach (q + tcrMHashes S.vp qs) ∧
      ∀ T : RawTable S N, Mach T =
        (qbTcrArM n (rawInternal S N optRand₀ pkSeedDist₀ F T)).forge st pk :=
  ⟨tcrMach S N optRand₀ F ω₀ n st pk, pue_tcrMach S N optRand₀ F ω₀ n st pk q qs hq hqs,
    fun T ↦ tcrMach_oracle S N optRand₀ pkSeedDist₀ F ω₀ n st pk T⟩

end deliver
end Reduction.ShakeApi
#print axioms Reduction.ShakeApi.tcr_mach_exists
