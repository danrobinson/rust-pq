import Integration.SlhDsaBridgeMach
import Reduction.Open.Fors
import PQ.Interactive.GamesGeneral
import Reduction.Open.Phase1Fors
import PQ.QROM.ExactDsprTightGame

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Reduction

/-! ## Generic facts about `close` -/

section closeLemmas

variable {W : Type} [Fintype W] {α : Type}

/-- Closing with an implementation that tracks a function `g` of the state. -/
theorem close_map_state {ι : Type} {spec : OracleSpec ι} {σ σ' : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (impl' : QueryImpl spec (StateT σ' ProbComp))
    (g : σ → σ')
    (h : ∀ t s, (impl' t).run (g s) = (fun p ↦ (p.1, g p.2)) <$> (impl t).run s)
    (X : QOC W spec α) (s : σ) :
    close impl' X (g s) = (fun p ↦ (p.1, g p.2)) <$> close impl X s := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | t
    · rw [close_instr_bind, close_instr_bind, map_bind]
      simp only [ih]
    · rw [close_query_bind, close_query_bind, h, liftU_map, bind_map_left, map_bind]
      simp only [ih]

/-- The implementation "classical wrapper `I`, then game `O`" with the joint state. -/
def compImpl {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {τ σ : Type}
    (O : QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (I : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec')))) :
    QueryImpl spec (StateT (τ × σ) ProbComp) :=
  fun q ↦ StateT.mk fun ts ↦
    (fun p ↦ (p.1.1, (p.1.2, p.2))) <$> (simulateQ O ((I q).run ts.1)).run ts.2

/-- Closing a wrapped machine is closing the machine with the composite implementation. -/
theorem close_wrap_eq {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {τ σ : Type}
    (O : QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (I : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec'))))
    (X : QOC W spec α) (t : τ) (s : σ) :
    close O (wrap I X t) s = (fun p ↦ ((p.1, p.2.1), p.2.2)) <$> close (compImpl O I) X (t, s) := by
  induction X using OracleComp.inductionOn generalizing t s with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [wrap_instr_bind, close_instr_bind, close_instr_bind, map_bind]
      simp only [ih]
    · rw [wrap_query_bind, close_bind, close_liftQ, close_query_bind]
      simp only [compImpl, StateT.run_mk, liftU_map, bind_map_left, map_bind, ih]

theorem monadLift_eq_liftL {ι' : Type} {spec' : OracleSpec ι'} {β : Type} (oa : ProbComp β) :
    (monadLift oa : OracleComp (unifSpec + spec') β) = liftL oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [liftL]
  | query_bind n k ih =>
    simp [liftL, ih]
    rfl

end closeLemmas

/-! ## Part A: the FORS second phase in open form (generic in `prims`) -/

section generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {W : Type} [Fintype W]

attribute [local instance] Lazy.openQ Lazy.closedQ

open Resources2
open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity (findOracles)

/-- Query-by-query interpretation of a FORS open program: uniform bits, openings answered by
`findOracles tg` (state: the opened indices), secrets from the table, hash queries by `ans`. -/
noncomputable def fImpl (ans : QueryImpl (publicHashSpec prims.core) Id)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) :
    QueryImpl (Lazy.OSpec prims (forsG prims)) (StateT (List ℕ) ProbComp)
  | .inl n => StateT.mk fun s ↦ (fun u ↦ (u, s)) <$> (liftM (unifSpec.query n) : ProbComp _)
  | .inr (.inl t) => findOracles tg (.inr t)
  | .inr (.inr (.inl d)) => StateT.mk fun s ↦ pure (tbl d, s)
  | .inr (.inr (.inr q)) => StateT.mk fun s ↦ pure (ans q, s)

theorem fImpl_bridge (ans : QueryImpl (publicHashSpec prims.core) Id)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) {α : Type}
    (P : OracleComp (Lazy.OSpec prims (forsG prims)) α) (s : List ℕ) :
    (simulateQ (fImpl ans tbl tg) P).run s =
      (simulateQ (findOracles tg) (simulateQ (Lazy.tblImpl (gspec := forsG prims) ans tbl) P)).run s := by
  induction P using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n | t | d | q
    · simp only [ih]
      simp [fImpl, Lazy.tblImpl, findOracles]
    · simp only [ih]
      simp [fImpl, Lazy.tblImpl]
    · simp only [ih]
      simp [fImpl, Lazy.tblImpl]
    · simp only [ih]
      simp [fImpl, Lazy.tblImpl]

/-- The opened FORS leaves of a signing transcript (as in `openPreAnswer`). -/
def fOpened (pk : PublicKeyCore prims.core) (log : G2Log prims) : List (Adrs × ℕ) :=
  openedLeaves pk (G2Log.signed log)

theorem fOpened_append (pk : PublicKeyCore prims.core) (log : G2Log prims) (msg : List Byte)
    (a R : prims.Y) :
    fOpened pk (log ++ [(msg, a, R)]) = fOpened pk log ++ forsIndices vp (digestParts pk R msg) := by
  simp [fOpened, openedLeaves, G2Log.signed, List.flatMap_append]

/-- One simulated signature, open form, returning also the leaves it opens (one more `H_msg`). -/
noncomputable def fSignOpen (pk : PublicKeyCore prims.core) (ys : List prims.Y) (m : List Byte)
    (R : prims.Y) :
    OracleComp (Lazy.OSpec prims (forsG prims))
      (GeneralScheme.SignatureCore vp prims.core × List (Adrs × ℕ)) := do
  let sig ← forsSignOpen pk ys m R
  let d ← (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot m :
    OracleComp (Lazy.OSpec prims (forsG prims)) (Bytes vp.params.m))
  pure (sig, forsIndices vp (splitDigest vp.params d))

/-- Open form of `openPreAnswer` with the opened leaves given: `H_msg` of the forgery and one
`F` per FORS tree. -/
def fAnswerO (pk : PublicKeyCore prims.core) (ys : List prims.Y) (opened : List (Adrs × ℕ))
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y) := do
  let digest ← PublicHash.hmsg prims.core sig.randomness pk.pkSeed pk.pkRoot msg
  let parts : DigestParts vp.params := splitDigest vp.params digest
  let imgs ← Vector.ofFnM fun i : Fin vp.params.k =>
    PublicHash.f prims.core pk.pkSeed (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i))
      (sig.fors[i.val]).sk
  return ((List.finRange vp.params.k).findSome? fun i =>
    if (parts.forsAdrs, leafIndex parts i) ∉ opened ∧
        imgs[i.val] = leafImage (vp := vp) ys
          (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)) then
      some (leafTarget vp prims (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)),
        (sig.fors[i.val]).sk)
    else none).getD (0, default)

theorem fAnswerO_tbl (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core)
    (ys : List prims.Y) (log : G2Log prims) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (fAnswerO pk ys (fOpened pk log) msg sig) = pure (openPreAnswer pk ys log msg sig) := by
  have hf : ∀ (a : Adrs) (y : prims.Y), (Lazy.tblHom (gspec := forsG prims) tbl).toMonadHom
      (PublicHash.f prims.core pk.pkSeed a y) = pure (prims.F pk.pkSeed a y) := fun a y =>
    (Lazy.tblHom (gspec := forsG prims) tbl).map_query' _
  have hm : ∀ (R : prims.Y) (m : List Byte),
      simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot m) =
      pure (prims.Hmsg R pk.pkSeed pk.pkRoot m) := fun R m =>
    (Lazy.tblHom (gspec := forsG prims) tbl).map_query' _
  have himgs : ∀ parts : DigestParts vp.params,
      simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (Vector.ofFnM fun i : Fin vp.params.k =>
          PublicHash.f prims.core pk.pkSeed (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i))
            (sig.fors[i.val]).sk) =
      pure (Vector.ofFn fun i : Fin vp.params.k =>
        prims.F pk.pkSeed (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i))
          (sig.fors[i.val]).sk) := fun parts =>
    (Vector.ofFnM_natural (Lazy.tblHom (gspec := forsG prims) tbl).toMonadHom _
      (fun i => pure (prims.F pk.pkSeed (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i))
          (sig.fors[i.val]).sk)) (fun i => hf _ _)).trans
      (Vector.ofFnM_pure_comp (m := OracleComp (unifSpec + forsG prims))
        (f := fun i : Fin vp.params.k =>
          prims.F pk.pkSeed (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i))
            (sig.fors[i.val]).sk))
  unfold fAnswerO
  rw [simulateQ_bind, hm, pure_bind, simulateQ_bind, himgs, pure_bind, simulateQ_pure]
  unfold openPreAnswer fOpened openedLeaves digestParts
  simp only [Vector.getElem_ofFn]

theorem fSignOpen_tbl (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core)
    (ys : List prims.Y) (m : List Byte) (R : prims.Y) :
    simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (fSignOpen pk ys m R) =
      (fun sig ↦ (sig, forsIndices vp (digestParts pk R m))) <$> Reduction.openSign pk tbl ys m R := by
  have hm : simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
      (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot m) =
      pure (prims.Hmsg R pk.pkSeed pk.pkRoot m) :=
    (Lazy.tblHom (gspec := forsG prims) tbl).map_query' _
  unfold fSignOpen
  rw [simulateQ_bind, forsSignOpen_tbl, map_eq_bind_pure_comp]
  refine bind_congr fun sig ↦ ?_
  rw [simulateQ_bind, hm, pure_bind, simulateQ_pure]
  rfl

/-- The forger's classical interface in the FORS second phase, open form: state = (signing
transcript, opened target indices, opened FORS leaves). -/
noncomputable def fSignS (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (ans : QueryImpl (publicHashSpec prims.core) Id) (tbl : SecretTable vp prims)
    (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y) (pkSeed : prims.PkSeed)
    (root : prims.Y) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims × List ℕ × List (Adrs × ℕ)) ProbComp)
  | .inl n => StateT.mk fun s ↦ (fun p ↦ (p.1, (s.1, p.2, s.2.2))) <$>
      (simulateQ (findOracles tg)
        (liftM (unifSpec.query n) : OracleComp (unifSpec + forsG prims) _)).run s.2.1
  | .inr msg => StateT.mk fun s ↦ do
      let addrnd ← optRand ⟨pkSeed, root⟩
      let R ← lazyRandomizer s.1 msg addrnd
      let r ← (simulateQ (fImpl ans tbl tg) (fSignOpen ⟨pkSeed, root⟩ ys msg R)).run s.2.1
      pure (r.1.1, (s.1 ++ [(msg, addrnd, R)], r.2, s.2.2 ++ r.1.2))

/-- **The FORS second phase in open form** (shared by `qToTcr` and `qToDspr`). -/
noncomputable def fRun (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (ans : QueryImpl (publicHashSpec prims.core) Id)
    (main : PublicKeyCore prims.core →
      QOC W (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
        (List Byte × GeneralScheme.SignatureCore vp prims.core))
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pkSeed : prims.PkSeed) : Closed W ((ℕ × prims.Y) × List ℕ) :=
  liftU (simulateQ (qmImpl ans st.1) (Lazy.openKeygen prims []ₒ pkSeed)) >>= fun root =>
  close (fSignS optRand ans st.1 st.2.1 st.2.2 pkSeed root) (main ⟨pkSeed, root⟩) ([], [], []) >>=
    fun z => liftU ((simulateQ (fImpl ans st.1 st.2.1)
      (fAnswerO ⟨pkSeed, root⟩ st.2.2 z.2.2.2 z.1.1 z.1.2)).run z.2.2.1)

/-- The wrapper of `qOpenPreFind`. -/
noncomputable abbrev fWrapI (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (tbl : SecretTable vp prims) (ys : List prims.Y) (pk : PublicKeyCore prims.core) :=
  (QueryImpl.ofLift unifSpec (OracleComp (unifSpec + forsG prims))).liftTarget
      (StateT (G2Log prims) (OracleComp (unifSpec + forsG prims))) +
    logSignOracle optRand pk lazyRandomizerLift (Reduction.openSign pk tbl ys)

theorem fSignS_step (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pkSeed : prims.PkSeed)
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)).Domain)
    (s : G2Log prims × List ℕ) :
    (fSignS optRand (PublicHash.impl prims) tbl tg ys pkSeed (idealRoot vp prims tbl pkSeed) t).run
        (s.1, s.2, fOpened (idealPk vp prims tbl pkSeed) s.1) =
      (fun p ↦ (p.1, (p.2.1, p.2.2, fOpened (idealPk vp prims tbl pkSeed) p.2.1))) <$>
        (compImpl (findOracles tg) (fWrapI optRand tbl ys (idealPk vp prims tbl pkSeed)) t).run s := by
  obtain ⟨log, op⟩ := s
  rcases t with n | msg
  · simp [fSignS, compImpl]
  · have hF : ForwardsUnif (findOracles (M := prims.Y) tg) := forwardsUnif_ofLift_add _
    simp [fSignS, compImpl, logSignOracle, fWrapI]
    simp only [lazyRandomizerLift, monadLift_eq_liftL, hF.run_simulateQ_liftL, fImpl_bridge,
      fSignOpen_tbl, simulateQ_map, StateT.run_map, bind_map_left, Functor.map_map,
      fOpened_append]
    rfl

/-- **Part A.** The shared second phase `qFindRun Q st pkSeed` of `qToTcr Q` and `qToDspr Q` is
the open-form machine at the true hash answers. -/
theorem qFindRun_eq_fRun (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    {pkSeedDist : ProbComp prims.PkSeed} (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pkSeed : prims.PkSeed) :
    qFindRun Q st pkSeed = fRun optRand (PublicHash.impl prims) Q.main st pkSeed := by
  obtain ⟨tbl, tg, ys⟩ := st
  unfold qFindRun qOpenPreFind qRunForgerLog fRun
  rw [qmImpl_openKeygen, liftU_pure, pure_bind]
  dsimp only
  rw [close_bind, close_wrap_eq]
  have hg := close_map_state (W := W)
    (compImpl (findOracles tg) (fWrapI optRand tbl ys (idealPk vp prims tbl pkSeed)))
    (fSignS optRand (PublicHash.impl prims) tbl tg ys pkSeed (idealRoot vp prims tbl pkSeed))
    (fun s ↦ (s.1, s.2, fOpened (idealPk vp prims tbl pkSeed) s.1))
    (fun t s ↦ fSignS_step optRand tbl tg ys pkSeed t s)
    (Q.main ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩) ([], [])
  have h0 : ((([] : G2Log prims), ([] : List ℕ)).1, (([] : G2Log prims), ([] : List ℕ)).2,
      fOpened (idealPk vp prims tbl pkSeed) (([] : G2Log prims), ([] : List ℕ)).1) =
      (([] : G2Log prims), ([] : List ℕ), ([] : List (Adrs × ℕ))) := rfl
  rw [h0] at hg
  change _ = (close (fSignS optRand (PublicHash.impl prims) tbl tg ys pkSeed
      (idealRoot vp prims tbl pkSeed)) (Q.main ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩)
      ([], [], []) >>= _)
  rw [hg, bind_map_left, bind_map_left]
  refine bind_congr fun p ↦ ?_
  rw [close_liftQ, fImpl_bridge]
  dsimp only
  erw [fAnswerO_tbl tbl (idealPk vp prims tbl pkSeed) ys p.2.1 p.1.1 p.1.2]

end generic

/-! ## Part B: the machine family in the port function -/

section mach

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- State of the FORS first phase (table, sampled targets, leaf images). -/
abbrev ForsSt (ω₀ : Ω128 c) : Type :=
  SecretTable Link.vp (primsΩ ω₀) × List ((primsΩ ω₀).AdrsKey × (primsΩ ω₀).Y) ×
    List (primsΩ ω₀).Y

/-- **The FORS second-phase machine family** for the fixed world `ω₀`, state `st`, seed `pk`. -/
noncomputable def forsMach (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed)
    (H : EncX c → EncY) : Closed (WS (EncX c) EncY E) ((ℕ × (primsΩ ω₀).Y) × List ℕ) :=
  fRun (optRandOf c optRand₀ ω₀) (hashH c ω₀ H) (qmForger c F ω₀ H) st pk

theorem forsMach_encΩ (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed) (T) :
    forsMach c optRand₀ F ω₀ st pk (encΩ { ω₀ with thash := T }) =
      qFindRun (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T }) st pk := by
  have h1 := qFindRun_eq_fRun (optRandOf c optRand₀ { ω₀ with thash := T })
    (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T }) st pk
  rw [internalΩ_main_withThash, impl_primsΩ_withThash] at h1
  refine Eq.trans ?_ h1.symm
  unfold forsMach
  qm_kernel_rfl

end mach

/-! ## Part C: the machine family is `PUE` -/

section pue

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Interpreting an open program with a STATEFUL implementation depending on the port function. -/
theorem evalCost_simulateQ_run {κ σ γ : Type} {sp : OracleSpec κ}
    (impl : (X → Y) → QueryImpl sp (StateT σ ProbComp)) (w : sp.Domain → ℕ)
    (hw : ∀ t s, EvalCost (fun H ↦ (impl H t).run s) (w t))
    (P : OracleComp sp γ) (n : ℕ) (hP : WCount w P n) (s : σ) :
    EvalCost (fun H ↦ (simulateQ (impl H) P).run s) n := by
  induction P using OracleComp.inductionOn generalizing n s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact (EvalCost.const (pure (a, s))).mono (Nat.zero_le _)
  | query_bind t k ih =>
    rw [wCount_query_bind] at hP
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have h := EvalCost.bind (hw t s)
      (g := fun r H ↦ (_root_.simulateQ (impl H) (k r.1)).run r.2) fun r ↦ ih r.1 _ (hP.2 r.1) r.2
    have e : w t + (n - w t) = n := by omega
    rw [e] at h
    exact h

end pue

section pueFors

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

attribute [local instance] Lazy.openQ Lazy.closedQ

open Resources2

/-- Own hash evaluations of the FORS second phase: key generation, `qs` simulated signatures
(each with one extra `H_msg` recording its opened leaves), the answer (`H_msg` + `k` `F`). -/
def forsMHashes (vp : ValidatedParams) (qs : ℕ) : ℕ :=
  Lazy.keygenHashes vp + qs * (forsSignHashes vp + 1) + (1 + vp.params.k)

theorem evalCost_fImpl (ω₀ : Ω128 c) (tbl : SecretTable Link.vp (primsΩ ω₀))
    (tg : List ((primsΩ ω₀).AdrsKey × (primsΩ ω₀).Y))
    (t : (Lazy.OSpec (primsΩ ω₀) (forsG (primsΩ ω₀))).Domain) (s : List ℕ) :
    EvalCost (fun H ↦ (fImpl (hashH c ω₀ H) tbl tg t).run s)
      (if Lazy.kind t = .hash then 1 else 0) := by
  rcases t with n | t | d | q
  · exact EvalCost.const _
  · exact EvalCost.const _
  · exact EvalCost.const _
  · have e : (fun H ↦ (fImpl (hashH c ω₀ H) tbl tg (.inr (.inr (.inr q)))).run s) =
        fun H ↦ (fun y ↦ (y, s)) <$> (pure (hashH c ω₀ H q) : ProbComp _) := by
      funext H
      simp [fImpl]
    rw [e]
    exact ((evalCost_hashH c ω₀ q).map _).mono (by simp [Lazy.kind])

theorem evalCost_fOpen (ω₀ : Ω128 c) (tbl : SecretTable Link.vp (primsΩ ω₀))
    (tg : List ((primsΩ ω₀).AdrsKey × (primsΩ ω₀).Y)) {γ : Type}
    (P : OracleComp (Lazy.OSpec (primsΩ ω₀) (forsG (primsΩ ω₀))) γ) (k : ℕ)
    (hP : IsQueryBoundP P (fun t ↦ Lazy.kind t = .hash) k) (s : List ℕ) :
    EvalCost (fun H ↦ (simulateQ (fImpl (hashH c ω₀ H) tbl tg) P).run s) k :=
  evalCost_simulateQ_run (fun H ↦ fImpl (hashH c ω₀ H) tbl tg) _
    (evalCost_fImpl c ω₀ tbl tg) P k (wCount_of_isQueryBoundP _ P k hP) s

theorem fSignOpen_hashes (ω₀ : Ω128 c) (pk : PublicKeyCore (primsΩ ω₀).core)
    (ys : List (primsΩ ω₀).Y) (m : List Byte) (R : (primsΩ ω₀).Y) :
    IsQueryBoundP (fSignOpen pk ys m R) (fun t ↦ Lazy.kind t = .hash)
      (forsSignHashes Link.vp + 1) := by
  unfold fSignOpen
  refine Lazy.qb_bind _ ((forsSignOpen_kindBound .hash pk ys m R).mono ?_) fun sig ↦
    Lazy.qb_bind _ (m := 0) (Lazy.query_kindBound .hash _) fun d ↦ isQueryBoundP_pure _ _ _
  simpa [Lazy.ind] using forsSignB_hash (vp := Link.vp)

theorem fAnswerO_hashes (ω₀ : Ω128 c) (pk : PublicKeyCore (primsΩ ω₀).core)
    (ys : List (primsΩ ω₀).Y) (opened : List (Adrs × ℕ)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core) :
    IsQueryBoundP (fAnswerO pk ys opened msg sig) (fun t ↦ Lazy.kind t = .hash)
      (1 + Link.vp.params.k) := by
  unfold fAnswerO
  refine (Lazy.qb_bind _ (Lazy.query_kindBound .hash _) fun digest ↦
    Lazy.qb_bind _ (m := 0) (Lazy.qb_ofFnM _ _ (Lazy.ind .hash .hash) fun i ↦
      Lazy.query_kindBound .hash _) fun imgs ↦ isQueryBoundP_pure _ _ _).mono ?_
  simp only [Lazy.ind]
  split <;> simp

theorem evalCost_fSignS (ω₀ : Ω128 c) (tbl : SecretTable Link.vp (primsΩ ω₀))
    (tg : List ((primsΩ ω₀).AdrsKey × (primsΩ ω₀).Y)) (ys : List (primsΩ ω₀).Y)
    (pkSeed : (primsΩ ω₀).PkSeed) (root : (primsΩ ω₀).Y)
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core)).Domain)
    (s : G2Log (primsΩ ω₀) × List ℕ × List (Adrs × ℕ)) :
    EvalCost (fun H ↦
      (fSignS (optRandOf c optRand₀ ω₀) (hashH c ω₀ H) tbl tg ys pkSeed root t).run s)
      (sgnW (forsSignHashes Link.vp + 1) t) := by
  rcases t with n | msg
  · exact EvalCost.const _
  · change EvalCost (fun H ↦ optRandOf c optRand₀ ω₀ ⟨pkSeed, root⟩ >>= fun addrnd ↦
      lazyRandomizer s.1 msg addrnd >>= fun R ↦
        (simulateQ (fImpl (hashH c ω₀ H) tbl tg) (fSignOpen ⟨pkSeed, root⟩ ys msg R)).run s.2.1 >>=
          fun r ↦ (pure (r.1.1, (s.1 ++ [(msg, addrnd, R)], r.2, s.2.2 ++ r.1.2)) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := EncX c) (Y := EncY)
        (optRandOf c optRand₀ ω₀ ⟨pkSeed, root⟩)) fun addrnd ↦
      EvalCost.bind (EvalCost.const (X := EncX c) (Y := EncY) (lazyRandomizer s.1 msg addrnd))
        fun R ↦ EvalCost.bind (evalCost_fOpen c ω₀ tbl tg _ _
          (fSignOpen_hashes c ω₀ ⟨pkSeed, root⟩ ys msg R) s.2.1)
          fun r ↦ EvalCost.const (X := EncX c) (Y := EncY)
            (pure (r.1.1, (s.1 ++ [(msg, addrnd, R)], r.2, s.2.2 ++ r.1.2)) : ProbComp _)
    exact h.mono (by simp)

/-- **`PUE`.**  The FORS second-phase machine family makes at most `q + forsMHashes qs` port
calls plus evaluations on every path. -/
theorem pue_forsMach (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (forsMach c optRand₀ F ω₀ st pk) (q + forsMHashes Link.vp qs) := by
  unfold forsMach fRun
  have hB : ∀ root : (primsΩ ω₀).Y, PUE (spec := unifSpec) cnt0 (fun H ↦
      close (fSignS (optRandOf c optRand₀ ω₀) (hashH c ω₀ H) st.1 st.2.1 st.2.2 pk root)
          (qmForger c F ω₀ H ⟨pk, root⟩) ([], [], []) >>= fun z ↦
        liftU ((simulateQ (fImpl (hashH c ω₀ H) st.1 st.2.1)
          (fAnswerO ⟨pk, root⟩ st.2.2 z.2.2.2 z.1.1 z.1.2)).run z.2.2.1))
      (q + qs * (forsSignHashes Link.vp + 1) + (1 + Link.vp.params.k)) := by
    intro root
    refine PUE.bind (PUE.close _ (evalCost_fSignS c optRand₀ ω₀ st.1 st.2.1 st.2.2 pk root)
      (pue_qmForger c F ω₀ q qs _ hq hqs ⟨pk, root⟩) _) fun z ↦ ?_
    have h := PUE.liftU_bind (E := E) (B := fun o _ ↦ (pure o : Closed (WS (EncX c) EncY E) _))
      (q := 0) (evalCost_fOpen c ω₀ st.1 st.2.1 _ _
        (fAnswerO_hashes c ω₀ ⟨pk, root⟩ st.2.2 z.2.2.2 z.1.1 z.1.2) z.2.2.1) fun o ↦ PUE.pure o 0
    simpa using h
  have h := PUE.liftU_bind (evalCost_open c ω₀ st.1 _ _ (keygen_hashes c ω₀ pk)) hB
  refine h.mono ?_
  unfold forsMHashes
  omega

end pueFors

/-! ## Delivered statements -/

section deliver

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- The SM-TCR (FORS) second-phase machine family. -/
noncomputable def forsTcrMach (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed)
    (H : EncX c → EncY) : Closed (WS (EncX c) EncY E) (ℕ × (primsΩ ω₀).Y) :=
  forsMach c optRand₀ F ω₀ st pk H >>= fun r ↦ liftU (pure (r.1.1, r.1.2))

/-- The SM-DSPR (FORS) second-phase machine family. -/
noncomputable def forsDsprMach (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed)
    (H : EncX c → EncY) : Closed (WS (EncX c) EncY E) (ℕ × Bool) :=
  forsMach c optRand₀ F ω₀ st pk H >>= fun r ↦
    liftU (pure (r.1.1, decide (((st.2.1[r.1.1]?.map Prod.snd).getD default) ≠ r.1.2 ∨
      r.1.1 ∈ r.2)))

theorem forsTcrMach_encΩ (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed) (T) :
    forsTcrMach c optRand₀ F ω₀ st pk (encΩ { ω₀ with thash := T }) =
      (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).forge st pk := by
  unfold forsTcrMach
  rw [forsMach_encΩ c optRand₀ pkSeedDist₀ F ω₀ st pk T]
  rfl

theorem forsDsprMach_encΩ (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed) (T) :
    forsDsprMach c optRand₀ F ω₀ st pk (encΩ { ω₀ with thash := T }) =
      (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).guess st pk := by
  unfold forsDsprMach
  rw [forsMach_encΩ c optRand₀ pkSeedDist₀ F ω₀ st pk T]
  rfl

theorem pue_forsTcrMach (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (forsTcrMach c optRand₀ F ω₀ st pk) (q + forsMHashes Link.vp qs) := by
  have h := PUE.bind (q₂ := 0) (pue_forsMach c optRand₀ F ω₀ st pk q qs hq hqs)
    (B := fun r _ ↦ (pure (r.1.1, r.1.2) : Closed (WS (EncX c) EncY E) _))
    fun r ↦ PUE.pure _ 0
  unfold forsTcrMach
  simpa using h

theorem pue_forsDsprMach (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (forsDsprMach c optRand₀ F ω₀ st pk) (q + forsMHashes Link.vp qs) := by
  have h := PUE.bind (q₂ := 0) (pue_forsMach c optRand₀ F ω₀ st pk q qs hq hqs)
    (B := fun r _ ↦ (pure (r.1.1, decide (((st.2.1[r.1.1]?.map Prod.snd).getD default) ≠ r.1.2 ∨
      r.1.1 ∈ r.2)) : Closed (WS (EncX c) EncY E) _))
    fun r ↦ PUE.pure _ 0
  unfold forsDsprMach
  simpa using h

/-- **Machine family, `tcrFv`**: one `PUE` family in the port function equal, at the port
function of every world `{ω₀ with thash := T}`, to the second phase of `qToTcr` there. -/
theorem fors_tcr_mach_exists (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (EncX c → EncY) → Closed (WS (EncX c) EncY E) (ℕ × (primsΩ ω₀).Y),
      PUE (spec := unifSpec) cnt0 Mach (q + forsMHashes Link.vp qs) ∧
      ∀ T, Mach (encΩ { ω₀ with thash := T }) =
        (qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).forge st pk :=
  ⟨forsTcrMach c optRand₀ F ω₀ st pk, pue_forsTcrMach c optRand₀ F ω₀ st pk q qs hq hqs,
    forsTcrMach_encΩ c optRand₀ pkSeedDist₀ F ω₀ st pk⟩

/-- **Machine family, `dspr`.** -/
theorem fors_dspr_mach_exists (ω₀ : Ω128 c) (st : ForsSt c ω₀) (pk : (primsΩ ω₀).PkSeed)
    (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (EncX c → EncY) → Closed (WS (EncX c) EncY E) (ℕ × Bool),
      PUE (spec := unifSpec) cnt0 Mach (q + forsMHashes Link.vp qs) ∧
      ∀ T, Mach (encΩ { ω₀ with thash := T }) =
        (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).guess st pk :=
  ⟨forsDsprMach c optRand₀ F ω₀ st pk, pue_forsDsprMach c optRand₀ F ω₀ st pk q qs hq hqs,
    forsDsprMach_encΩ c optRand₀ pkSeedDist₀ F ω₀ st pk⟩

/-- **`hModel` of `qfors`, `tcrFv`**, discharged with `q' = q + forsMHashes Link.vp qs`. -/
theorem forsTcr_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : Ω128 c) (st : Open.ForsP1State Link.vp (primsΩ ω₀))
      (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n)
          (q + forsMHashes Link.vp qs),
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToTcr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mo, hMo⟩ := (pue_forsTcrMach c optRand₀ F ω₀ st pk q qs hq hqs).exists_model ρ
  refine ⟨Mo, fun T Ev _ ↦ ?_⟩
  rw [hMo, forsTcrMach_encΩ c optRand₀ pkSeedDist₀ F ω₀ st pk T, hρ]

/-- **`hModel` of `qfors`, `dspr`**, with `q' = q + forsMHashes Link.vp qs`: the model is the
model `HybridModel.ofProgram` of a one-port program, hence `Additive`; its `RowsBound` is taken
from the named hypothesis `hRows` ("`RowsBound` holds for `ofProgram` models", NOT proved: it is
proved only for `ofSecondPort` models, `ofSecondPort_rowsBound`). -/
theorem forsDspr_hModel (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hRows : ∀ (x : QuantumComp LocalSig.instruments.{0} (qromSpec (EncX c) EncY)
        (fun _ ↦ ℕ × Bool) (progReg (EncX c) EncY E)) (ρ : SubState ((EncX c × EncY) × E))
        (hx : x.IsQueryBound (fun _ ↦ q + forsMHashes Link.vp qs)),
      PQ.QROM.Rows.RowsBound (fun H Ev ↦ ((PQ.QROM.HybridModel.ofProgram
        LocalSig.Interp.instruments x ρ (q + forsMHashes Link.vp qs) hx Sigma.snd).prob H Ev).toReal)
        (q + forsMHashes Link.vp qs)) :
    ∀ (ω₀ : Ω128 c) (st : Open.ForsP1State Link.vp (primsΩ ω₀))
      (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bool) (q + forsMHashes Link.vp qs),
        Mo.Additive ∧
        PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) (q + forsMHashes Link.vp qs) ∧
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bool → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).guess st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨x, hx, hxe⟩ := (pue_forsDsprMach c optRand₀ F ω₀ st pk q qs hq hqs).exists_prog_qprob
  refine ⟨PQ.QROM.HybridModel.ofProgram LocalSig.Interp.instruments x ρ _ hx Sigma.snd,
    PQ.QROM.HybridModel.ofProgram_additive _ x ρ _ hx Sigma.snd, hRows x ρ hx, fun T Ev _ ↦ ?_⟩
  refine (hxe Ev _ ρ).trans ?_
  rw [forsDsprMach_encΩ c optRand₀ pkSeedDist₀ F ω₀ st pk T, hρ]

/-- The count at SLH-DSA-SHA2-128s. -/
theorem forsMHashes_128s (qs : ℕ) : forsMHashes Link.vp qs = 269839 + qs * 1950028 := by
  unfold forsMHashes
  rw [keygenHashes_128s, Resources2.forsSignHashes_128s]
  have hk : Link.vp.params.k = 14 := rfl
  rw [hk]
  ring

/-- The count is the `tcrFv` and the `dspr` field of `openCounts128s qs`. -/
theorem forsMHashes_openCounts128s (qs : ℕ) :
    forsMHashes Link.vp qs = (openCounts128s qs).tcrFv ∧
    forsMHashes Link.vp qs = (openCounts128s qs).dspr := by
  simp only [forsMHashes_128s, openCounts128s, and_self]

end deliver

end Reduction
