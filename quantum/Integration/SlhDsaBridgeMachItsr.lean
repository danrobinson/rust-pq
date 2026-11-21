import Integration.SlhDsaBridgeMach
import PQ.Interactive.QromBridgeEvalQ

/-!
# The ITSR reduction machine (`qbItsrL`) as a `PUE` family in the port function

NOT part of the default target; compiled by hand like `scripts/check-integration.sh` step 3.

`qbItsrL Q = qLazyRun (PublicHash.impl prims) (qItsrOpen Q)` is not closed: it talks to the
ITSR game's target oracle.  So the family is a `PUE` family over the interface
`unifSpec + Lazy.itsrG prims` (weights `0`: target queries are the game's, counted by the game),
not a closed machine; the varied component is `hmsg`.

* `qmItsrOpen` (`qItsrOpen` with the forger program as argument), `qbItsrL_eq` (`rfl`).
* `itsrMach … ω₀ H`, `itsrMach_encΩ` (equation at `{ω₀ with hmsg := Hm}`), `pue_itsrMach`
  (budget `q + itsrHashes Link.vp qs`), `itsr_mach_exists` (primitive form),
  `itsrHashes_openCounts128s`.
* Not done: an `IAdv`/`QuantumComp` program over the `H_msg` component alone (what
  `qprf`'s Part-C `hModel` needs); see `quantum/HANDOFF-qmach.md`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Reduction

section generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {W : Type} [Fintype W]

/-- `qItsrOpen` with the forger program as argument. -/
noncomputable def qmItsrOpen (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (main : PublicKeyCore prims.core →
      QOC W (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
        (List Byte × GeneralScheme.SignatureCore vp prims.core)) :
    QOC W (Lazy.OSpec prims (Lazy.itsrG prims)) (prims.Y × ItsrIn prims) :=
  liftQ (liftM pkSeedDist : OracleComp (Lazy.OSpec prims (Lazy.itsrG prims)) prims.PkSeed) >>=
    fun pkSeed ↦
  liftQ (Lazy.openKeygen prims (Lazy.itsrG prims) pkSeed) >>= fun root ↦
  wrap ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims (Lazy.itsrG prims)))).liftTarget
        (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (Lazy.itsrG prims)))) +
      logSignOracle optRand ⟨pkSeed, root⟩ (Lazy.itsrRandomizerO pkSeed root)
        (fun m R ↦ Lazy.openSign prims (Lazy.itsrG prims) m pkSeed root R))
    (main ⟨pkSeed, root⟩) [] >>= fun z ↦
  liftQ (pure (z.1.2.randomness, (pkSeed, root, z.1.1)))

theorem qbItsrL_eq (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    {pkSeedDist : ProbComp prims.PkSeed}
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qbItsrL Q = qLazyRun (PublicHash.impl prims) (qmItsrOpen optRand pkSeedDist Q.main) := rfl

/-- One step of the ITSR adversary's signing harness: at most `signHashes` hash queries per
signing query, none otherwise. -/
theorem itsr_step_hashes (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeed : prims.PkSeed) (root : prims.Y)
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)).Domain)
    (s : G2Log prims) :
    IsQueryBoundP ((((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims (Lazy.itsrG prims)))).liftTarget
          (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (Lazy.itsrG prims)))) +
        logSignOracle optRand ⟨pkSeed, root⟩ (Lazy.itsrRandomizerO pkSeed root)
          (fun m R ↦ Lazy.openSign prims (Lazy.itsrG prims) m pkSeed root R)) t).run s)
      (fun t ↦ Lazy.kind t = .hash) (sgnW (Lazy.signHashes vp) t) := by
  cases t with
  | inl n =>
    simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
    exact Lazy.qb_bind (fun t ↦ Lazy.kind t = .hash) (m := 0)
      (Lazy.liftM_kindBound (gspec := Lazy.itsrG prims) (D := SecIdx) (V := prims.Y)
        (hspec := publicHashSpec prims.core) .hash (by decide)
        (liftM (unifSpec.query n) : ProbComp _)) fun x ↦ isQueryBoundP_pure _ (x, s) _
  | inr m =>
    have hstep := Lazy.qb_bind (fun t ↦ Lazy.kind t = .hash)
      (Lazy.liftM_kindBound (gspec := Lazy.itsrG prims) (D := SecIdx) (V := prims.Y)
        (hspec := publicHashSpec prims.core) .hash (by decide) (optRand ⟨pkSeed, root⟩))
      fun addrnd ↦
      Lazy.qb_bind (fun t ↦ Lazy.kind t = .hash)
        (Lazy.itsrRandomizerO_kindBound .hash pkSeed root s m addrnd) fun R ↦
        Lazy.qb_bind (fun t ↦ Lazy.kind t = .hash) (m := 0)
          (Lazy.openSign_kindBound (gspec := Lazy.itsrG prims) .hash m pkSeed root R)
          fun sig ↦ isQueryBoundP_pure _ (sig, s ++ [(m, addrnd, R)]) _
    refine (by simpa [logSignOracle] using hstep : IsQueryBoundP _ _ _).mono ?_
    simpa [Lazy.ind] using Lazy.signB_hash (vp := vp)

theorem keygen_hashesG (pkSeed : prims.PkSeed) :
    IsQueryBoundP (Lazy.openKeygen prims (Lazy.itsrG prims) pkSeed) (fun t ↦ Lazy.kind t = .hash)
      (Lazy.keygenHashes vp) :=
  (Lazy.openKeygen_kindBound .hash pkSeed).mono (by simpa [Lazy.ind] using Lazy.keygenB_hash)

end generic

section mach

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

theorem impl_primsΩ_withHmsg (ω₀ : Ω128 c) (Hm) :
    PublicHash.impl (primsΩ { ω₀ with hmsg := Hm }) = hashH c ω₀ (encΩ { ω₀ with hmsg := Hm }) := by
  funext q
  cases q <;> rfl

theorem internalΩ_main_withHmsg (ω₀ : Ω128 c) (Hm) :
    (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with hmsg := Hm }).main =
      fun pk ↦ qmForger c F ω₀ (encΩ { ω₀ with hmsg := Hm }) pk := by
  funext pk
  simp only [internalΩ, qPureBytesToInternal, qToInternal, qPureBytesToTyped, QForger.wrapForger,
    PortForger.at, qmCSign_eq, qmCRead_eq, pureBytesView]
  rfl

/-- **The ITSR machine family** for the fixed world `ω₀`, as a function of the port function. -/
noncomputable def itsrMach (ω₀ : Ω128 c) (H : EncX c → EncY) :
    QOC (WS (EncX c) EncY E) (unifSpec + Lazy.itsrG (primsΩ ω₀))
      ((primsΩ ω₀).Y × ItsrIn (primsΩ ω₀)) :=
  qLazyRun (hashH c ω₀ H) (qmItsrOpen (optRandOf c optRand₀ ω₀) pkSeedDist₀ (qmForger c F ω₀ H))

set_option maxRecDepth 200000 in
/-- **ITSR, equation.** At the port function of `{ω₀ with hmsg := Hm}` the family is the ITSR
adversary of that world. -/
theorem itsrMach_encΩ (ω₀ : Ω128 c) (Hm) :
    itsrMach c optRand₀ pkSeedDist₀ F ω₀ (encΩ { ω₀ with hmsg := Hm }) =
      qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with hmsg := Hm }) := by
  rw [qbItsrL_eq (optRandOf c optRand₀ { ω₀ with hmsg := Hm }), internalΩ_main_withHmsg,
    impl_primsΩ_withHmsg]
  unfold itsrMach
  qm_kernel_rfl

/-- Hash weight on the open interface of the ITSR adversary. -/
abbrev hashWI (ω₀ : Ω128 c) : (Lazy.OSpec (primsΩ ω₀) (Lazy.itsrG (primsΩ ω₀))).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .hash then 1 else 0

/-- Hash weight on the interface after the lazy cache. -/
abbrev hashWU (ω₀ : Ω128 c) :
    (Lazy.RSpec (Lazy.itsrG (primsΩ ω₀)) Unit (primsΩ ω₀).Y
      (publicHashSpec (primsΩ ω₀).core)).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .hash then 1 else 0

/-- Own hash evaluations of the ITSR adversary (`Open.itsrOpen_hashes`). -/
def itsrHashes (vp : ValidatedParams) (qs : ℕ) : ℕ :=
  Lazy.keygenHashes vp + qs * Lazy.signHashes vp

theorem itsrHashes_openCounts128s (qs : ℕ) :
    itsrHashes Link.vp qs = (openCounts128s qs).itsr := by
  unfold itsrHashes
  rw [keygenHashes_128s, signHashes_128s]
  simp only [openCounts128s]

theorem pue_qmItsrOpen (ω₀ : Ω128 c) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (hashWI c ω₀) (fun H ↦ qmItsrOpen (optRandOf c optRand₀ ω₀) pkSeedDist₀
      (qmForger c F ω₀ H)) (q + itsrHashes Link.vp qs) := by
  unfold qmItsrOpen
  have h0 : WCount (hashWI c ω₀) (liftM pkSeedDist₀ :
      OracleComp (Lazy.OSpec (primsΩ ω₀) (Lazy.itsrG (primsΩ ω₀))) _) 0 :=
    wCount_of_isQueryBoundP _ _ _ (Lazy.liftM_kindBound .hash (by decide) pkSeedDist₀)
  have hk : ∀ pkSeed, WCount (hashWI c ω₀)
      (Lazy.openKeygen (primsΩ ω₀) (Lazy.itsrG (primsΩ ω₀)) pkSeed) (Lazy.keygenHashes Link.vp) :=
    fun pkSeed ↦ wCount_of_isQueryBoundP _ _ _ (keygen_hashesG pkSeed)
  have hrun : ∀ pkSeed root, PUE (hashWI c ω₀) (fun H ↦
      wrap ((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec (primsΩ ω₀)
          (Lazy.itsrG (primsΩ ω₀))))).liftTarget
          (StateT (G2Log (primsΩ ω₀)) (OracleComp (Lazy.OSpec (primsΩ ω₀)
            (Lazy.itsrG (primsΩ ω₀))))) +
        logSignOracle (optRandOf c optRand₀ ω₀) ⟨pkSeed, root⟩
          (Lazy.itsrRandomizerO pkSeed root)
          (fun m R ↦ Lazy.openSign (primsΩ ω₀) (Lazy.itsrG (primsΩ ω₀)) m pkSeed root R))
        (qmForger c F ω₀ H ⟨pkSeed, root⟩) [] >>= fun z ↦
      liftQ (pure (z.1.2.randomness, (pkSeed, root, z.1.1))))
      (q + qs * Lazy.signHashes Link.vp + 0) := by
    intro pkSeed root
    refine PUE.bind (PUE.wrap _ (cnt := sgnW (Lazy.signHashes Link.vp)) ?_
      (pue_qmForger c F ω₀ q qs _ hq hqs ⟨pkSeed, root⟩) []) fun z ↦ ?_
    · exact fun t s ↦ wCount_of_isQueryBoundP _ _ _ (itsr_step_hashes _ pkSeed root t s)
    · simp only [liftQ_pure]
      exact PUE.pure _ 0
  have h := PUE.liftQ_bind _ h0 fun pkSeed ↦ PUE.liftQ_bind _ (hk pkSeed) fun root ↦
    hrun pkSeed root
  refine h.mono ?_
  unfold itsrHashes
  omega

theorem evalCostQ_hashH (ω₀ : Ω128 c) {ι' : Type} {sp : OracleSpec ι'}
    (cnt : (unifSpec + sp).Domain → ℕ)
    (q : PublicHashQuery (primsΩ ω₀).core.PkSeed (primsΩ ω₀).core.AdrsKey (primsΩ ω₀).core.Y) :
    EvalCostQ E cnt (fun H ↦ (pure (hashH c ω₀ H q) :
      OracleComp (unifSpec + sp) ((publicHashSpec (primsΩ ω₀).core).Range q))) 1 := by
  cases q with
  | thash pk a xs =>
    by_cases h : xs.length ≤ c.tl
    · have e : (fun H : EncX c → EncY ↦ (pure (hashH c ω₀ H (.thash pk a xs)) :
          OracleComp (unifSpec + sp) (Bytes Link.vp.params.n))) =
          fun H ↦ pure ((fun y : EncY ↦ y.1) (H (.inl (pk, a, BList.ofList xs h)))) := by
        funext H
        simp [hashH, h]
      exact e ▸ EvalCostQ.eval _ _
    · have e : (fun H : EncX c → EncY ↦ (pure (hashH c ω₀ H (.thash pk a xs)) :
          OracleComp (unifSpec + sp) (Bytes Link.vp.params.n))) = fun _ ↦ pure default := by
        funext H
        simp [hashH, h]
      exact e ▸ (EvalCostQ.const _ (wCount_pure _ _ _)).mono (Nat.zero_le _)
  | hmsg r pk root m =>
    by_cases h : m.length ≤ c.ml
    · have e : (fun H : EncX c → EncY ↦ (pure (hashH c ω₀ H (.hmsg r pk root m)) :
          OracleComp (unifSpec + sp) (Bytes Link.vp.params.m))) =
          fun H ↦ pure ((fun y : EncY ↦ y.2) (H (.inr (.inl (r, pk, root, BList.ofList m h))))) := by
        funext H
        simp [hashH, h]
      exact e ▸ EvalCostQ.eval _ _
    · have e : (fun H : EncX c → EncY ↦ (pure (hashH c ω₀ H (.hmsg r pk root m)) :
          OracleComp (unifSpec + sp) (Bytes Link.vp.params.m))) = fun _ ↦ pure default := by
        funext H
        simp [hashH, h]
      exact e ▸ (EvalCostQ.const _ (wCount_pure _ _ _)).mono (Nat.zero_le _)

/-- **ITSR, `PUE`.**  Target queries weigh `0` (they are the game's). -/
theorem pue_itsrMach (ω₀ : Ω128 c) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (fun _ ↦ 0) (itsrMach c optRand₀ pkSeedDist₀ F ω₀) (q + itsrHashes Link.vp qs) := by
  unfold itsrMach qLazyRun
  refine PUE.wrap0E (fun H ↦ Lazy.interp (hashH c ω₀ H)) (cnt := hashWU c ω₀) ?_
    (PUE.map _ (PUE.wrap _ (cnt := hashWI c ω₀) ?_ (pue_qmItsrOpen c optRand₀ pkSeedDist₀ F ω₀ q qs
      hq hqs) []))
  · intro t
    rcases t with n | t | d | hq'
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact (EvalCostQ.const _ (wCount_zero _ _)).mono (Nat.zero_le _)
    · exact evalCostQ_hashH c ω₀ _ hq'
  · intro t s
    refine wCount_of_isQueryBoundP _ _ _ ?_
    rcases t with n | t | d | hq'
    · simp [Lazy.lazyImplR, Lazy.kind]
    · simp [Lazy.lazyImplR, Lazy.kind]
    · rcases hc : s.lookup d with _ | v
      · rw [Lazy.lazyImplR_sec_run_miss d s hc]
        simp [Lazy.kind]
      · rw [Lazy.lazyImplR_sec_run_hit d s v hc]
        simp
    · simp [Lazy.lazyImplR, Lazy.kind, hashWI]

/-- **ITSR, primitive form.** -/
theorem itsr_mach_exists (ω₀ : Ω128 c) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (EncX c → EncY) → QOC (WS (EncX c) EncY E) (unifSpec + Lazy.itsrG (primsΩ ω₀))
        ((primsΩ ω₀).Y × ItsrIn (primsΩ ω₀)),
      PUE (fun _ ↦ 0) Mach (q + itsrHashes Link.vp qs) ∧
      ∀ Hm, Mach (encΩ { ω₀ with hmsg := Hm }) =
        qbItsrL (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with hmsg := Hm }) :=
  ⟨itsrMach c optRand₀ pkSeedDist₀ F ω₀, pue_itsrMach c optRand₀ pkSeedDist₀ F ω₀ q qs hq hqs,
    fun Hm ↦ itsrMach_encΩ c optRand₀ pkSeedDist₀ F ω₀ Hm⟩

end mach

end Reduction

#print axioms Reduction.itsrMach_encΩ
#print axioms Reduction.pue_itsrMach
#print axioms Reduction.itsr_mach_exists
#print axioms Reduction.itsrHashes_openCounts128s
