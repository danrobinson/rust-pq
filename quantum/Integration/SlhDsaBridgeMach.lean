import Integration.SlhDsaBridgePrf
import Reduction.Open.Tcr
import Reduction.Open.Phase1Tcr
import Reduction.Instance128sV2
import PQ.Interactive.QromBridgeEvalProg

/-!
# The class-TCR reduction machine as a `PUE` family in the port function

NOT part of the default target; compiled by hand like `scripts/check-integration.sh` step 3.

* Part A (generic in `prims`): `qMemoForge_eq_qmMach`: the second phase `qMemoForge n Q s pkSeed`
  of `qbTcrArM n Q` is `qmMach optRand (PublicHash.impl prims) n Q.main s pkSeed`, the machine
  written with the OPEN programs of `security/` (`Lazy.openKeygen`, `Lazy.openSign` per signing
  query, the tail `qmTail` = `H_msg` + `collO`/`verifyFree`) interpreted query by query by
  `qmImpl ans tbl`.  Per-query facts: `Lazy.openKeygen_tbl`, `Lazy.openSign_tbl`,
  `Resources2.collO_tbl`, `Resources2.verifyCalls_eq_free` (through `qmImpl_bridge`).
* Part B: `hashH c ω₀ H` answers each hash query by ONE evaluation of the port function `H`
  (constants out of cap); `impl_primsΩ_withThash`; `tcrMach … ω₀ n st pk H`; `tcrMach_encΩ`.
  The cross-world equation is closed by a kernel-checked `rfl` (`qm_kernel_rfl`) after the
  scheme-dependent wrappers were rewritten away (`qmCSign_eq`, `qmCRead_eq`); a direct
  kernel `rfl` on the unrewritten forger runs out of time/memory.
* Part C: `pue_tcrMach`: budget `q + tcrMHashes Link.vp qs`.
* Delivered: `tcr_mach_exists` (step 3), `tcr_forge_model`, `tcr_forge_model_ρ₀` (step 5),
  `tcr_hModel` (the hypothesis `hModel` of `quantum/HANDOFF-qtcr.md`), `tcrMHashes_openCounts128s`.
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

attribute [local instance] Lazy.openQ

/-- Uniform bits and the empty game, as probabilistic computations. -/
noncomputable def qmToProb : QueryImpl (unifSpec + []ₒ) ProbComp
  | .inl n => (liftM (unifSpec.query n) : ProbComp _)
  | .inr t => PEmpty.elim t

/-- The query-by-query interpretation of an open program (empty game): uniform bits are uniform
bits, secrets are read from the table, hash queries are answered by `ans`. -/
noncomputable def qmImpl (ans : QueryImpl (publicHashSpec prims.core) Id)
    (tbl : SecretTable vp prims) : QueryImpl (Lazy.OSpec prims []ₒ) ProbComp
  | .inl n => (liftM (unifSpec.query n) : ProbComp _)
  | .inr (.inl t) => PEmpty.elim t
  | .inr (.inr (.inl d)) => pure (tbl d)
  | .inr (.inr (.inr q)) => pure (ans q)

theorem simulateQ_qmToProb_pure {α : Type} (a : α) :
    simulateQ qmToProb (pure a : OracleComp (unifSpec + []ₒ) α) = pure a := simulateQ_pure _ _

/-- `qmImpl` is the table interpretation of `security/` followed by `qmToProb`. -/
theorem qmImpl_bridge (ans : QueryImpl (publicHashSpec prims.core) Id)
    (tbl : SecretTable vp prims) {α : Type} (P : OracleComp (Lazy.OSpec prims []ₒ) α) :
    simulateQ (qmImpl ans tbl) P =
      simulateQ qmToProb (simulateQ (Lazy.tblImpl (gspec := []ₒ) ans tbl) P) := by
  induction P using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with n | t | d | q
    · simp only [ih]
      rfl
    · exact PEmpty.elim t
    · simp only [ih]
      simp [qmImpl, Lazy.tblImpl]
    · simp only [ih]
      simp [qmImpl, Lazy.tblImpl]

/-- The verification tail of the second phase as an open program: `H_msg` of the forgery, then
verification with the collision search against `L` interleaved (`collO`). -/
noncomputable def qmTail (pkSeed : prims.PkSeed) (L : List (prims.AdrsKey × List prims.Y))
    (root : prims.Y)
    (z : (List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :
    OracleComp (Lazy.OSpec prims []ₒ) (ℕ × List prims.Y) := do
  let dg ← (PublicHash.hmsg prims.core z.1.2.randomness pkSeed root z.1.1 :
    OracleComp (Lazy.OSpec prims []ₒ) (Bytes vp.params.m))
  let c ← (simulateQ (Resources2.collO (gspec := []ₒ) pkSeed L)
    (Resources2.verifyFree pkSeed (splitDigest vp.params dg) z.1.2)).run none
  return c.2.getD (0, [])

/-- The signing oracle with open signing interpreted by `qmImpl ans tbl`. -/
noncomputable def qmSignO (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (ans : QueryImpl (publicHashSpec prims.core) Id) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (root : prims.Y) :
    QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (StateT (G2Log prims) ProbComp) :=
  fun msg => StateT.mk fun log => do
    let addrnd ← optRand ⟨pkSeed, root⟩
    let R ← lazyRandomizer log msg addrnd
    let sig ← simulateQ (qmImpl ans tbl) (Lazy.openSign prims []ₒ msg pkSeed root R)
    pure (sig, log ++ [(msg, addrnd, R)])

/-- The classical interface of the forger during the second phase. -/
noncomputable def qmImplS (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (ans : QueryImpl (publicHashSpec prims.core) Id) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (root : prims.Y) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
    qmSignO optRand ans tbl pkSeed root

/-- **The second phase of the class-TCR adversary in open form**: key generation, the forger's
run against the signing oracle with open signing, the verification tail; every hash evaluation
is an `ans`-query of an open program. -/
noncomputable def qmMach (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (ans : QueryImpl (publicHashSpec prims.core) Id) (n : ℕ)
    (main : PublicKeyCore prims.core →
      QOC W (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
        (List Byte × GeneralScheme.SignatureCore vp prims.core))
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    Closed W (ℕ × {xs : List prims.Y // xs.length = n}) :=
  liftU (simulateQ (qmImpl ans s.1) (Lazy.openKeygen prims []ₒ pkSeed)) >>= fun root =>
  close (qmImplS optRand ans s.1 pkSeed root) (main ⟨pkSeed, root⟩) [] >>= fun z =>
  liftU (classOut prims n s.2 <$> simulateQ (qmImpl ans s.1) (qmTail pkSeed s.2 root z))

theorem qmImpl_openKeygen (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    simulateQ (qmImpl (PublicHash.impl prims) tbl) (Lazy.openKeygen prims []ₒ pkSeed) =
      pure (idealRoot vp prims tbl pkSeed) := by
  rw [qmImpl_bridge, Lazy.openKeygen_tbl, simulateQ_qmToProb_pure]

theorem qmImpl_openSign (tbl : SecretTable vp prims) (msg : List Byte)
    (pk : PublicKeyCore prims.core) (R : prims.Y) :
    simulateQ (qmImpl (PublicHash.impl prims) tbl)
        (Lazy.openSign prims []ₒ msg pk.pkSeed pk.pkRoot R) =
      pure (idealSign vp prims tbl msg pk R) := by
  rw [qmImpl_bridge, Lazy.openSign_tbl, simulateQ_qmToProb_pure]

theorem qmImpl_tail (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed)
    (L : List (prims.AdrsKey × List prims.Y))
    (z : (List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :
    simulateQ (qmImpl (PublicHash.impl prims) tbl)
        (qmTail pkSeed L (idealRoot vp prims tbl pkSeed) z) =
      pure ((findCollisionM pkSeed L
        (verifyCalls (idealPk vp prims tbl pkSeed) z.1.1 z.1.2)).getD (0, [])) := by
  rw [qmImpl_bridge]
  have hmsg : ∀ (R : prims.Y) (root : prims.Y) (m : List Byte),
      simulateQ (Lazy.tblImpl (gspec := []ₒ) (PublicHash.impl prims) tbl)
        (PublicHash.hmsg prims.core R pkSeed root m :
          OracleComp (Lazy.OSpec prims []ₒ) (Bytes vp.params.m)) =
      pure (prims.Hmsg R pkSeed root m) := by
    intro R root m
    simp [PublicHash.hmsg, Lazy.tblImpl, PublicHash.impl]
  unfold qmTail
  simp only [simulateQ_bind, simulateQ_pure]
  rw [hmsg, simulateQ_qmToProb_pure, pure_bind]
  have hc := Resources2.collO_tbl (gspec := []ₒ) tbl pkSeed L
    (Resources2.verifyFree pkSeed (splitDigest vp.params
      (prims.Hmsg z.1.2.randomness pkSeed (idealRoot vp prims tbl pkSeed) z.1.1)) z.1.2) []
  have hnil : findCollisionM pkSeed L [] = none := rfl
  rw [hnil] at hc
  rw [hc, simulateQ_qmToProb_pure, pure_bind, Resources2.verifyCalls_eq_free]
  rfl

theorem qmSignO_ideal (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    qmSignO optRand (PublicHash.impl prims) tbl pkSeed (idealRoot vp prims tbl pkSeed) =
      g2SignOracle optRand (idealPk vp prims tbl pkSeed)
        (fun m R => idealSign vp prims tbl m (idealPk vp prims tbl pkSeed) R) := by
  funext msg
  refine StateT.ext fun log => ?_
  have h := fun R ↦ qmImpl_openSign tbl msg (idealPk vp prims tbl pkSeed) R
  simp only [qmSignO, StateT.run_mk]
  simp only [idealPk] at h ⊢
  simp [g2SignOracle, h]

/-- **Part A.** The second phase of `qbTcrArM n Q` is the open-form machine at the true hash
answers. -/
theorem qMemoForge_eq_qmMach (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    {pkSeedDist : ProbComp prims.PkSeed} (n : ℕ)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    qMemoForge n Q s pkSeed = qmMach optRand (PublicHash.impl prims) n Q.main s pkSeed := by
  unfold qmMach qMemoForge
  rw [qmImpl_openKeygen, liftU_pure, pure_bind]
  unfold qmImplS
  rw [qmSignO_ideal]
  refine bind_congr fun z ↦ ?_
  rw [qmImpl_tail, map_pure]

end generic

/-! ## Part B: the hash answers as port evaluations, and the machine family

For a fixed world `ω₀` the class-TCR second phase in world `{ω₀ with thash := T}` is one fixed
family `tcrMach … ω₀ n st pk H` evaluated at the port function `H = encΩ {ω₀ with thash := T}`. -/

/-- Close a goal `a = b` by `Eq.refl a`, the definitional check left to the kernel (as
`Reduction.Open.tcr_kernel_rfl`; no axiom). -/
elab "qm_kernel_rfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← Lean.instantiateMVars (← g.getType)
  let some (_, a, _) := t.consumeMData.eq? | throwError "qm_kernel_rfl: not an equality"
  let pf ← Lean.Meta.mkEqRefl a
  g.assign pf
  Lean.Elab.Tactic.replaceMainGoal []

/-- `Coded.signingImpl` without the (unused) scheme arguments. -/
def qmCSign {M S Sb : Type} (encS : S → Sb) :
    QueryImpl (unifSpec + (M →ₒ Sb)) (OracleComp (unifSpec + (M →ₒ S)))
  | .inl t => (query (spec := unifSpec + (M →ₒ S)) (.inl t) : OracleComp _ (unifSpec.Range t))
  | .inr m => encS <$> (query (spec := unifSpec + (M →ₒ S)) (.inr m) : OracleComp _ S)

/-- `Coded.readForgery` without the (unused) scheme arguments. -/
def qmCRead {M S Sb : Type} (decS : Sb → Option S) (fallback : S) (out : M × Sb) : M × S :=
  (out.1, (decS out.2).getD fallback)

theorem qmCSign_eq {M PK SK S PKb SKb Sb : Type} {alg : SignatureAlg ProbComp M PK SK S}
    {balg : SignatureAlg ProbComp M PKb SKb Sb} (v : Coded.View alg balg) :
    Coded.signingImpl v = qmCSign v.encS := by
  funext t
  rcases t with t | t <;> rfl

theorem qmCRead_eq {M PK SK S PKb SKb Sb : Type} {alg : SignatureAlg ProbComp M PK SK S}
    {balg : SignatureAlg ProbComp M PKb SKb Sb} (v : Coded.View alg balg) :
    Coded.readForgery v = qmCRead v.decS := rfl

section mach

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- **Each public-hash query as ONE evaluation of the port function** (`Thash` in the first
coordinate of the `.inl` component, `H_msg` in the second coordinate of the `.inr (.inl _)`
component); out-of-cap inputs get the constant `default`, as in `FinFns.toRand`. -/
def hashH (ω₀ : Ω128 c) (H : EncX c → EncY) : QueryImpl (publicHashSpec (primsΩ ω₀).core) Id
  | .thash pk a xs =>
      if h : xs.length ≤ c.tl then (H (.inl (pk, a, BList.ofList xs h))).1 else default
  | .hmsg r pk root m =>
      if h : m.length ≤ c.ml then (H (.inr (.inl (r, pk, root, BList.ofList m h)))).2 else default

/-- At the port function of world `{ω₀ with thash := T}`, `hashH` IS the hash interpretation of
that world. -/
theorem impl_primsΩ_withThash (ω₀ : Ω128 c) (T) :
    PublicHash.impl (primsΩ { ω₀ with thash := T }) = hashH c ω₀ (encΩ { ω₀ with thash := T }) := by
  funext q
  cases q <;> rfl

/-- The internal forger of the reduction (`qPureBytesToInternal` around the compiled port
program), written with the world fixed to `ω₀` except for the port function. -/
noncomputable def qmForger (ω₀ : Ω128 c) (H : EncX c → EncY)
    (pk : PublicKeyCore (primsΩ ω₀).core) :
    QOC (WS (EncX c) EncY E)
      (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core))
      (List Byte × GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core) :=
  Guarded.readForgery pureEncode ([], constSig default) <$>
    wrap0 (Guarded.signingImpl pureEncode)
      (qmCRead (decodePureSig Link.vp (primsΩ ω₀) (codecR ω₀.toRand))
          (Except.error (External.Error.contextTooLong 0)) <$>
        wrap0 (qmCSign (encodePureSig Link.vp (primsΩ ω₀) (codecR ω₀.toRand)))
          (compileQ H (F.main (encodePublicKey (codecR ω₀.toRand) pk))))

theorem internalΩ_main_withThash (ω₀ : Ω128 c) (T) :
    (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T }).main =
      fun pk ↦ qmForger c F ω₀ (encΩ { ω₀ with thash := T }) pk := by
  funext pk
  simp only [internalΩ, qPureBytesToInternal, qToInternal, qPureBytesToTyped, QForger.wrapForger,
    PortForger.at, qmCSign_eq, qmCRead_eq, pureBytesView]
  rfl

/-- **The class-TCR second-phase machine family** for the fixed world `ω₀`, arity `n`, state
`st` and seed `pk`, as a function of the port function `H`. -/
noncomputable def tcrMach (ω₀ : Ω128 c) (n : ℕ)
    (st : SecretTable Link.vp (primsΩ ω₀) ×
      List ((primsΩ ω₀).AdrsKey × List (primsΩ ω₀).Y))
    (pk : (primsΩ ω₀).PkSeed) (H : EncX c → EncY) :
    Closed (WS (EncX c) EncY E) (ℕ × {xs : List (primsΩ ω₀).Y // xs.length = n}) :=
  qmMach (optRandOf c optRand₀ ω₀) (hashH c ω₀ H) n (qmForger c F ω₀ H) st pk

/-- **Step 3, equation.**  At the port function of world `{ω₀ with thash := T}`, the family is
the second phase of the quantum class-TCR adversary of that world. -/
theorem tcrMach_encΩ (ω₀ : Ω128 c) (n : ℕ)
    (st : SecretTable Link.vp (primsΩ ω₀) ×
      List ((primsΩ ω₀).AdrsKey × List (primsΩ ω₀).Y))
    (pk : (primsΩ ω₀).PkSeed) (T) :
    tcrMach c optRand₀ F ω₀ n st pk (encΩ { ω₀ with thash := T }) =
      (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).forge st pk := by
  have h1 := qMemoForge_eq_qmMach (optRandOf c optRand₀ { ω₀ with thash := T }) n
    (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T }) st pk
  rw [internalΩ_main_withThash, impl_primsΩ_withThash] at h1
  refine Eq.trans ?_ h1.symm
  unfold tcrMach
  qm_kernel_rfl

end mach

/-! ## Part C: the machine family is `PUE` -/

/-- Weight of an interface query: `k` for a signing query, `0` for uniform bits. -/
abbrev sgnW {M S : Type} (k : ℕ) : (unifSpec + (M →ₒ S)).Domain → ℕ :=
  Sum.elim (fun _ ↦ 0) (fun _ ↦ k)

/-- Weight of an open-program query: `1` per hash query. -/
abbrev hashW {vp : ValidatedParams} (prims : Primitives vp.params) :
    (Lazy.OSpec prims []ₒ).Domain → ℕ :=
  fun t ↦ if Lazy.kind t = .hash then 1 else 0

/-- Own hash evaluations of the class-TCR second phase (key generation, `qs` signatures,
`H_msg` and verification with collision search): `tcrM_phase2_open_hashes`'s count. -/
def tcrMHashes (vp : ValidatedParams) (qs : ℕ) : ℕ :=
  Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp * 2)

section pue

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

attribute [local instance] Lazy.openQ

/-- One hash answer is at most one evaluation of the port function. -/
theorem evalCost_hashH (ω₀ : Ω128 c) (q : PublicHashQuery (primsΩ ω₀).core.PkSeed
    (primsΩ ω₀).core.AdrsKey (primsΩ ω₀).core.Y) :
    EvalCost (fun H ↦ (pure (hashH c ω₀ H q) : ProbComp ((publicHashSpec (primsΩ ω₀).core).Range q)))
      1 := by
  cases q with
  | thash pk a xs =>
    by_cases h : xs.length ≤ c.tl
    · have e : (fun H : EncX c → EncY ↦ (pure (hashH c ω₀ H (.thash pk a xs)) :
          ProbComp (Bytes Link.vp.params.n))) =
          fun H ↦ pure ((fun y : EncY ↦ y.1) (H (.inl (pk, a, BList.ofList xs h)))) := by
        funext H
        simp [hashH, h]
      exact e ▸ EvalCost.eval _ _
    · have e : (fun H : EncX c → EncY ↦ (pure (hashH c ω₀ H (.thash pk a xs)) :
          ProbComp (Bytes Link.vp.params.n))) = fun _ ↦ pure default := by
        funext H
        simp [hashH, h]
      exact e ▸ (EvalCost.const _).mono (Nat.zero_le _)
  | hmsg r pk root m =>
    by_cases h : m.length ≤ c.ml
    · have e : (fun H : EncX c → EncY ↦ (pure (hashH c ω₀ H (.hmsg r pk root m)) :
          ProbComp (Bytes Link.vp.params.m))) =
          fun H ↦ pure ((fun y : EncY ↦ y.2) (H (.inr (.inl (r, pk, root, BList.ofList m h))))) := by
        funext H
        simp [hashH, h]
      exact e ▸ EvalCost.eval _ _
    · have e : (fun H : EncX c → EncY ↦ (pure (hashH c ω₀ H (.hmsg r pk root m)) :
          ProbComp (Bytes Link.vp.params.m))) = fun _ ↦ pure default := by
        funext H
        simp [hashH, h]
      exact e ▸ (EvalCost.const _).mono (Nat.zero_le _)

/-- Each query of an open program costs its hash weight. -/
theorem evalCost_qmImpl (ω₀ : Ω128 c) (tbl : SecretTable Link.vp (primsΩ ω₀))
    (t : (Lazy.OSpec (primsΩ ω₀) []ₒ).Domain) :
    EvalCost (fun H ↦ qmImpl (hashH c ω₀ H) tbl t) (hashW (primsΩ ω₀) t) := by
  rcases t with n | t | d | q
  · exact EvalCost.const _
  · exact PEmpty.elim t
  · exact EvalCost.const _
  · exact evalCost_hashH c ω₀ q

/-- An open program with at most `k` hash queries costs `k` evaluations. -/
theorem evalCost_open (ω₀ : Ω128 c) (tbl : SecretTable Link.vp (primsΩ ω₀)) {α : Type}
    (P : OracleComp (Lazy.OSpec (primsΩ ω₀) []ₒ) α) (k : ℕ)
    (hP : IsQueryBoundP P (fun t ↦ Lazy.kind t = .hash) k) :
    EvalCost (fun H ↦ simulateQ (qmImpl (hashH c ω₀ H) tbl) P) k :=
  EvalCost.simulateQ (fun H ↦ qmImpl (hashH c ω₀ H) tbl) (hashW (primsΩ ω₀))
    (evalCost_qmImpl c ω₀ tbl) P k (wCount_of_isQueryBoundP _ P k hP)

theorem keygen_hashes (ω₀ : Ω128 c) (pkSeed : (primsΩ ω₀).PkSeed) :
    IsQueryBoundP (Lazy.openKeygen (primsΩ ω₀) []ₒ pkSeed) (fun t ↦ Lazy.kind t = .hash)
      (Lazy.keygenHashes Link.vp) :=
  (Lazy.openKeygen_kindBound .hash pkSeed).mono (by simpa [Lazy.ind] using Lazy.keygenB_hash)

theorem sign_hashes (ω₀ : Ω128 c) (msg : List Byte) (pkSeed : (primsΩ ω₀).PkSeed)
    (root R : (primsΩ ω₀).Y) :
    IsQueryBoundP (Lazy.openSign (primsΩ ω₀) []ₒ msg pkSeed root R)
      (fun t ↦ Lazy.kind t = .hash) (Lazy.signHashes Link.vp) :=
  (Lazy.openSign_kindBound .hash msg pkSeed root R).mono
    (by simpa [Lazy.ind] using Lazy.signB_hash)

theorem tail_hashes (ω₀ : Ω128 c) (pkSeed : (primsΩ ω₀).PkSeed)
    (L : List ((primsΩ ω₀).AdrsKey × List (primsΩ ω₀).Y)) (root : (primsΩ ω₀).Y)
    (z : (List Byte × GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core) ×
      G2Log (primsΩ ω₀)) :
    IsQueryBoundP (qmTail pkSeed L root z) (fun t ↦ Lazy.kind t = .hash)
      (1 + Resources2.verifyHashes Link.vp * 2) := by
  have hver : ∀ (parts : DigestParts Link.vp.params)
      (sig : GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core),
      IsQueryBoundP ((simulateQ (Resources2.collO (gspec := []ₒ) pkSeed L)
        (Resources2.verifyFree pkSeed parts sig)).run none) (fun t ↦ Lazy.kind t = .hash)
        (Resources2.verifyHashes Link.vp * 2) := fun parts sig ↦
    IsQueryBoundP.simulateQ_run_of_step_le (cost := 2) (q := fun t ↦ Lazy.kind t = .hash)
      (Resources2.verifyFree_bound pkSeed parts sig)
      (fun t _ s ↦ Resources2.collO_step_bound pkSeed L .hash t s)
      (fun t ht s ↦ absurd trivial ht) none
  have hmsg : ∀ (R root : (primsΩ ω₀).Y) (m : List Byte),
      IsQueryBoundP (PublicHash.hmsg (primsΩ ω₀).core R pkSeed root m :
        OracleComp (Lazy.OSpec (primsΩ ω₀) []ₒ) (Bytes Link.vp.params.m))
        (fun t ↦ Lazy.kind t = .hash) 1 :=
    fun R root m ↦ (isQueryBoundP_query_iff _ _ _).2 fun _ ↦ Nat.one_pos
  unfold qmTail
  exact Lazy.qb_bind _ (hmsg _ _ _) fun dg ↦
    Lazy.qb_bind _ (m := 0) (hver _ _) fun c ↦ isQueryBoundP_pure _ _ _

/-- Each answer of the forger's classical interface costs its weight. -/
theorem evalCost_qmImplS (ω₀ : Ω128 c) (tbl : SecretTable Link.vp (primsΩ ω₀))
    (pkSeed : (primsΩ ω₀).PkSeed) (root : (primsΩ ω₀).Y)
    (t : (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore Link.vp (primsΩ ω₀).core)).Domain)
    (s : G2Log (primsΩ ω₀)) :
    EvalCost (fun H ↦ (qmImplS (optRandOf c optRand₀ ω₀) (hashH c ω₀ H) tbl pkSeed root t).run s)
      (sgnW (Lazy.signHashes Link.vp) t) := by
  rcases t with n | msg
  · exact EvalCost.const _
  · change EvalCost (fun H ↦ optRandOf c optRand₀ ω₀ ⟨pkSeed, root⟩ >>= fun addrnd ↦
      lazyRandomizer s msg addrnd >>= fun R ↦
        simulateQ (qmImpl (hashH c ω₀ H) tbl)
          (Lazy.openSign (primsΩ ω₀) []ₒ msg pkSeed root R) >>= fun sig ↦
          (pure (sig, s ++ [(msg, addrnd, R)]) : ProbComp _)) _
    have h := EvalCost.bind (EvalCost.const (X := EncX c) (Y := EncY)
        (optRandOf c optRand₀ ω₀ ⟨pkSeed, root⟩)) fun addrnd ↦
      EvalCost.bind (EvalCost.const (X := EncX c) (Y := EncY) (lazyRandomizer s msg addrnd))
        fun R ↦ EvalCost.bind (evalCost_open c ω₀ tbl _ _ (sign_hashes c ω₀ msg pkSeed root R))
          fun sig ↦ EvalCost.const (X := EncX c) (Y := EncY)
            (pure (sig, s ++ [(msg, addrnd, R)]) : ProbComp _)
    exact h.mono (by simp)

/-- The forger family is `PUE`, every signing query weighing `k`. -/
theorem pue_qmForger (ω₀ : Ω128 c) (q qs k : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (pk : PublicKeyCore (primsΩ ω₀).core) :
    PUE (sgnW k) (fun H ↦ qmForger c F ω₀ H pk) (q + qs * k) := by
  unfold qmForger
  refine PUE.map _ (PUE.wrap0 (cnt := sgnW k) _ ?_ (PUE.map _ (PUE.wrap0 (cnt := sgnW k)
    (cnt' := sgnW k) _ ?_ (PUE.compileQ (sgnW k) _ _
    (wCount_of_countBound isPort isSign _ k ?_ _ q qs (hq _) (hqs _))))))
  · intro t
    rcases t with n | e
    · exact wCount_liftM_query _ _ le_rfl
    · simp only [Guarded.signingImpl]
      split
      · exact trivial
      · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · intro t
    rcases t with n | m
    · exact wCount_liftM_query _ _ le_rfl
    · exact WCount.map (wCount_liftM_query _ _ le_rfl) _
  · intro t
    rcases t with j | u | n | m <;> simp [compileW, isPort, isSign]

/-- **Step 3, `PUE`.**  The class-TCR machine family makes at most `q + tcrMHashes qs` port
calls plus evaluations on every path. -/
theorem pue_tcrMach (ω₀ : Ω128 c) (n : ℕ)
    (st : SecretTable Link.vp (primsΩ ω₀) ×
      List ((primsΩ ω₀).AdrsKey × List (primsΩ ω₀).Y))
    (pk : (primsΩ ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    PUE (spec := unifSpec) cnt0 (tcrMach c optRand₀ F ω₀ n st pk) (q + tcrMHashes Link.vp qs) := by
  unfold tcrMach qmMach
  have hB : ∀ root : (primsΩ ω₀).Y, PUE (spec := unifSpec) cnt0 (fun H ↦
      close (qmImplS (optRandOf c optRand₀ ω₀) (hashH c ω₀ H) st.1 pk root)
          (qmForger c F ω₀ H ⟨pk, root⟩) [] >>= fun z ↦
        liftU (classOut (primsΩ ω₀) n st.2 <$>
          simulateQ (qmImpl (hashH c ω₀ H) st.1) (qmTail pk st.2 root z)))
      (q + qs * Lazy.signHashes Link.vp + (1 + Resources2.verifyHashes Link.vp * 2)) := by
    intro root
    refine PUE.bind (PUE.close _ (evalCost_qmImplS c optRand₀ ω₀ st.1 pk root)
      (pue_qmForger c F ω₀ q qs _ hq hqs ⟨pk, root⟩) []) fun z ↦ ?_
    have h := PUE.liftU_bind (E := E) (B := fun o _ ↦ (pure o : Closed (WS (EncX c) EncY E) _))
      (q := 0)
      ((evalCost_open c ω₀ st.1 _ _ (tail_hashes c ω₀ pk st.2 root z)).map
        (classOut (primsΩ ω₀) n st.2)) fun o ↦ PUE.pure o 0
    simpa using h
  have h := PUE.liftU_bind (evalCost_open c ω₀ st.1 _ _ (keygen_hashes c ω₀ pk)) hB
  refine h.mono ?_
  unfold tcrMHashes
  omega

end pue

/-! ## Steps 3 and 5: the delivered statements -/

section deliver

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- **Step 3 (class TCR, every arity `n`).**  For a fixed world `ω₀`, state `st` and seed `pk`
there is ONE machine family in the port function, `PUE` with budget `q + tcrMHashes qs`, equal at
the port function of `{ω₀ with thash := T}` to the second phase of the quantum class-TCR
adversary of that world, for every `Thash` table `T`. -/
theorem tcr_mach_exists (ω₀ : Ω128 c) (n : ℕ)
    (st : SecretTable Link.vp (primsΩ ω₀) ×
      List ((primsΩ ω₀).AdrsKey × List (primsΩ ω₀).Y))
    (pk : (primsΩ ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mach : (EncX c → EncY) →
        Closed (WS (EncX c) EncY E) (ℕ × {xs : List (primsΩ ω₀).Y // xs.length = n}),
      PUE (spec := unifSpec) cnt0 Mach (q + tcrMHashes Link.vp qs) ∧
      ∀ T, Mach (encΩ { ω₀ with thash := T }) =
        (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).forge st pk :=
  ⟨tcrMach c optRand₀ F ω₀ n st pk, pue_tcrMach c optRand₀ F ω₀ n st pk q qs hq hqs,
    fun T ↦ tcrMach_encΩ c optRand₀ pkSeedDist₀ F ω₀ n st pk T⟩

/-- **Step 5 (class TCR, every arity `n`): the hybrid model of the forge machine**, for an
initial state `ρ ⊗ |()⟩⟨()|`. -/
theorem tcr_forge_model (ω₀ : Ω128 c) (n : ℕ)
    (st : SecretTable Link.vp (primsΩ ω₀) ×
      List ((primsΩ ω₀).AdrsKey × List (primsΩ ω₀).Y))
    (pk : (primsΩ ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (ρ : SubState ((EncX c × EncY) × E)) :
    ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × {xs : List (primsΩ ω₀).Y // xs.length = n})
        (q + tcrMHashes Link.vp qs),
      ∀ T (Ev : ℕ × {xs : List (primsΩ ω₀).Y // xs.length = n} → Prop) [DecidablePred Ev],
        Mo.prob (encΩ { ω₀ with thash := T }) Ev =
          qWeight Ev ((qbTcrArM n
            (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).forge st pk)
            (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  obtain ⟨Mo, hMo⟩ := (pue_tcrMach c optRand₀ F ω₀ n st pk q qs hq hqs).exists_model ρ
  refine ⟨Mo, fun T Ev _ ↦ ?_⟩
  rw [hMo, tcrMach_encΩ c optRand₀ pkSeedDist₀ F ω₀ n st pk T]

/-- **Step 5, at the forger's initial state**: the initial state of the class-TCR adversary is
the port forger's `F.ρ₀` (for every world), and the model computes the Born weights of the
forge machine from it. -/
theorem tcr_forge_model_ρ₀ (ω₀ : Ω128 c) (n : ℕ)
    (st : SecretTable Link.vp (primsΩ ω₀) ×
      List ((primsΩ ω₀).AdrsKey × List (primsΩ ω₀).Y))
    (pk : (primsΩ ω₀).PkSeed) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × {xs : List (primsΩ ω₀).Y // xs.length = n})
        (q + tcrMHashes Link.vp qs),
      ∀ T (Ev : ℕ × {xs : List (primsΩ ω₀).Y // xs.length = n} → Prop) [DecidablePred Ev],
        Mo.prob (encΩ { ω₀ with thash := T }) Ev =
          qWeight Ev ((qbTcrArM n
            (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).forge st pk)
            (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F { ω₀ with thash := T })).ρ₀ := by
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mo, hMo⟩ := tcr_forge_model c optRand₀ pkSeedDist₀ F ω₀ n st pk q qs hq hqs ρ
  refine ⟨Mo, fun T Ev _ ↦ ?_⟩
  rw [hMo T Ev]
  change _ = qWeight Ev _ F.ρ₀
  rw [hρ]

/-- **The hypothesis `hModel` of agent `qtcr` (`quantum/HANDOFF-qtcr.md`), discharged**, with
`q' = q + tcrMHashes Link.vp qs`, for every forger with at most `q` port calls and `qs` signing
queries on every path. -/
theorem tcr_hModel (n q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : Ω128 c) (st : Open.TcrP1State Link.vp (primsΩ ω₀))
      (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY
          (ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = n}) (q + tcrMHashes Link.vp qs),
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = n} → Prop)
          [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀ :=
  fun ω₀ st pk ↦ tcr_forge_model_ρ₀ c optRand₀ pkSeedDist₀ F ω₀ n st pk q qs hq hqs

/-- The count at SLH-DSA-SHA2-128s is the `tcr1/tcr2/tcrLen/tcrK` field of `openCounts128s`. -/
theorem tcrMHashes_128s (qs : ℕ) : tcrMHashes Link.vp qs = 269824 + qs * 2007385 + 7857 := by
  unfold tcrMHashes
  rw [keygenHashes_128s, signHashes_128s, Resources2.verifyHashes_128s]

theorem tcrMHashes_openCounts128s (qs : ℕ) :
    tcrMHashes Link.vp qs = (openCounts128s qs).tcr1 ∧
    tcrMHashes Link.vp qs = (openCounts128s qs).tcr2 ∧
    tcrMHashes Link.vp qs = (openCounts128s qs).tcrLen ∧
    tcrMHashes Link.vp qs = (openCounts128s qs).tcrK := by
  simp only [tcrMHashes_128s, openCounts128s, and_self]

end deliver

end Reduction

#print axioms Reduction.qmImpl_bridge
#print axioms Reduction.qMemoForge_eq_qmMach
#print axioms Reduction.tcrMach_encΩ
#print axioms Reduction.pue_tcrMach
#print axioms Reduction.tcr_mach_exists
#print axioms Reduction.tcr_forge_model
#print axioms Reduction.tcr_forge_model_ρ₀
#print axioms Reduction.tcr_hModel
#print axioms Reduction.tcrMHashes_openCounts128s
