import Ideal.Realize.Walk
import Reduction.Open.Tcr
import Reduction.LinearBytes

/-!
# Open programs with a compression port (generic part of the realisers)

An ideal-model forger makes compression queries of its own.  In the open programs of
`Reduction/Open` the forger enters as a program without such queries; here the forger's
compression queries are threaded through the game slot of `Lazy.OSpec prims (hS St Blk)` (which
`Lazy.tblImpl` forwards).

* `FSpecP S` — interface of a forger with a compression port and signatures of type `S`;
  `typedP codec mb` — the typed port forger built from a byte-level port forger `mb` (the port
  variant of `Reduction.bytesToTypedS`); `typedP_inst`: answering its port by `g` gives
  `bytesToTypedS` of the byte forger with its port answered by `g`.
* `tcrMOpenR gspec run L pk` — `Reduction.Open.tcrMOpen` with the forger's run abstracted to an
  arbitrary open program `run root` (`tcrMOpen_eq_R`); `tcrMOpenR_bound`: its queries.
* `portImpl`, `portRun`, `tcrMOpenP optRand mainP L pk` — the open second-phase program of
  `bTcrArM n` for a forger with port.  **Fusion** (`tcrMOpenP_fusion`): under any interpretation
  that answers port queries by `g`, it is `tcrMOpen` at the forger with its port answered by `g`.
* counts of `tcrMOpenP` (`tcrMOpenP_port`, `tcrMOpenP_hashes`, `tcrMOpenP_hmsg`, `tcrMOpenP_bad`):
  port queries `≤ qf`; hash queries `≤ keygenHashes + qs·signHashes + (1 + 2·verifyHashes)`;
  `H_msg` queries `≤ qs + 1`; no `Thash` query on more than `B` values and no `H_msg` query on
  more than `ℓ` bytes.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize

open Reduction Reduction.Open Reduction.Lazy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## General fusion lemmas -/

section Fusion

variable {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {σ α : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Two stateful runs of a program — through `hP` directly, or through `h` after rewriting each
query by `inst` — agree under the outer interpretation `φ`, if they agree at every query. -/
theorem port_fusion (φ : QueryImpl spec₂ m) (inst : QueryImpl spec (OracleComp spec₁))
    (h : QueryImpl spec₁ (StateT σ (OracleComp spec₂)))
    (hP : QueryImpl spec (StateT σ (OracleComp spec₂)))
    (hstep : ∀ t s, simulateQ φ ((hP t).run s) = simulateQ φ ((simulateQ h (inst t)).run s))
    (oa : OracleComp spec α) (s : σ) :
    simulateQ φ ((simulateQ hP oa).run s) =
      simulateQ φ ((simulateQ h (simulateQ inst oa)).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep, ih]

/-- Two stateless rewritings commute, if they commute at every query. -/
theorem simulateQ_comm_of_step {ι₃ : Type} {spec₃ : OracleSpec ι₃}
    (a : QueryImpl spec₁ (OracleComp spec₃)) (b : QueryImpl spec (OracleComp spec₁))
    (c : QueryImpl spec₂ (OracleComp spec₃)) (d : QueryImpl spec (OracleComp spec₂))
    (hstep : ∀ t, simulateQ a (b t) = simulateQ c (d t)) (oa : OracleComp spec α) :
    simulateQ a (simulateQ b oa) = simulateQ c (simulateQ d oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, hstep, ih]

/-- `instImpl₀ g` is the identity on lifted probabilistic computations. -/
theorem instImpl₀_liftM (g : CF St Blk) (ob : ProbComp α) :
    simulateQ (instImpl₀ g) (liftM ob : OracleComp (unifSpec + hS St Blk) α) = ob := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftM_bind, simulateQ_bind]
    simp only [ih]
    have : simulateQ (instImpl₀ g)
        (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp (unifSpec + hS St Blk) _) =
        (liftM (unifSpec.query n) : ProbComp _) := by
      show simulateQ (instImpl₀ g) (liftM ((unifSpec + hS St Blk).query (.inl n))) = _
      rw [simulateQ_spec_query]
      rfl
    rw [this]

end Fusion

/-! ## Forgers with a compression port -/

/-- Interface of a forger with a compression port: uniform bits, compression queries, signing
queries answered in `S`. -/
abbrev FSpecP (S : Type) := unifSpec + (hS St Blk + (List Byte →ₒ S))

/-- A compression query of a port forger. -/
def isPortQ {S : Type} : (FSpecP S).Domain → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A signing query of a port forger. -/
def isSignQ {S : Type} : (FSpecP S).Domain → Bool
  | .inr (.inr _) => true
  | _ => false

/-- A signing query of a port forger on a message of more than `ℓ` bytes. -/
def isLongQ {S : Type} (ℓ : ℕ) : (FSpecP S).Domain → Bool
  | .inr (.inr m) => decide (ℓ < m.length)
  | _ => false

section Typed

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [Inhabited prims.Y]

/-- A typed forger program with compression port. -/
abbrev PortForgerProg (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  PublicKeyCore prims.core →
    OracleComp (FSpecP (GeneralScheme.SignatureCore vp prims.core))
      (List Byte × GeneralScheme.SignatureCore vp prims.core)

variable (codec : CoreWireCodec vp.params prims.core)

/-- Port variant of `Coded.signingImpl`: sampling and compression queries forwarded, a signing
query answered by one typed signing query whose answer is encoded. -/
def signP : QueryImpl (FSpecP (List Byte))
    (OracleComp (FSpecP (GeneralScheme.SignatureCore vp prims.core)))
  | .inl n => (liftM ((FSpecP (GeneralScheme.SignatureCore vp prims.core)).query (.inl n)) :
      OracleComp (FSpecP (GeneralScheme.SignatureCore vp prims.core)) _)
  | .inr (.inl q) =>
      (liftM ((FSpecP (GeneralScheme.SignatureCore vp prims.core)).query (.inr (.inl q))) :
        OracleComp (FSpecP (GeneralScheme.SignatureCore vp prims.core)) _)
  | .inr (.inr m) => encodeSignature vp codec <$>
      (liftM ((FSpecP (GeneralScheme.SignatureCore vp prims.core)).query (.inr (.inr m))) :
        OracleComp (FSpecP (GeneralScheme.SignatureCore vp prims.core))
          (GeneralScheme.SignatureCore vp prims.core))

/-- Port variant of `Coded.readForgery`. -/
def readP (out : List Byte × List Byte) : List Byte × GeneralScheme.SignatureCore vp prims.core :=
  (out.1, ((decodeSignature vp codec out.2).toOption).getD (constSig default))

/-- **The typed port forger built from a byte-level port forger** (port variant of
`Reduction.bytesToTypedS`). -/
def typedP (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte)) :
    PortForgerProg vp prims :=
  fun pk => readP codec <$> simulateQ (signP codec) (mb (encodePublicKey codec pk))

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- **Answering the port of `typedP codec mb` by `g`** gives the Reduction's typed forger built
from the byte forger with its port answered by `g`. -/
theorem typedP_inst (g : CF St Blk)
    (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte))
    (pk : PublicKeyCore prims.core) :
    simulateQ (instImpl g) (typedP codec mb pk) =
      (bytesToTypedS (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist)
        ⟨fun pkb => simulateQ (instImpl g) (mb pkb)⟩).toUnforgeableAdversary.main pk := by
  have hc : ∀ {α : Type} (X : OracleComp (FSpecP (List Byte)) α),
      simulateQ (instImpl g) (simulateQ (signP codec) X) =
        simulateQ (Coded.signingImpl (bytesView vp prims codec optRand pkSeedDist))
          (simulateQ (instImpl g) X) := by
    intro α X
    refine simulateQ_comm_of_step _ _ _ _ (fun t => ?_) X
    rcases t with n | q | m
    · simp [signP, instImpl, Coded.signingImpl]
    · simp [signP, instImpl]
    · simp [signP, instImpl, Coded.signingImpl, bytesView]
  show simulateQ (instImpl g) (readP codec <$> simulateQ (signP codec)
      (mb (encodePublicKey codec pk))) =
    Coded.readForgery (bytesView vp prims codec optRand pkSeedDist) (constSig default) <$>
      simulateQ (Coded.signingImpl (bytesView vp prims codec optRand pkSeedDist))
        (simulateQ (instImpl g) (mb (encodePublicKey codec pk)))
  rw [simulateQ_map, hc]
  rfl

/-- Each step of `signP` issues exactly the query it translates: the count of any class of typed
queries that corresponds (`hpq`) to a class of byte-level queries is preserved. -/
theorem typedP_bound (pb : (FSpecP (List Byte)).Domain → Bool)
    (pt : (FSpecP (GeneralScheme.SignatureCore vp prims.core)).Domain → Bool)
    (hpq : ∀ (n : ℕ) (q : St × Blk) (m : List Byte),
      pt (.inl n) = pb (.inl n) ∧ pt (.inr (.inl q)) = pb (.inr (.inl q)) ∧
        pt (.inr (.inr m)) = pb (.inr (.inr m)))
    (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte))
    (pk : PublicKeyCore prims.core) (n : ℕ)
    (h : IsQueryBoundP (mb (encodePublicKey codec pk)) (fun i => pb i = true) n) :
    IsQueryBoundP (typedP codec mb pk) (fun i => pt i = true) n := by
  unfold typedP
  rw [isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_of_step h (fun t ht => ?_) (fun t ht => ?_)
  · rcases t with n | q | m
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
    · show IsQueryBoundP (_ <$> _) _ _
      rw [isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rcases t with n | q | m
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' =>
        absurd (((hpq n default []).1).symm.trans h') ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h' =>
        absurd (((hpq 0 q []).2.1).symm.trans h') ht
    · show IsQueryBoundP (_ <$> _) _ _
      rw [isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff _ _ _).2 fun h' =>
        absurd (((hpq 0 default m).2.2).symm.trans h') ht

/-- The forged message of `typedP codec mb` is a forged message of `mb`. -/
theorem typedP_out (mb : List Byte → OracleComp (FSpecP (List Byte)) (List Byte × List Byte))
    (pk : PublicKeyCore prims.core)
    (z : List Byte × GeneralScheme.SignatureCore vp prims.core)
    (hz : z ∈ support (typedP codec mb pk)) :
    ∃ out ∈ support (mb (encodePublicKey codec pk)), z.1 = out.1 := by
  unfold typedP at hz
  rw [support_map] at hz
  obtain ⟨out, hout, rfl⟩ := hz
  exact ⟨out, support_simulateQ_subset _ _ hout, rfl⟩

end Typed

/-! ## The open second-phase program with the forger's run abstracted -/

section Open

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {ι : Type}

attribute [local instance] Lazy.openQ

/-- `Reduction.Open.tcrMOpen` with the forger's run abstracted: key generation, the run
`run root` (returning forgery and transcript), one `H_msg` query for the forgery, verification
of the forgery with the collision search against `L`. -/
noncomputable def tcrMOpenR (gspec : OracleSpec ι)
    (run : prims.Y → OracleComp (Lazy.OSpec prims gspec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims))
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × List prims.Y) := do
  let root ← Lazy.openKeygen prims gspec pkSeed
  let z ← run root
  let dg ← (PublicHash.hmsg prims.core z.1.2.randomness pkSeed root z.1.1 :
    OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m))
  let c ← (simulateQ (Resources2.collO (gspec := gspec) pkSeed L)
    (Resources2.verifyFree pkSeed (splitDigest vp.params dg) z.1.2)).run none
  return c.2.getD (0, [])

/-- The handler by which the open programs run a forger without port. -/
noncomputable def stdImpl (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (gspec : OracleSpec ι) (pkSeed : prims.PkSeed) (root : prims.Y) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims gspec))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims gspec))).liftTarget
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims gspec))) +
    logSignOracle optRand ⟨pkSeed, root⟩ lazyRandomizerLift
      (fun m R => Lazy.openSign prims gspec m pkSeed root R)

/-- `tcrMOpen` is `tcrMOpenR` at the standard run of the forger program. -/
theorem tcrMOpen_eq_R (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (gspec : OracleSpec ι) (main : TcrForgerProg vp prims)
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    tcrMOpen optRand gspec main L pkSeed =
      tcrMOpenR gspec (fun root =>
        (simulateQ (stdImpl optRand gspec pkSeed root) (main ⟨pkSeed, root⟩)).run []) L pkSeed :=
  rfl

/-- The handler by which the open program runs a forger WITH port: sampling as before, a
compression query becomes a game query of the open program, signing as before. -/
noncomputable def portImpl (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeed : prims.PkSeed) (root : prims.Y) :
    QueryImpl (FSpecP (GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))))
  | .inl n => stdImpl optRand (hS St Blk) pkSeed root (.inl n)
  | .inr (.inl q) => (liftM (Lazy.gameQ prims (hS St Blk) q) :
      StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St)
  | .inr (.inr m) => stdImpl optRand (hS St Blk) pkSeed root (.inr m)

/-- The run of a port forger inside the open program. -/
noncomputable def portRun (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (mainP : PortForgerProg vp prims) (pkSeed : prims.PkSeed) (root : prims.Y) :
    OracleComp (Lazy.OSpec prims (hS St Blk))
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  (simulateQ (portImpl optRand pkSeed root) (mainP ⟨pkSeed, root⟩)).run []

/-- **The open second-phase program of `bTcrArM n` for a forger with compression port.** -/
noncomputable def tcrMOpenP (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (mainP : PortForgerProg vp prims) (L : List (prims.AdrsKey × List prims.Y))
    (pkSeed : prims.PkSeed) : OracleComp (Lazy.OSpec prims (hS St Blk)) (ℕ × List prims.Y) :=
  tcrMOpenR (hS St Blk) (portRun optRand mainP pkSeed) L pkSeed

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Fusion for the forger's run. -/
theorem portRun_fusion (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (φ : QueryImpl (Lazy.OSpec prims (hS St Blk)) m) (g : CF St Blk)
    (hφ : ∀ q, φ (.inr (.inl q)) = pure (g q))
    (mainP : PortForgerProg vp prims) (pkSeed : prims.PkSeed) (root : prims.Y) :
    simulateQ φ (portRun optRand mainP pkSeed root) =
      simulateQ φ ((simulateQ (stdImpl optRand (hS St Blk) pkSeed root)
        (simulateQ (instImpl g) (mainP ⟨pkSeed, root⟩))).run []) := by
  refine port_fusion φ (instImpl g) (stdImpl optRand (hS St Blk) pkSeed root)
    (portImpl optRand pkSeed root) (fun t s => ?_) _ _
  rcases t with n | q | msg
  · simp [portImpl, instImpl]
  · simp [portImpl, instImpl, Lazy.gameQ, hφ]
  · simp [portImpl, instImpl]

/-- **Fusion.**  Under any interpretation `φ` of the open program that answers port queries by
`g`, the port program is `tcrMOpen` at the forger program with its port answered by `g`. -/
theorem tcrMOpenP_fusion (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (φ : QueryImpl (Lazy.OSpec prims (hS St Blk)) m) (g : CF St Blk)
    (hφ : ∀ q, φ (.inr (.inl q)) = pure (g q))
    (mainP : PortForgerProg vp prims) (L : List (prims.AdrsKey × List prims.Y))
    (pkSeed : prims.PkSeed) :
    simulateQ φ (tcrMOpenP optRand mainP L pkSeed) =
      simulateQ φ (tcrMOpen optRand (hS St Blk) (fun pk => simulateQ (instImpl g) (mainP pk))
        L pkSeed) := by
  rw [tcrMOpen_eq_R]
  unfold tcrMOpenP tcrMOpenR
  simp only [simulateQ_bind]
  refine bind_congr fun root => ?_
  rw [portRun_fusion optRand φ g hφ]

/-! ## Queries of the open program -/

/-- An `H_msg` query of an open program. -/
def isHmsgIdx {ι P K Y : Type} : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery P K Y)) → Bool
  | .inr (.inr (.inr (.hmsg _ _ _ _))) => true
  | _ => false

/-- A hash query of an open program that is too long: `Thash` on more than `B` values or
`H_msg` on more than `ℓ` bytes. -/
def isBadIdx {ι P K Y : Type} (B ℓ : ℕ) : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery P K Y)) → Bool
  | .inr (.inr (.inr (.thash _ _ xs))) => decide (B < xs.length)
  | .inr (.inr (.inr (.hmsg _ _ _ M))) => decide (ℓ < M.length)
  | _ => false

section Counts

variable {gspec : OracleSpec ι}
variable (p : ℕ ⊕ (ι ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) → Prop)
  [DecidablePred p]

/-- Queries of `tcrMOpenR`, from those of its four parts. -/
theorem tcrMOpenR_bound
    (run : prims.Y → OracleComp (Lazy.OSpec prims gspec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims))
    (L : List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) (a b c d : ℕ)
    (hk : IsQueryBoundP (Lazy.openKeygen prims gspec pkSeed) p a)
    (hrun : ∀ root, IsQueryBoundP (run root) p b)
    (hm : ∀ root, ∀ z ∈ support (run root),
      IsQueryBoundP (PublicHash.hmsg prims.core z.1.2.randomness pkSeed root z.1.1 :
        OracleComp (Lazy.OSpec prims gspec) (Bytes vp.params.m)) p c)
    (hv : ∀ (parts : DigestParts vp.params) (sig : GeneralScheme.SignatureCore vp prims.core),
      IsQueryBoundP ((simulateQ (Resources2.collO (gspec := gspec) pkSeed L)
        (Resources2.verifyFree pkSeed parts sig)).run none) p d) :
    IsQueryBoundP (tcrMOpenR gspec run L pkSeed) p (a + b + c + d) := by
  unfold tcrMOpenR
  exact (isQueryBoundP_bind hk fun root _ =>
    isQueryBoundP_bind (hrun root) fun z hz =>
      isQueryBoundP_bind (hm root z hz) fun dg _ =>
        isQueryBoundP_bind (m := 0) (hv _ _) fun c _ => isQueryBoundP_pure _ _ _).mono (by omega)

/-- A lifted probabilistic computation makes no `p`-query, if `p` holds of no sampling query. -/
theorem liftM_np (hu : ∀ n, ¬ p (.inl n)) {β : Type} (ob : ProbComp β) :
    IsQueryBoundP (liftM ob : OracleComp (Lazy.OSpec prims gspec) β) p 0 :=
  IsQueryBoundP.of_imp (fun t ht => by
      rcases t with n | t
      · exact absurd ht (hu n)
      · rfl)
    (isQueryBoundP_liftM_isRight
      (hs := gspec + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core)) ob)

/-- Open signing makes at most one `p`-query (the `H_msg` query), if `p` holds of no secret read
and of no `Thash` query on `1`, `2`, `len` or `k` values. -/
theorem openSign_one (msg : List Byte) (pkSeed : prims.PkSeed) (pkRoot R : prims.Y)
    (hsec : ∀ d, ¬ p (.inr (.inr (.inl d))))
    (hth : ∀ key xs, OkLen vp xs → ¬ p (thIdx prims ι pkSeed key xs)) :
    IsQueryBoundP (Lazy.openSign prims gspec msg pkSeed pkRoot R) p 1 := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pkSeed a y :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
    fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hth _ _ (Or.inl rfl))
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      (ys.length = vp.params.len ∨ ys.length = vp.params.k) →
      IsQueryBoundP (PublicHash.tl prims.core pkSeed a ys :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
    fun _ ys hys => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inr hys)))
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pkSeed a l r :
      OracleComp (OSpec prims gspec) prims.Y) p 0 :=
    fun _ _ _ => (isQueryBoundP_query_iff _ _ _).2 fun h =>
      absurd h (hth _ _ (Or.inr (Or.inl rfl)))
  have hs : ∀ a : Adrs, IsQueryBoundP (secQ prims gspec a) p 0 :=
    fun _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hsec _)
  have hmq : IsQueryBoundP (PublicHash.hmsg prims.core R pkSeed pkRoot msg :
      OracleComp (OSpec prims gspec) _) p 1 :=
    (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  unfold Lazy.openSign GeneralScheme.signInternalWithSecretRandomizerM
  exact (isQueryBoundP_bind (m := 0) hmq fun digest _ =>
    isQueryBoundP_bind_zero _ _ (np_forsSign p prims.core hf hh hs _ _) fun forsSig =>
      isQueryBoundP_bind_zero _ _ (np_forsPk p prims.core hf htl hh forsSig _ _) fun forsPk =>
        isQueryBoundP_bind_zero _ _ (np_signFromPos p prims.core hf htl hh hs _ _ _ _ _)
          fun htSig => isQueryBoundP_pure _ _ _).mono (by omega)

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)

/-- A sampling step of the forger's run makes no `p`-query. -/
theorem unifStep_np (hu : ∀ n, ¬ p (.inl n)) (pkSeed : prims.PkSeed) (root : prims.Y) (n : ℕ)
    (s : G2Log prims) :
    IsQueryBoundP ((stdImpl optRand gspec pkSeed root (.inl n)).run s) p 0 := by
  unfold stdImpl
  simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
  exact isQueryBoundP_bind_zero _ _
    (liftM_np (gspec := gspec) p hu (liftM (unifSpec.query n) : ProbComp _)) fun x =>
      isQueryBoundP_pure _ (x, s) _

/-- A signing step of the forger's run makes as many `p`-queries as open signing. -/
theorem signStep_bound (hu : ∀ n, ¬ p (.inl n)) (pkSeed : prims.PkSeed) (root : prims.Y)
    (msg : List Byte) (c : ℕ)
    (hsign : ∀ R, IsQueryBoundP (Lazy.openSign prims gspec msg pkSeed root R) p c)
    (s : G2Log prims) :
    IsQueryBoundP ((stdImpl optRand gspec pkSeed root (.inr msg)).run s) p c := by
  have hstep := isQueryBoundP_bind (liftM_np (gspec := gspec) p hu (optRand ⟨pkSeed, root⟩))
    fun addrnd _ => isQueryBoundP_bind
      (liftM_np (gspec := gspec) p hu (lazyRandomizer s msg addrnd)) fun R _ =>
        isQueryBoundP_bind (m := 0) (hsign R)
          fun sig _ => isQueryBoundP_pure _ (sig, s ++ [(msg, addrnd, R)]) _
  simpa [stdImpl, logSignOracle, lazyRandomizerLift] using hstep

end Counts

section PortCounts

variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (mainP : PortForgerProg vp prims) (L : List (prims.AdrsKey × List prims.Y))
  (pkSeed : prims.PkSeed)

private theorem kind_hmIdx (R : prims.Y) (pk : prims.PkSeed) (root : prims.Y) (m : List Byte) :
    Lazy.kind (hmIdx prims (St × Blk) R pk root m) = .hash := rfl

/-- **Port queries of the open program**: at most the forger's compression queries. -/
theorem tcrMOpenP_port (qf : ℕ)
    (hqf : ∀ pk, IsQueryBoundP (mainP pk) (fun i => isPortQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qf) :
    IsQueryBoundP (tcrMOpenP optRand mainP L pkSeed) (fun t => Lazy.kind t = .game) qf := by
  have hu : ∀ n : ℕ, ¬ Lazy.kind (ι := St × Blk) (D := SecIdx)
      (κ := PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y) (.inl n) = .game := by
    intro n; simp [Lazy.kind]
  have hsec : ∀ d : SecIdx, ¬ Lazy.kind (ι := St × Blk) (D := SecIdx)
      (κ := PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y) (.inr (.inr (.inl d))) = .game := by
    intro d; simp [Lazy.kind]
  have hth : ∀ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y),
      ¬ Lazy.kind (thIdx prims (St × Blk) pk key xs) = .game := by
    intro pk key xs; simp [Lazy.kind]
  have hhm : ∀ (R : prims.Y) (pk : prims.PkSeed) (root : prims.Y) (m : List Byte),
      ¬ Lazy.kind (hmIdx prims (St × Blk) R pk root m) = .game := by
    intro R pk root m; simp [Lazy.kind]
  have h := tcrMOpenR_bound (gspec := hS St Blk) (fun t => Lazy.kind t = .game)
    (portRun optRand mainP pkSeed) L pkSeed 0 qf 0 0
    (np_openKeygen _ pkSeed hsec fun key xs _ => hth _ _ _)
    (fun root => by
      have := IsQueryBoundP.simulateQ_run_of_step (q := fun t => Lazy.kind t = .game)
        (impl := portImpl optRand pkSeed root) (hqf ⟨pkSeed, root⟩)
        (fun t ht s => by
          rcases t with n | q | msg
          · simp [isPortQ] at ht
          · show IsQueryBoundP ((liftM (Lazy.gameQ prims (hS St Blk) q) :
              StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St).run s) _ 1
            rw [StateT.run_monadLift]
            exact isQueryBoundP_bind (m := 0) ((isQueryBoundP_query_iff _ _ _).2 fun _ =>
              Nat.one_pos) fun x _ => isQueryBoundP_pure _ (x, s) _
          · simp [isPortQ] at ht)
        (fun t ht s => by
          rcases t with n | q | msg
          · exact unifStep_np _ optRand hu pkSeed root n s
          · exact absurd rfl ht
          · exact signStep_bound _ optRand hu pkSeed root msg 0
              (fun R => np_openSign _ msg pkSeed root R hsec (fun key xs _ => hth _ _ _)
                (hhm _ _ _ _)) s) []
      exact this)
    (fun root z _ => (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hhm _ _ _ _))
    (fun parts sig => np_collO_run _ pkSeed L (fun key xs _ => hth _ _ _)
      (fun q _ => hth _ _ _) parts sig none)
  exact h.mono (by omega)

/-- **Hash queries of the open program** (`Thash` and `H_msg` together):
`≤ keygenHashes + qs·signHashes + (1 + 2·verifyHashes)`, the count of
`Reduction.Open.tcrM_phase2_open_hashes`. -/
theorem tcrMOpenP_hashes (qs : ℕ)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk) (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (tcrMOpenP optRand mainP L pkSeed) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp * 2)) := by
  have hu : ∀ n : ℕ, ¬ Lazy.kind (ι := St × Blk) (D := SecIdx)
      (κ := PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y) (.inl n) = .hash := by
    intro n; simp [Lazy.kind]
  have h := tcrMOpenR_bound (gspec := hS St Blk) (fun t => Lazy.kind t = .hash)
    (portRun optRand mainP pkSeed) L pkSeed _ (qs * Lazy.signB vp 0 1) 1
      (Resources2.verifyHashes vp * 2)
    (Lazy.openKeygen_kindBound .hash pkSeed)
    (fun root => IsQueryBoundP.simulateQ_run_of_step_le (q := fun t => Lazy.kind t = .hash)
        (impl := portImpl optRand pkSeed root) (hqs ⟨pkSeed, root⟩)
        (fun t ht s => by
          rcases t with n | q | msg
          · simp [isSignQ] at ht
          · simp [isSignQ] at ht
          · exact signStep_bound _ optRand hu pkSeed root msg _
              (fun R => by
                simpa [Lazy.ind] using
                  Lazy.openSign_kindBound (gspec := hS St Blk) .hash msg pkSeed root R) s)
        (fun t ht s => by
          rcases t with n | q | msg
          · exact unifStep_np _ optRand hu pkSeed root n s
          · show IsQueryBoundP ((liftM (Lazy.gameQ prims (hS St Blk) q) :
              StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St).run s) _ 0
            rw [StateT.run_monadLift]
            exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => by
              simp [Lazy.kind] at h) fun x => isQueryBoundP_pure _ (x, s) _
          · exact absurd rfl ht) [])
    (fun root z _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun parts sig => IsQueryBoundP.simulateQ_run_of_step_le (cost := 2)
      (q := fun t => Lazy.kind t = .hash)
      (Resources2.verifyFree_bound pkSeed parts sig)
      (fun t ht s => Resources2.collO_step_bound pkSeed L .hash t s)
      (fun t ht s => absurd trivial ht) none)
  refine h.mono ?_
  have h1 : Lazy.keygenB vp (Lazy.ind .hash .sec) (Lazy.ind .hash .hash) ≤ Lazy.keygenHashes vp := by
    simpa [Lazy.ind] using Lazy.keygenB_hash (vp := vp)
  have h2 : qs * Lazy.signB vp 0 1 ≤ qs * Lazy.signHashes vp :=
    Nat.mul_le_mul_left _ Lazy.signB_hash
  omega

/-- **`H_msg` queries of the open program**: one per signing query and one for the forgery. -/
theorem tcrMOpenP_hmsg (qs : ℕ)
    (hqs : ∀ pk, IsQueryBoundP (mainP pk) (fun i => isSignQ (S := GeneralScheme.SignatureCore vp prims.core) i = true) qs) :
    IsQueryBoundP (tcrMOpenP optRand mainP L pkSeed) (fun t => isHmsgIdx t = true) (qs + 1) := by
  have hu : ∀ n : ℕ, ¬ isHmsgIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inl n) = true := by
    intro n; simp [isHmsgIdx]
  have hsec : ∀ d : SecIdx, ¬ isHmsgIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) (.inr (.inr (.inl d))) = true := by
    intro d; simp [isHmsgIdx]
  have hth : ∀ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y),
      ¬ isHmsgIdx (thIdx prims (St × Blk) pk key xs) = true := by
    intro pk key xs; simp [isHmsgIdx]
  have h := tcrMOpenR_bound (gspec := hS St Blk) (fun t => isHmsgIdx t = true)
    (portRun optRand mainP pkSeed) L pkSeed 0 (qs * 1) 1 0
    (np_openKeygen _ pkSeed hsec fun key xs _ => hth _ _ _)
    (fun root => IsQueryBoundP.simulateQ_run_of_step_le (q := fun t => isHmsgIdx t = true)
        (impl := portImpl optRand pkSeed root) (hqs ⟨pkSeed, root⟩)
        (fun t ht s => by
          rcases t with n | q | msg
          · simp [isSignQ] at ht
          · simp [isSignQ] at ht
          · exact signStep_bound _ optRand hu pkSeed root msg 1
              (fun R => openSign_one _ msg pkSeed root R hsec fun key xs _ => hth _ _ _) s)
        (fun t ht s => by
          rcases t with n | q | msg
          · exact unifStep_np _ optRand hu pkSeed root n s
          · show IsQueryBoundP ((liftM (Lazy.gameQ prims (hS St Blk) q) :
              StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St).run s) _ 0
            rw [StateT.run_monadLift]
            exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => by
              simp [isHmsgIdx] at h) fun x => isQueryBoundP_pure _ (x, s) _
          · exact absurd rfl ht) [])
    (fun root z _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun parts sig => np_collO_run _ pkSeed L (fun key xs _ => hth _ _ _)
      (fun q _ => hth _ _ _) parts sig none)
  exact h.mono (by omega)

/-- **No long hash query in the open program**: if the hash calls of the scheme are on at most
`B` values, the stored list has only entries of at most `B` values, and the forger's signing
queries and its forgery are on messages of at most `ℓ` bytes, then the open program makes no
`Thash` query on more than `B` values and no `H_msg` query on more than `ℓ` bytes. -/
theorem tcrMOpenP_bad (B ℓ : ℕ) (hB : ∀ xs : List prims.Y, OkLen vp xs → xs.length ≤ B)
    (hL : ∀ q ∈ L, q.2.length ≤ B)
    (hlong : ∀ pk, IsQueryBoundP (mainP pk) (fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (mainP pk), z.1.length ≤ ℓ) :
    IsQueryBoundP (tcrMOpenP optRand mainP L pkSeed) (fun t => isBadIdx B ℓ t = true) 0 := by
  have hu : ∀ n : ℕ, ¬ isBadIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) B ℓ (.inl n) = true := by
    intro n; simp [isBadIdx]
  have hsec : ∀ d : SecIdx, ¬ isBadIdx (ι := St × Blk) (P := prims.PkSeed) (K := prims.AdrsKey)
      (Y := prims.Y) B ℓ (.inr (.inr (.inl d))) = true := by
    intro d; simp [isBadIdx]
  have hth : ∀ (pk : prims.PkSeed) (key : prims.AdrsKey) (xs : List prims.Y), xs.length ≤ B →
      ¬ isBadIdx B ℓ (thIdx prims (St × Blk) pk key xs) = true := by
    intro pk key xs h; simp [isBadIdx]; omega
  have hhm : ∀ (R : prims.Y) (pk : prims.PkSeed) (root : prims.Y) (m : List Byte),
      m.length ≤ ℓ → ¬ isBadIdx B ℓ (hmIdx prims (St × Blk) R pk root m) = true := by
    intro R pk root m h; simp [isBadIdx]; omega
  have h := tcrMOpenR_bound (gspec := hS St Blk) (fun t => isBadIdx B ℓ t = true)
    (portRun optRand mainP pkSeed) L pkSeed 0 0 0 0
    (np_openKeygen _ pkSeed hsec fun key xs hx => hth _ _ _ (hB xs hx))
    (fun root => qb_simulateQ_run_zero (p := fun i => isLongQ (S := GeneralScheme.SignatureCore vp prims.core) ℓ i = true)
        (impl := portImpl optRand pkSeed root)
        (fun t ht s => by
          rcases t with n | q | msg
          · exact unifStep_np _ optRand hu pkSeed root n s
          · show IsQueryBoundP ((liftM (Lazy.gameQ prims (hS St Blk) q) :
              StateT (G2Log prims) (OracleComp (Lazy.OSpec prims (hS St Blk))) St).run s) _ 0
            rw [StateT.run_monadLift]
            exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => by
              simp [isBadIdx] at h) fun x => isQueryBoundP_pure _ (x, s) _
          · have hm : msg.length ≤ ℓ := by
              simp only [isLongQ, decide_eq_true_eq, not_lt] at ht
              exact ht
            exact signStep_bound _ optRand hu pkSeed root msg 0
              (fun R => np_openSign _ msg pkSeed root R hsec
                (fun key xs hx => hth _ _ _ (hB xs hx)) (hhm _ _ _ _ hm)) s)
        (hlong ⟨pkSeed, root⟩) [])
    (fun root z hz => (isQueryBoundP_query_iff _ _ _).2 fun h => by
      refine absurd h (hhm _ _ _ _ (hout ⟨pkSeed, root⟩ z.1 ?_))
      have hz' : z.1 ∈ support ((simulateQ (portImpl optRand pkSeed root)
          (mainP ⟨pkSeed, root⟩)).run' []) := by
        rw [StateT.run'_eq, support_map]
        exact ⟨z, hz, rfl⟩
      exact support_simulateQ_run'_subset _ _ _ hz')
    (fun parts sig => np_collO_run _ pkSeed L (fun key xs hx => hth _ _ _ (hB xs hx))
      (fun q hq => hth _ _ _ (hL q hq)) parts sig none)
  exact h

end PortCounts

end Open

end Ideal.Realize

#print axioms Ideal.Realize.typedP_inst
#print axioms Ideal.Realize.tcrMOpen_eq_R
#print axioms Ideal.Realize.tcrMOpenP_fusion
#print axioms Ideal.Realize.tcrMOpenP_port
#print axioms Ideal.Realize.tcrMOpenP_hashes
#print axioms Ideal.Realize.tcrMOpenP_hmsg
#print axioms Ideal.Realize.tcrMOpenP_bad
