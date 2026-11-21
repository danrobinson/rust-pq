import Reduction.Lazy.Core
import Reduction.PRFHop

/-!
# Open programs for key generation and signing over the lazy secret oracle

Shared by `Reduction.Lazy.MsgLazy` and `Reduction.Lazy.ItsrLazy`.

* `OSpec prims gspec = RSpec gspec SecIdx prims.Y (publicHashSpec prims.core)`: the interface of
  the open programs; hash evaluations are queries (`hspec := publicHashSpec prims.core`,
  `hI := PublicHash.impl prims`), secret reads are queries at `secIdx a`.
* `openKeygen`, `openSign`: VCVio's provider-parametric programs at the provider `secQ`;
  `openKeygen_tbl`, `openSign_tbl`: under `tblImpl _ g` they are `pure (idealRoot …)`,
  `pure (idealSign …)`.
* `evalDist_lazyRun_eq_table_run'`: the `run'` form of `Core.evalDist_lazyRun_eq_table`.
* Counting (`qb_*`): `IsQueryBoundP` budgets of the callback-parametric programs for an arbitrary
  predicate and per-callback budgets; `openKeygen_kindBound`, `openSign_kindBound` give, for each
  kind `K`, the budgets `keygenB`, `signB`, with closed forms `keygenB_sec`, `signB_sec`
  (`2^h'·len`, `signReads vp`), `keygenB_hash`, `signB_hash` (`keygenHashes vp`, `signHashes vp`)
  and `keygenB_game`, `signB_game` (`0`).

What the hash count does not cover: the single final `verifyInternal` inside `harnessValid`
(MsgLazy only; a fixed number of hash calls, evaluated inline as a pure function), and the
forger's own computation.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Lazy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable {ι : Type} {gspec : OracleSpec ι}

/-- Interface of the open programs of the SLH-DSA reductions: uniform bits, the game oracles
`gspec`, the secret oracle `SecIdx →ₒ prims.Y`, and the public hash functions. -/
abbrev OSpec (prims : Primitives vp.params) (gspec : OracleSpec ι) :=
  RSpec gspec SecIdx prims.Y (publicHashSpec prims.core)

/-- A hash evaluation, as an explicit query of the open program. -/
@[reducible] def openQ (prims : Primitives vp.params) (gspec : OracleSpec ι) :
    HasQuery (publicHashSpec prims.core) (OracleComp (OSpec prims gspec)) :=
  ⟨fun q => (liftM ((OSpec prims gspec).query (.inr (.inr (.inr q)))) :
    OracleComp (OSpec prims gspec) _)⟩

/-- In the closed (eager) world hashes are evaluated by `prims`. -/
@[reducible] def closedQ (prims : Primitives vp.params) (gspec : OracleSpec ι) :
    HasQuery (publicHashSpec prims.core) (OracleComp (unifSpec + gspec)) :=
  ⟨fun q => pure (PublicHash.impl prims q)⟩

attribute [local instance] openQ closedQ

/-- Read the secret value at address `a`: a query to the secret oracle at `secIdx a`. -/
def secQ (prims : Primitives vp.params) (gspec : OracleSpec ι) (a : Adrs) :
    OracleComp (OSpec prims gspec) prims.Y :=
  (liftM ((OSpec prims gspec).query (.inr (.inr (.inl (secIdx a))))) :
    OracleComp (OSpec prims gspec) _)

/-- A game query of the open program. -/
def gameQ (prims : Primitives vp.params) (gspec : OracleSpec ι) (t : ι) :
    OracleComp (OSpec prims gspec) (gspec.Range t) :=
  (liftM ((OSpec prims gspec).query (.inr (.inl t))) : OracleComp (OSpec prims gspec) _)

/-- Open key generation: the root of the top tree, reading secrets from the secret oracle. -/
def openKeygen (prims : Primitives vp.params) (gspec : OracleSpec ι) (pkSeed : prims.PkSeed) :
    OracleComp (OSpec prims gspec) prims.Y :=
  GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core (secQ prims gspec) pkSeed

/-- Open signing at a supplied randomizer. -/
def openSign (prims : Primitives vp.params) (gspec : OracleSpec ι) (msg : List Byte)
    (pkSeed : prims.PkSeed) (pkRoot R : prims.Y) :
    OracleComp (OSpec prims gspec) (GeneralScheme.SignatureCore vp prims.core) :=
  GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core (secQ prims gspec) msg
    pkSeed pkRoot R

/-! ## Interpretation by a table -/

/-- `tblImpl` as a hash-preserving monad morphism. -/
noncomputable def tblHom (g : SecretTable vp prims) :
    HasQuery.QueryHom (publicHashSpec prims.core) (OracleComp (OSpec prims gspec))
      (OracleComp (unifSpec + gspec)) :=
  { toMonadHom := simulateQ' (tblImpl (PublicHash.impl prims) g)
    map_query' := fun q => by
      simp [tblImpl] }

theorem free_apply {α : Type} (oa : OracleComp (publicHashSpec prims.core) α) :
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
      (m := OracleComp (unifSpec + gspec))).toMonadHom oa =
      pure (simulateQ (PublicHash.impl prims) oa) := by
  have hImpl : HasQuery.toQueryImpl (spec := publicHashSpec prims.core)
      (m := OracleComp (unifSpec + gspec)) =
      (PublicHash.impl prims).liftTarget (OracleComp (unifSpec + gspec)) := by
    funext q
    rfl
  rw [HasQuery.QueryHom.ofSimulateQ_apply, hImpl, simulateQ_liftTarget]
  rfl

theorem simulateQ_tblImpl_secQ (g : SecretTable vp prims) (a : Adrs) :
    simulateQ (tblImpl (gspec := gspec) (PublicHash.impl prims) g) (secQ prims gspec a) =
      pure (secretOf vp prims g a) := by
  unfold secQ
  rw [simulateQ_spec_query]
  rfl

theorem simulateQ_tblImpl_gameQ (g : SecretTable vp prims) (t : ι) :
    simulateQ (tblImpl (gspec := gspec) (PublicHash.impl prims) g) (gameQ prims gspec t) =
      (liftM ((unifSpec + gspec).query (.inr t)) : OracleComp (unifSpec + gspec) _) := by
  unfold gameQ
  rw [simulateQ_spec_query]
  rfl

theorem simulateQ_tblImpl_liftM {D V : Type} {κ : Type} {hspec : OracleSpec κ}
    (hI : QueryImpl hspec Id) (g : D → V) {β : Type} (ob : ProbComp β) :
    simulateQ (tblImpl (gspec := gspec) hI g)
      (liftM ob : OracleComp (RSpec gspec D V hspec) β) =
      (liftM ob : OracleComp (unifSpec + gspec) β) := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftM_bind, liftM_bind, simulateQ_bind]
    simp only [ih]
    congr 1

/-- Open key generation under a table is the eager root. -/
theorem openKeygen_tbl (g : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    simulateQ (tblImpl (gspec := gspec) (PublicHash.impl prims) g) (openKeygen prims gspec pkSeed) =
      pure (idealRoot vp prims g pkSeed) := by
  have h1 := GeneralScheme.keygenInternalWithSecretM_natural (vp := vp) prims.core
    (tblHom (gspec := gspec) g)
    (secQ prims gspec) (fun a => pure (secretOf vp prims g a))
    (fun a _ => simulateQ_tblImpl_secQ g a) pkSeed
  have h2 := GeneralScheme.keygenInternalWithSecretM_natural (vp := vp) prims.core
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
      (m := OracleComp (unifSpec + gspec)))
    (fun a => pure (secretOf vp prims g a)) (fun a => pure (secretOf vp prims g a))
    (fun a _ => by simp) pkSeed
  rw [free_apply] at h2
  exact h1.trans h2.symm

/-- Open signing under a table is the eager signature. -/
theorem openSign_tbl (g : SecretTable vp prims) (msg : List Byte) (pk : PublicKeyCore prims.core)
    (R : prims.Y) :
    simulateQ (tblImpl (gspec := gspec) (PublicHash.impl prims) g)
        (openSign prims gspec msg pk.pkSeed pk.pkRoot R) =
      pure (idealSign vp prims g msg pk R) := by
  have h1 := GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp) prims.core
    (tblHom (gspec := gspec) g)
    (secQ prims gspec) (fun a => pure (secretOf vp prims g a))
    (fun a _ => simulateQ_tblImpl_secQ g a) msg pk.pkSeed pk.pkRoot R
  have h2 := GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp) prims.core
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
      (m := OracleComp (unifSpec + gspec)))
    (fun a => pure (secretOf vp prims g a)) (fun a => pure (secretOf vp prims g a))
    (fun a _ => by simp) msg pk.pkSeed pk.pkRoot R
  rw [free_apply] at h2
  exact h1.trans h2.symm

/-! ## A `run'` form of lazy = eager -/

/-- `evalDist_lazyRun_eq_table` for the output only (`run'`). -/
theorem evalDist_lazyRun_eq_table_run' {κ : Type} {hspec : OracleSpec κ} {D V α σ : Type}
    [DecidableEq D] [Fintype D] [SampleableType V] [Tables.UniformSampler D V]
    [MeasurableSpace α] (hI : QueryImpl hspec Id)
    (G : QueryImpl (unifSpec + gspec) (StateT σ ProbComp))
    (hG : ∀ s, (simulateQ G (liftM ($ᵗ V : ProbComp V) : OracleComp (unifSpec + gspec) V)).run s =
      (fun v => (v, s)) <$> ($ᵗ V : ProbComp V))
    (P : OracleComp (RSpec gspec D V hspec) α) (s : σ) :
    𝒟[(simulateQ G (lazyRun hI P)).run' s] =
      𝒟[Tables.uniformTable D V >>= fun g =>
        (simulateQ G (simulateQ (tblImpl hI g) P)).run' s] := by
  let _ : MeasurableSpace (α × σ) := ⊤
  have h := evalDist_lazyRun_eq_table hI G hG P s
  have hm : Measurable (Prod.fst : α × σ → α) := measurable_from_top
  simp only [StateT.run'_eq]
  rw [evalDist_map _ hm, h, ← evalDist_map _ hm, map_bind]

/-! ## Counting queries of the callback-parametric programs

`IsQueryBoundP`-versions of the counts in `Reduction.PRFHop`, for an arbitrary query predicate
`p` and arbitrary budgets of the four callbacks: `cF` (`F`), `cT` (`T_l`), `cH` (`H`) and `cS`
(the secret provider). -/

section Count

variable {κ' : Type} {spec : OracleSpec κ'} (p : κ' → Prop) [DecidablePred p]

theorem qb_bind {α β : Type} {oa : OracleComp spec α} {ob : α → OracleComp spec β} {n m : ℕ}
    (h1 : IsQueryBoundP oa p n) (h2 : ∀ x, IsQueryBoundP (ob x) p m) :
    IsQueryBoundP (oa >>= ob) p (n + m) :=
  isQueryBoundP_bind h1 fun x _ => h2 x

theorem qb_ofFnM {α : Type} {k : ℕ} (g : Fin k → OracleComp spec α) (c : ℕ)
    (h : ∀ i, IsQueryBoundP (g i) p c) : IsQueryBoundP (Vector.ofFnM g) p (k * c) := by
  induction k with
  | zero =>
      rw [Vector.ofFnM_zero]
      exact isQueryBoundP_pure _ _ _
  | succ k ih =>
      rw [Vector.ofFnM_succ]
      refine (qb_bind p (ih (fun i => g i.castSucc) (fun i => h i.castSucc))
        fun xs => qb_bind p (m := 0) (h (Fin.last k)) fun a => isQueryBoundP_pure _ _ _).mono ?_
      rw [Nat.succ_mul]
      omega

/-- Budget of a height-`z` Merkle root: `2^z` leaves and `2^z - 1` nodes. -/
def merkleB (cl cn : ℕ) : ℕ → ℕ
  | 0 => cl
  | z + 1 => merkleB cl cn z + (merkleB cl cn z + cn)

/-- Budget of a height-`z` authentication path. -/
def authB (cl cn : ℕ) : ℕ → ℕ
  | 0 => 0
  | z + 1 => authB cl cn z + merkleB cl cn z

theorem merkleB_add (cl cn z : ℕ) : merkleB cl cn z + cn = 2 ^ z * (cl + cn) := by
  induction z with
  | zero => simp [merkleB]
  | succ z ih =>
      have h2 : 2 ^ (z + 1) * (cl + cn) = 2 ^ z * (cl + cn) + 2 ^ z * (cl + cn) := by
        rw [pow_succ]; ring
      rw [merkleB, h2, ← ih]
      omega

theorem merkleB_le (cl cn z : ℕ) : merkleB cl cn z ≤ 2 ^ z * (cl + cn) := by
  rw [← merkleB_add]; omega

theorem authB_add (cl cn z : ℕ) : authB cl cn z + (cl + cn) ≤ 2 ^ z * (cl + cn) := by
  induction z with
  | zero => simp [authB]
  | succ z ih =>
      have h := merkleB_add cl cn z
      have h2 : 2 ^ (z + 1) * (cl + cn) = 2 ^ z * (cl + cn) + 2 ^ z * (cl + cn) := by
        rw [pow_succ]; ring
      rw [authB, h2]
      omega

theorem merkleB_zero (z : ℕ) : merkleB 0 0 z = 0 := by
  induction z with
  | zero => rfl
  | succ z ih => simp [merkleB, ih]

theorem authB_zero (z : ℕ) : authB 0 0 z = 0 := by
  induction z with
  | zero => rfl
  | succ z ih => simp [authB, ih, merkleB_zero]

theorem qb_merkleRoot {Y : Type} (leaf : ℕ → OracleComp spec Y)
    (node : ℕ → ℕ → Y → Y → OracleComp spec Y) (cl cn z t : ℕ)
    (hleaf : ∀ i, IsQueryBoundP (leaf i) p cl)
    (hnode : ∀ h i l r, IsQueryBoundP (node h i l r) p cn) :
    IsQueryBoundP (PerfectMerkleTree.merkleRootM leaf node z t) p (merkleB cl cn z) := by
  induction z generalizing t with
  | zero => simpa [PerfectMerkleTree.merkleRootM, merkleB] using hleaf t
  | succ z ih =>
      simp only [PerfectMerkleTree.merkleRootM]
      exact qb_bind p (ih (2 * t)) fun l => qb_bind p (ih (2 * t + 1)) fun r => hnode _ _ l r

theorem qb_authPath {Y : Type} (leaf : ℕ → OracleComp spec Y)
    (node : ℕ → ℕ → Y → Y → OracleComp spec Y) (cl cn idx z : ℕ)
    (hleaf : ∀ i, IsQueryBoundP (leaf i) p cl)
    (hnode : ∀ h i l r, IsQueryBoundP (node h i l r) p cn) :
    IsQueryBoundP (PerfectMerkleTree.intrinsicAuthPathM leaf node idx z) p (authB cl cn z) := by
  induction z with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ z ih =>
      simp only [PerfectMerkleTree.intrinsicAuthPathM]
      refine (qb_bind p ih fun path => qb_bind p (m := 0)
        (qb_merkleRoot p leaf node cl cn z _ hleaf hnode) fun sr =>
          isQueryBoundP_pure _ _ _).mono ?_
      simp [authB]

theorem qb_climb {Y : Type} (node : ℕ → ℕ → Y → Y → OracleComp spec Y) (cn : ℕ)
    (hnode : ∀ h i l r, IsQueryBoundP (node h i l r) p cn) (idx : ℕ) (x : Y) (auth : List Y) :
    IsQueryBoundP (PerfectMerkleTree.climbM node idx x auth) p (auth.length * cn) := by
  induction auth using List.reverseRecOn with
  | nil => exact isQueryBoundP_pure _ _ _
  | append_singleton auth a ih =>
      rw [PerfectMerkleTree.climbM_concat]
      refine (qb_bind p (m := cn) ih fun child => ?_).mono ?_
      · split_ifs <;> exact hnode _ _ _ _
      · simp [Nat.succ_mul]

variable (core : CorePrimitives vp.params)
  {hash : Adrs → core.Y → OracleComp spec core.Y}
  {compress : Adrs → List core.Y → OracleComp spec core.Y}
  {nodeHash : Adrs → core.Y → core.Y → OracleComp spec core.Y}
  {secret : Adrs → OracleComp spec core.Y}
  (cF cT cH cS : ℕ)

variable (hhash : ∀ a y, IsQueryBoundP (hash a y) p cF)
  (hcompress : ∀ a ys, IsQueryBoundP (compress a ys) p cT)
  (hnode : ∀ a l r, IsQueryBoundP (nodeHash a l r) p cH)
  (hsecret : ∀ a, IsQueryBoundP (secret a) p cS)

include hhash in
theorem qb_chain (adrs : Adrs) (x : core.Y) (i s : ℕ) :
    IsQueryBoundP (chainWith hash adrs x i s) p (s * cF) := by
  induction s with
  | zero => exact isQueryBoundP_pure _ _ _
  | succ s ih =>
      rw [chainWith_succ, Nat.succ_mul]
      exact qb_bind p ih fun y => hhash _ y

/-- Budget of one WOTS+ key generation without the final compression (also bounds a WOTS+
signature). -/
def wotsB (vp : ValidatedParams) (cF cS : ℕ) : ℕ :=
  vp.params.len * (cS + (vp.params.w - 1) * cF)

/-- Budget of one XMSS signature. -/
def xmssSignB (vp : ValidatedParams) (cF cT cH cS : ℕ) : ℕ :=
  authB (wotsB vp cF cS + cT) cH vp.params.hp + wotsB vp cF cS

/-- Budget of one XMSS root recovery. -/
def xmssPkB (vp : ValidatedParams) (cF cT cH : ℕ) : ℕ :=
  vp.params.len * ((vp.params.w - 1) * cF) + cT + vp.params.hp * cH

include hhash hsecret in
theorem qb_wotsTops (adrs : Adrs) :
    IsQueryBoundP (wotsPkGenTopsWithSecret core hash secret adrs) p (wotsB vp cF cS) :=
  qb_ofFnM p (fun i : Fin vp.params.len => do
      let x ← secret (wotsSkAdrs adrs i.val)
      chainWith hash (wotsChainAdrs adrs i.val) x 0 (vp.params.w - 1)) _
    (fun i => qb_bind p (hsecret _) fun x => qb_chain p core cF hhash _ x _ _)

include hhash hsecret in
theorem qb_wotsSign (msg : core.Y) (adrs : Adrs) :
    IsQueryBoundP (wotsSignWithSecret core hash secret msg adrs) p (wotsB vp cF cS) :=
  qb_ofFnM p (fun i : Fin vp.params.len => do
      let x ← secret (wotsSkAdrs adrs i.val)
      chainWith hash (wotsChainAdrs adrs i.val) x 0 (chainStepsCore core msg i.val)) _
    (fun i => (qb_bind p (hsecret _) fun x => qb_chain p core cF hhash _ x _ _).mono
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (chainStepsCore_le core msg i.val)) _))

include hhash hcompress hsecret in
theorem qb_wotsPkGen (adrs : Adrs) :
    IsQueryBoundP (wotsPkGenWithSecret core hash compress secret adrs) p (wotsB vp cF cS + cT) :=
  qb_bind p (qb_wotsTops p core cF cS hhash hsecret adrs) fun _ => hcompress _ _

include hhash hcompress hnode hsecret in
theorem qb_xmssNode (adrs : Adrs) (z t : ℕ) :
    IsQueryBoundP (xmssNodeWithSecret core hash compress nodeHash secret adrs z t) p
      (merkleB (wotsB vp cF cS + cT) cH z) :=
  qb_merkleRoot p (xmssLeafWithSecret core hash compress secret adrs)
    (xmssNodeHashWith nodeHash adrs) _ _ z t
    (fun i => qb_wotsPkGen p core cF cT cS hhash hcompress hsecret _)
    (fun h i l r => hnode _ l r)

include hhash hcompress hnode hsecret in
theorem qb_xmssSign (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    IsQueryBoundP (xmssSignWithSecret core hash compress nodeHash secret msg adrs idx) p
      (xmssSignB vp cF cT cH cS) := by
  have h := qb_authPath p (xmssLeafWithSecret core hash compress secret adrs)
    (xmssNodeHashWith nodeHash adrs) _ _ idx vp.params.hp
    (fun i => qb_wotsPkGen p core cF cT cS hhash hcompress hsecret _)
    (fun h i l r => hnode _ l r)
  exact (qb_bind p h fun path => qb_bind p (m := 0)
    (qb_wotsSign p core cF cS hhash hsecret msg _) fun sig => isQueryBoundP_pure _ _ _).mono
      (by unfold xmssSignB; omega)

include hhash hcompress in
theorem qb_wotsPkFromSig (sig : WotsSig vp.params core) (msg : core.Y) (adrs : Adrs) :
    IsQueryBoundP (wotsPkFromSigWith core hash compress sig msg adrs) p
      (vp.params.len * ((vp.params.w - 1) * cF) + cT) :=
  qb_bind p (qb_ofFnM p (fun i : Fin vp.params.len =>
      chainWith hash (wotsChainAdrs adrs i.val) sig[i.val] (chainStepsCore core msg i.val)
        (vp.params.w - 1 - chainStepsCore core msg i.val)) _
    (fun i => (qb_chain p core cF hhash _ _ _ _).mono
      (Nat.mul_le_mul_right _ (Nat.sub_le _ _)))) fun _ => hcompress _ _

include hhash hcompress hnode in
theorem qb_xmssPk (idx : ℕ) (sig : XmssSig vp.params core) (msg : core.Y) (adrs : Adrs) :
    IsQueryBoundP (xmssPkFromSigWith core hash compress nodeHash idx sig msg adrs) p
      (xmssPkB vp cF cT cH) := by
  have hc : ∀ leaf, IsQueryBoundP (PerfectMerkleTree.climbM (xmssNodeHashWith nodeHash adrs) idx
      leaf sig.auth.toList) p (vp.params.hp * cH) := fun leaf => by
    have h := qb_climb p (xmssNodeHashWith nodeHash adrs) cH (fun h i l r => hnode _ l r) idx leaf
      sig.auth.toList
    rwa [Vector.length_toList] at h
  exact qb_bind p (qb_wotsPkFromSig p core cF cT hhash hcompress sig.wots msg _) hc

include hhash hcompress hnode hsecret in
theorem qb_signFromPos (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      IsQueryBoundP (GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash
        secret recoverFinal pos layers h msg) p
        (layers * (xmssSignB vp cF cT cH cS + xmssPkB vp cF cT cH))
  | 0, _, _ => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      exact isQueryBoundP_pure _ _ _
  | 1, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      refine (qb_bind p (m := xmssPkB vp cF cT cH)
        (qb_xmssSign p core cF cT cH cS hhash hcompress hnode hsecret msg _ _) fun sig => ?_).mono
          (by omega)
      cases recoverFinal
      · exact isQueryBoundP_pure _ _ _
      · exact (qb_bind p (m := 0) (qb_xmssPk p core cF cT cH hhash hcompress hnode _ sig msg _)
          fun _ => isQueryBoundP_pure _ _ _).mono (by omega)
  | layers + 2, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret]
      refine (qb_bind p (qb_xmssSign p core cF cT cH cS hhash hcompress hnode hsecret msg _ _)
        fun sig => qb_bind p (qb_xmssPk p core cF cT cH hhash hcompress hnode _ sig msg _)
          fun root => qb_bind p (m := 0)
            (qb_signFromPos false _ (layers + 1) _ root) fun _ =>
              isQueryBoundP_pure _ _ _).mono ?_
      exact Nat.le_of_eq (by ring)

include hhash hnode hsecret in
theorem qb_forsSign (md : List Byte) (adrs : Adrs) :
    IsQueryBoundP (forsSignWithSecret core hash nodeHash secret md adrs) p
      (vp.params.k * (cS + authB (cS + cF) cH vp.params.a)) := by
  refine qb_ofFnM p _ _ fun i => ?_
  have h := qb_authPath p (forsLeafWithSecret core hash secret adrs)
    (forsNodeHashWith nodeHash adrs) (cS + cF) cH
    (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) vp.params.a
    (fun j => qb_bind p (hsecret _) fun x => hhash _ x)
    (fun h i l r => hnode _ l r)
  exact (qb_bind p (hsecret _) fun sk => qb_bind p (m := 0) h
    fun path => isQueryBoundP_pure _ _ _).mono (by omega)

include hhash hcompress hnode in
theorem qb_forsPk (sig : ForsSigCore vp.params core) (md : List Byte) (adrs : Adrs) :
    IsQueryBoundP (forsPkFromSigWith core hash nodeHash compress sig md adrs) p
      (vp.params.k * (cF + vp.params.a * cH) + cT) := by
  refine qb_bind p (qb_ofFnM p _ _ fun i => ?_) fun _ => hcompress _ _
  refine qb_bind p (hhash _ _) fun leaf => ?_
  have h := qb_climb p (forsNodeHashWith nodeHash adrs) cH (fun h i l r => hnode _ l r)
    (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) leaf (sig[i.val]).auth.toList
  rwa [Vector.length_toList] at h

end Count

/-! ## Query counts of the open programs, by kind -/

section OpenCount

/-- `1` if the kinds coincide, `0` otherwise: the cost, for the kind `K`, of one query of kind
`K'`. -/
def ind (K K' : Kind) : ℕ := if K = K' then 1 else 0

theorem query_kindBound {κ : Type} {hspec : OracleSpec κ} {D V : Type} (K : Kind)
    (t : ℕ ⊕ (ι ⊕ (D ⊕ κ))) :
    IsQueryBoundP (liftM ((RSpec gspec D V hspec).query t) :
      OracleComp (RSpec gspec D V hspec) _) (fun t => kind t = K) (ind K (kind t)) :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => by simp [ind, h]

/-- A lifted `ProbComp` makes only `unif` queries. -/
theorem liftM_kindBound {κ : Type} {hspec : OracleSpec κ} {D V β : Type} (K : Kind)
    (hK : K ≠ .unif) (ob : ProbComp β) :
    IsQueryBoundP (liftM ob : OracleComp (RSpec gspec D V hspec) β) (fun t => kind t = K) 0 :=
  IsQueryBoundP.of_imp (fun t ht => by cases t <;> simp_all [kind])
    (isQueryBoundP_liftM_isRight (hs := gspec + ((D →ₒ V) + hspec)) ob)

theorem gameQ_kindBound (K : Kind) (t : ι) :
    IsQueryBoundP (gameQ prims gspec t) (fun t => kind t = K) (ind K .game) :=
  query_kindBound K _

/-- Budget of open key generation: `cS` per secret read, `c` per hash evaluation. -/
def keygenB (vp : ValidatedParams) (cS c : ℕ) : ℕ :=
  merkleB (wotsB vp c cS + c) c vp.params.hp

/-- Budget of one open signature: `cS` per secret read, `c` per hash evaluation. -/
def signB (vp : ValidatedParams) (cS c : ℕ) : ℕ :=
  c + vp.params.k * (cS + authB (cS + c) c vp.params.a) +
    (vp.params.k * (c + vp.params.a * c) + c) +
    vp.params.d * (xmssSignB vp c c c cS + xmssPkB vp c c c)

theorem openKeygen_kindBound (K : Kind) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (openKeygen prims gspec pkSeed) (fun t => kind t = K)
      (keygenB vp (ind K .sec) (ind K .hash)) :=
  qb_xmssNode (fun t => kind t = K) prims.core (ind K .hash) (ind K .hash) (ind K .hash)
    (ind K .sec)
    (hash := PublicHash.f prims.core pkSeed) (compress := PublicHash.tl prims.core pkSeed)
    (nodeHash := PublicHash.h prims.core pkSeed) (secret := secQ prims gspec)
    (fun _ _ => query_kindBound K _) (fun _ _ => query_kindBound K _)
    (fun _ _ _ => query_kindBound K _) (fun _ => query_kindBound K _) _ _ _

theorem openSign_kindBound (K : Kind) (msg : List Byte) (pkSeed : prims.PkSeed)
    (pkRoot R : prims.Y) :
    IsQueryBoundP (openSign prims gspec msg pkSeed pkRoot R) (fun t => kind t = K)
      (signB vp (ind K .sec) (ind K .hash)) := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pkSeed a y :
      OracleComp (OSpec prims gspec) prims.Y) (fun t => kind t = K) (ind K .hash) :=
    fun _ _ => query_kindBound K _
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsQueryBoundP (PublicHash.tl prims.core pkSeed a ys :
      OracleComp (OSpec prims gspec) prims.Y) (fun t => kind t = K) (ind K .hash) :=
    fun _ _ => query_kindBound K _
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pkSeed a l r :
      OracleComp (OSpec prims gspec) prims.Y) (fun t => kind t = K) (ind K .hash) :=
    fun _ _ _ => query_kindBound K _
  have hs : ∀ a : Adrs, IsQueryBoundP (secQ prims gspec a) (fun t => kind t = K) (ind K .sec) :=
    fun _ => query_kindBound K _
  have hm : IsQueryBoundP (PublicHash.hmsg prims.core R pkSeed pkRoot msg :
      OracleComp (OSpec prims gspec) _) (fun t => kind t = K) (ind K .hash) :=
    query_kindBound K _
  unfold openSign GeneralScheme.signInternalWithSecretRandomizerM
  refine (qb_bind _ hm fun digest =>
    qb_bind _ (qb_forsSign _ prims.core _ _ _ hf hh hs _ _) fun forsSig =>
      qb_bind _ (qb_forsPk _ prims.core _ _ _ hf htl hh forsSig _ _) fun forsPk =>
        qb_bind _ (m := 0) (qb_signFromPos _ prims.core _ _ _ _ hf htl hh hs _ _ _ _ _)
          fun htSig => isQueryBoundP_pure _ _ _).mono ?_
  unfold signB
  omega

/-! ### Closed forms -/

theorem signB_le (cS c : ℕ) :
    signB vp cS c ≤ c + vp.params.k * (2 ^ vp.params.a * (cS + c + c)) +
      (vp.params.k * (c + vp.params.a * c) + c) +
      vp.params.d * (2 ^ vp.params.hp * (wotsB vp c cS + c + c) + xmssPkB vp c c c) := by
  have h1 := authB_add (cS + c) c vp.params.a
  have h2 := authB_add (wotsB vp c cS + c) c vp.params.hp
  unfold signB
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)
    le_rfl) (Nat.mul_le_mul_left _ (Nat.add_le_add_right (by unfold xmssSignB; omega) _))

theorem keygenB_game : keygenB vp 0 0 = 0 := by
  simp [keygenB, wotsB, merkleB_zero]

theorem signB_game : signB vp 0 0 = 0 := by
  simp [signB, xmssSignB, xmssPkB, wotsB, authB_zero]

/-- Key generation reads `2^h'·len` secret values. -/
theorem keygenB_sec : keygenB vp 1 0 ≤ 2 ^ vp.params.hp * vp.params.len :=
  (merkleB_le _ _ _).trans (le_of_eq (by simp [wotsB]))

/-- One signature reads at most `signReads vp` secret values. -/
theorem signB_sec : signB vp 1 0 ≤ signReads vp :=
  (signB_le 1 0).trans (le_of_eq (by simp [wotsB, xmssPkB, signReads]))

/-- Hash evaluations of key generation: `2^h'` WOTS+ public keys (`len·(w-1)` chain steps and
one `T_len` each) and at most `2^h'` tree nodes. -/
def keygenHashes (vp : ValidatedParams) : ℕ :=
  2 ^ vp.params.hp * (vp.params.len * (vp.params.w - 1) + 2)

/-- Hash evaluations of one signature (an upper bound): `H_msg`; FORS signing (`k` trees of
`2^a` leaves and nodes); FORS root recovery (`k·(a+1)` and one `T_k`); and per hypertree layer
one XMSS signature (as key generation) and one XMSS root recovery (`len·(w-1) + 1 + h'`). -/
def signHashes (vp : ValidatedParams) : ℕ :=
  1 + vp.params.k * (2 ^ vp.params.a * 2) + (vp.params.k * (1 + vp.params.a) + 1) +
    vp.params.d * (2 ^ vp.params.hp * (vp.params.len * (vp.params.w - 1) + 2) +
      (vp.params.len * (vp.params.w - 1) + 1 + vp.params.hp))

theorem keygenB_hash : keygenB vp 0 1 ≤ keygenHashes vp :=
  (merkleB_le _ _ _).trans (le_of_eq (by simp [wotsB, keygenHashes]))

theorem signB_hash : signB vp 0 1 ≤ signHashes vp :=
  (signB_le 0 1).trans (le_of_eq (by simp [wotsB, xmssPkB, signHashes]))

end OpenCount

end Lazy
end Reduction
