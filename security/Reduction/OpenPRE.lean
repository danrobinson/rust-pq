import Reduction.Tables
import Reduction.Harness

/-!
# Step 5: the FORS open-preimage branch (SM-DT-OpenPRE on `F`)

`bOpenPre A` (EC: `R_FPOpenPRE_FOpenPRE ∘ R_MFORSTWESNPRFEUFCMA_EUFCMA`):

* `pick` (seed hidden): sample the table — eagerly, `2^256` cells, as written; only its WOTS+
  cells are read (`Reduction/Lazy/Sparse.lean`, `bOpenPreS`) — and commit to the tweaks of
  **all** `2^h·k·2^a` FORS leaves (`14·2^75` at 128s), in the order of the ledger
  `forsLeafAddresses`.  Not feasible in any variant;
* `find` (seed and leaf images `ys` revealed): the public key needs only WOTS+ secrets.  A signing
  query builds the FORS trees from the leaf *images* — the honest program is run with the leaf
  hash replaced by the identity and the "secret" at a leaf replaced by its image — and obtains the
  `k` revealed secret values from the opening oracle; the hypertree part is honest.  After `A`
  outputs a forgery, the first FORS tree whose opened leaf was never opened and whose image is hit
  by the forged secret value gives the answer.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- The tweaks `bOpenPre` commits to: all FORS leaves, in ledger order. -/
def forsLeafKeys (vp : ValidatedParams) (prims : Primitives vp.params) : List prims.AdrsKey :=
  (forsLeafAddresses vp).map prims.adrsToKey

/-- The FORS leaf address whose secret lives at the `FORS_PRF` address `a`. -/
def skToLeaf (a : Adrs) : Adrs := ⟨a.layer, a.tree, AddrType.forsTree.toCode, a.word1, 0, a.word3⟩

/-- Target index of a FORS leaf address. -/
def leafTarget (vp : ValidatedParams) (prims : Primitives vp.params) [DecidableEq prims.AdrsKey]
    (leaf : Adrs) : ℕ :=
  (forsLeafKeys vp prims).idxOf (prims.adrsToKey leaf)

/-- The image of a FORS leaf, read off the challenge images. -/
def leafImage (ys : List prims.Y) (leaf : Adrs) : prims.Y :=
  ys.getD (leafTarget vp prims leaf) default

/-- The FORS authentication paths for digest `md`, computed from leaf images only (the `sk`
fields of the result are images, to be replaced by opened preimages). -/
def forsSigFromImages (pkSeed : prims.PkSeed) (ys : List prims.Y) (md : List Byte)
    (adrs : Adrs) : ForsSigCore vp.params prims.core :=
  (forsSignWithSecret prims.core
    (fun a x => if a.word2 = 0 then x else prims.F pkSeed a x)
    (fun a l r => prims.H pkSeed a l r)
    (fun a => leafImage (vp := vp) ys (skToLeaf a)) md adrs :
    Id (ForsSigCore vp.params prims.core))

/-- The answer extracted from a forgery: `(target index, preimage)`. -/
def openPreAnswer (pk : PublicKeyCore prims.core) (ys : List prims.Y) (log : G2Log prims)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) : ℕ × prims.Y :=
  let parts : DigestParts vp.params := digestParts pk sig.randomness msg
  let opened := openedLeaves pk (G2Log.signed log)
  ((List.finRange vp.params.k).findSome? fun i =>
    let leaf := forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)
    if (parts.forsAdrs, leafIndex parts i) ∉ opened ∧
        prims.F pk.pkSeed leaf (sig.fors[i.val]).sk = leafImage (vp := vp) ys leaf then
      some (leafTarget vp prims leaf, (sig.fors[i.val]).sk)
    else none).getD (0, default)

/-- Oracle interface of the `find` phase. -/
abbrev openSpecY (prims : Primitives vp.params) : OracleSpec (ℕ ⊕ ℕ) :=
  unifSpec + TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.openSpec prims.Y

/-- The honest hypertree signature over a table, in the identity monad. -/
def opHt (T : SecretTable vp prims) (pkSeed : prims.PkSeed) (m0 : prims.Y)
    (parts : DigestParts vp.params) : GeneralHypertree.Signature vp prims.core :=
  (GeneralHypertree.signWithSecret prims.core (fun a x => prims.F pkSeed a x)
    (fun a xs => prims.Tl pkSeed a xs) (fun a l r => prims.H pkSeed a l r)
    (fun a => secretOf vp prims T a) m0 parts : Id (GeneralHypertree.Signature vp prims.core))

/-- The signing procedure of `bOpenPre` for message `m` and randomizer `R`: FORS authentication
paths from the leaf images, the `k` revealed secrets from the opening oracle, honest hypertree. -/
def openSign (pk : PublicKeyCore prims.core) (tbl : SecretTable vp prims) (ys : List prims.Y)
    (m : List Byte) (R : prims.Y) :
    OracleComp (openSpecY prims) (GeneralScheme.SignatureCore vp prims.core) := do
  let forsSig ← (Vector.ofFnM fun i : Fin vp.params.k => do
    let x ← ((openSpecY prims).query (Sum.inr (leafTarget vp prims
        (forsNodeAdrs (digestParts pk R m).forsAdrs 0 (leafIndex (digestParts pk R m) i)))) :
      OracleComp (openSpecY prims) prims.Y)
    pure (⟨x, ((forsSigFromImages (vp := vp) pk.pkSeed ys (digestParts pk R m).md.toList
      (digestParts pk R m).forsAdrs)[i.val]).auth⟩ : ForsTreeSigCore vp.params prims.core) :
    OracleComp (openSpecY prims) (ForsSigCore vp.params prims.core))
  return ⟨R, forsSig, opHt tbl pk.pkSeed
    (forsPkFromSig prims forsSig (digestParts pk R m).md.toList pk.pkSeed
      (digestParts pk R m).forsAdrs) (digestParts pk R m)⟩

/-- `bOpenPre` with the table sampler as a parameter (the proofs are carried out for an abstract
sampler; see the `sampleTable` hazard in `status/BRIEF.md`). -/
noncomputable def bOpenPreWith (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Adversary
      (forsOpenPreProblem vp prims pkSeedDist) where
  State := SecretTable vp prims
  pick := do
    let tbl ← (liftM my :
      OracleComp (unifSpec + TweakableHash.SourceFinalValidity.collectionSpec
        (forsOpenPreProblem vp prims pkSeedDist).thColl) (SecretTable vp prims))
    return (tbl, forsLeafKeys vp prims)
  find := fun tbl pkSeed ys => do
    let z ← runForgerLog A (idealPk vp prims tbl pkSeed) lazyRandomizerLift
      (openSign (idealPk vp prims tbl pkSeed) tbl ys)
    return openPreAnswer (idealPk vp prims tbl pkSeed) ys z.2 z.1.1 z.1.2

/-- The SM-DT-OpenPRE adversary built from a forger. -/
noncomputable def bOpenPre (A : Forger vp prims optRand pkSeedDist) :
    TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.Adversary
      (forsOpenPreProblem vp prims pkSeedDist) :=
  bOpenPreWith (sampleTable vp prims) A

/-! ## Deterministic helpers -/

section Det

set_option linter.unusedSectionVars false

/-- The `FORS_PRF` address holding the secret of the FORS leaf `leaf`. -/
def skOf (leaf : Adrs) : Adrs :=
  ⟨leaf.layer, leaf.tree, AddrType.forsPrf.toCode, leaf.word1, 0, leaf.word3⟩

theorem op_wotsTops_congr {p : Params} (core : CorePrimitives p) {m : Type → Type} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (s1 s2 : Adrs → m core.Y) (adrs : Adrs)
    (h : ∀ a : Adrs, a.layer = adrs.layer → a.tree = adrs.tree →
      a.type = AddrType.wotsPrf.toCode → s1 a = s2 a) :
    wotsPkGenTopsWithSecret core hash s1 adrs = wotsPkGenTopsWithSecret core hash s2 adrs := by
  unfold wotsPkGenTopsWithSecret
  exact congrArg Vector.ofFnM (funext fun i => by rw [h (wotsSkAdrs adrs i.val) rfl rfl rfl])

theorem op_wotsSign_congr {p : Params} (core : CorePrimitives p) {m : Type → Type} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (s1 s2 : Adrs → m core.Y) (adrs : Adrs)
    (h : ∀ a : Adrs, a.layer = adrs.layer → a.tree = adrs.tree →
      a.type = AddrType.wotsPrf.toCode → s1 a = s2 a) (msg : core.Y) :
    wotsSignWithSecret core hash s1 msg adrs = wotsSignWithSecret core hash s2 msg adrs := by
  unfold wotsSignWithSecret
  exact congrArg Vector.ofFnM (funext fun i => by rw [h (wotsSkAdrs adrs i.val) rfl rfl rfl])

theorem op_xmssLeaf_congr {p : Params} (core : CorePrimitives p) {m : Type → Type} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (s1 s2 : Adrs → m core.Y) (adrs : Adrs)
    (h : ∀ a : Adrs, a.layer = adrs.layer → a.tree = adrs.tree →
      a.type = AddrType.wotsPrf.toCode → s1 a = s2 a) :
    xmssLeafWithSecret core hash compress s1 adrs = xmssLeafWithSecret core hash compress s2 adrs := by
  funext t
  unfold xmssLeafWithSecret wotsPkGenWithSecret
  rw [op_wotsTops_congr core hash s1 s2 (wotsLeafAdrs adrs t) (fun a hl ht hty => h a hl ht hty)]

theorem op_xmssSign_congr {p : Params} (core : CorePrimitives p) {m : Type → Type} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (s1 s2 : Adrs → m core.Y) (adrs : Adrs)
    (h : ∀ a : Adrs, a.layer = adrs.layer → a.tree = adrs.tree →
      a.type = AddrType.wotsPrf.toCode → s1 a = s2 a) (msg : core.Y) (idx : ℕ) :
    xmssSignWithSecret core hash compress nodeHash s1 msg adrs idx =
      xmssSignWithSecret core hash compress nodeHash s2 msg adrs idx := by
  unfold xmssSignWithSecret
  rw [op_xmssLeaf_congr core hash compress s1 s2 adrs h,
    op_wotsSign_congr core hash s1 s2 (wotsLeafAdrs adrs idx) (fun a hl ht hty => h a hl ht hty)]

/-- A provider is only read at `WOTS_PRF` addresses with in-range layer and tree. -/
def WotsAgree {Y : Type} {m : Type → Type} (s1 s2 : Adrs → m Y) : Prop :=
  ∀ a : Adrs, a.layer < 2 ^ 32 → a.tree < 2 ^ 96 → a.type = AddrType.wotsPrf.toCode → s1 a = s2 a

theorem op_pos_agree (hb : CanonicalAddressBounds vp.params) {Y : Type} {m : Type → Type}
    {s1 s2 : Adrs → m Y} (h : WotsAgree s1 s2) (pos : LayerPosition vp) :
    ∀ a : Adrs, a.layer = pos.toAdrs.layer → a.tree = pos.toAdrs.tree →
      a.type = AddrType.wotsPrf.toCode → s1 a = s2 a := by
  intro a hl ht hty
  obtain ⟨f1, f2, -⟩ := Adrs.fits_of_isCanonical _ (layerPosition_toAdrs_isCanonical hb pos)
  rw [Adrs.fits_iff] at f1 f2
  exact h a (by rw [hl]; exact f1) (by rw [ht]; exact f2) hty

theorem op_signFromPosition_congr (hb : CanonicalAddressBounds vp.params)
    (core : CorePrimitives vp.params) {m : Type → Type} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (s1 s2 : Adrs → m core.Y)
    (h : WotsAgree s1 s2) (recoverFinal : Bool) (pos : LayerPosition vp) :
    ∀ (layers : ℕ) (hl : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash s1 recoverFinal pos
          layers hl msg =
        GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash s2 recoverFinal pos
          layers hl msg
  | 0, _, _ => by
      rw [GeneralHypertree.signFromPositionWithSecret, GeneralHypertree.signFromPositionWithSecret]
  | 1, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret, GeneralHypertree.signFromPositionWithSecret,
        op_xmssSign_congr core hash compress nodeHash s1 s2 _ (op_pos_agree hb h pos)]
  | layers + 2, hremaining, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret, GeneralHypertree.signFromPositionWithSecret,
        op_xmssSign_congr core hash compress nodeHash s1 s2 _ (op_pos_agree hb h pos)]
      refine bind_congr fun sig => bind_congr fun root => ?_
      dsimp only
      rw [op_signFromPosition_congr hb core hash compress nodeHash s1 s2 h false _ (layers + 1)]

theorem op_signWithSecret_congr (hb : CanonicalAddressBounds vp.params)
    (core : CorePrimitives vp.params) {m : Type → Type} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (s1 s2 : Adrs → m core.Y)
    (h : WotsAgree s1 s2) (msg : core.Y) (parts : DigestParts vp.params) :
    GeneralHypertree.signWithSecret core hash compress nodeHash s1 msg parts =
      GeneralHypertree.signWithSecret core hash compress nodeHash s2 msg parts :=
  op_signFromPosition_congr hb core hash compress nodeHash s1 s2 h _ _ _ _ _

/-- Key generation over a table reads only in-range `WOTS_PRF` cells. -/
theorem op_idealRoot_congr (hb : CanonicalAddressBounds vp.params)
    (tbl tbl' : SecretTable vp prims) (pkSeed : prims.PkSeed)
    (h : WotsAgree (m := Id) (fun a => secretOf vp prims tbl a) (fun a => secretOf vp prims tbl' a)) :
    idealRoot vp prims tbl pkSeed = idealRoot vp prims tbl' pkSeed := by
  unfold idealRoot GeneralScheme.keygenInternalWithSecretM GeneralHypertree.rootWithSecretM
    GeneralHypertree.rootWithSecret xmssRootWithSecret xmssNodeWithSecret
  rw [op_xmssLeaf_congr prims.core _ _ (fun a => pure (secretOf vp prims tbl a))
    (fun a => pure (secretOf vp prims tbl' a)) _ (fun a hl ht hty => by
      have h1 : a.layer < 2 ^ 32 := by
        rw [hl]
        show vp.params.d - 1 < 2 ^ 32
        have := hb.d_le
        have := vp.valid.d_pos
        omega
      have h2 : a.tree < 2 ^ 96 := by
        rw [ht]
        show 0 < 2 ^ 96
        norm_num
      exact congrArg pure (h a h1 h2 hty))]

open PerfectMerkleTree in
theorem op_merkleRootM_congr {Y : Type} {m : Type → Type} [Monad m] (leaf1 leaf2 : ℕ → m Y)
    (node : ℕ → ℕ → Y → Y → m Y) : ∀ (z t : ℕ),
    (∀ i, i / 2 ^ z = t → leaf1 i = leaf2 i) →
      merkleRootM leaf1 node z t = merkleRootM leaf2 node z t
  | 0, t, h => by
      rw [merkleRootM, merkleRootM]
      exact h t (by simp)
  | z + 1, t, h => by
      rw [merkleRootM, merkleRootM,
        op_merkleRootM_congr leaf1 leaf2 node z (2 * t) (fun i hi => h i (by
          rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]; omega)),
        op_merkleRootM_congr leaf1 leaf2 node z (2 * t + 1) (fun i hi => h i (by
          rw [pow_succ, ← Nat.div_div_eq_div_mul, hi]; omega))]

open PerfectMerkleTree in
theorem op_authPathM_congr {Y : Type} {m : Type → Type} [Monad m] (leaf1 leaf2 : ℕ → m Y)
    (node : ℕ → ℕ → Y → Y → m Y) (idx hgt : ℕ)
    (h : ∀ i, i / 2 ^ hgt = idx / 2 ^ hgt → leaf1 i = leaf2 i) : ∀ z, z ≤ hgt →
      intrinsicAuthPathM leaf1 node idx z = intrinsicAuthPathM leaf2 node idx z
  | 0, _ => by rw [intrinsicAuthPathM, intrinsicAuthPathM]
  | z + 1, hz => by
      rw [intrinsicAuthPathM, intrinsicAuthPathM, op_authPathM_congr leaf1 leaf2 node idx hgt h z
        (by omega),
        op_merkleRootM_congr leaf1 leaf2 node z (sibling (idx / 2 ^ z)) (fun i hi => h i (by
          obtain ⟨c, rfl⟩ : ∃ c, hgt = z + (c + 1) := ⟨hgt - z - 1, by omega⟩
          rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hi, pow_succ,
            Nat.mul_comm, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul (idx / 2 ^ z),
            sibling_div_two]))]

theorem op_ofFnM_id_getElem {α : Type} : ∀ {k : ℕ} (f : Fin k → Id α) (i : ℕ) (hi : i < k),
    (Id.run (Vector.ofFnM f))[i] = Id.run (f ⟨i, hi⟩)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, f, i, hi => by
    rw [Vector.ofFnM_succ]
    simp only [Id.run_bind, Id.run_pure]
    by_cases h : i < k
    · rw [Vector.getElem_push_lt h]
      exact op_ofFnM_id_getElem (fun j => f j.castSucc) i h
    · have : i = k := by omega
      subst this
      rw [Vector.getElem_push_eq]
      rfl

/-- The honest FORS signature over a table, in the identity monad. -/
def opFors (T : SecretTable vp prims) (pkSeed : prims.PkSeed) (md : List Byte) (adrs : Adrs) :
    ForsSigCore vp.params prims.core :=
  (forsSignWithSecret prims.core (fun a x => prims.F pkSeed a x)
    (fun a l r => prims.H pkSeed a l r) (fun a => secretOf vp prims T a) md adrs :
    Id (ForsSigCore vp.params prims.core))

theorem op_idealSign_eq (T : SecretTable vp prims) (msg : List Byte)
    (pk : PublicKeyCore prims.core) (R : prims.Y) :
    idealSign vp prims T msg pk R =
      ⟨R, opFors T pk.pkSeed (digestParts pk R msg).md.toList (digestParts pk R msg).forsAdrs,
        opHt T pk.pkSeed
          (forsPkFromSig prims
            (opFors T pk.pkSeed (digestParts pk R msg).md.toList (digestParts pk R msg).forsAdrs)
            (digestParts pk R msg).md.toList pk.pkSeed (digestParts pk R msg).forsAdrs)
          (digestParts pk R msg)⟩ := by
  have k1 : ∀ (md : List Byte) (adrs : Adrs),
      simulateQ (PublicHash.impl prims) (forsSignWithSecretM prims.core
        (fun a => pure (secretOf vp prims T a)) md pk.pkSeed adrs :
          OracleComp (publicHashSpec prims.core) _) = opFors T pk.pkSeed md adrs := by
    intro md adrs
    exact forsSignWithSecret_natural prims.core (simulateQ' (PublicHash.impl prims))
      (PublicHash.f prims.core pk.pkSeed) (fun a x => (prims.F pk.pkSeed a x : Id prims.Y))
      (PublicHash.h prims.core pk.pkSeed) (fun a l r => (prims.H pk.pkSeed a l r : Id prims.Y))
      (fun a => pure (secretOf vp prims T a)) (fun a => pure (secretOf vp prims T a))
      (fun a y => PublicHash.simulateQ_f prims pk.pkSeed a y)
      (fun a l r => PublicHash.simulateQ_h prims pk.pkSeed a l r)
      (fun a _ => simulateQ_pure (PublicHash.impl prims) _) md adrs
  have k3 : ∀ (m0 : prims.Y) (parts : DigestParts vp.params),
      simulateQ (PublicHash.impl prims) (GeneralHypertree.signWithSecretM prims.core
        (fun a => pure (secretOf vp prims T a)) m0 pk.pkSeed parts :
          OracleComp (publicHashSpec prims.core) _) = opHt T pk.pkSeed m0 parts := by
    intro m0 parts
    exact GeneralHypertree.signWithSecret_natural prims.core
      (simulateQ' (PublicHash.impl prims))
      (PublicHash.f prims.core pk.pkSeed) (fun a x => (prims.F pk.pkSeed a x : Id prims.Y))
      (PublicHash.tl prims.core pk.pkSeed) (fun a xs => (prims.Tl pk.pkSeed a xs : Id prims.Y))
      (PublicHash.h prims.core pk.pkSeed) (fun a l r => (prims.H pk.pkSeed a l r : Id prims.Y))
      (fun a => pure (secretOf vp prims T a)) (fun a => pure (secretOf vp prims T a))
      (fun a y => PublicHash.simulateQ_f prims pk.pkSeed a y)
      (fun a xs => PublicHash.simulateQ_tl prims pk.pkSeed a xs)
      (fun a l r => PublicHash.simulateQ_h prims pk.pkSeed a l r)
      (fun a _ => simulateQ_pure (PublicHash.impl prims) _) m0 parts
  rw [← k1, ← k3]
  unfold idealSign GeneralScheme.signInternalWithSecretRandomizerM
  simp only [simulateQ_bind, simulateQ_pure, PublicHash.simulateQ_hmsg]
  rfl

theorem op_fors_idx_div (p : Params) (md : List Byte) (i : ℕ) :
    (i * 2 ^ p.a + forsIdx p md i) / 2 ^ p.a = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (forsIdx_lt p md i), Nat.zero_add]

theorem opFors_sk (T : SecretTable vp prims) (pkSeed : prims.PkSeed) (md : List Byte)
    (adrs : Adrs) (i : ℕ) (hi : i < vp.params.k) :
    ((opFors T pkSeed md adrs)[i]).sk =
      secretOf vp prims T (forsSkAdrs adrs (i * 2 ^ vp.params.a + forsIdx vp.params md i)) := by
  unfold opFors forsSignWithSecret
  exact congrArg ForsTreeSigCore.sk (op_ofFnM_id_getElem _ i hi)

theorem opFors_auth (T : SecretTable vp prims) (pkSeed : prims.PkSeed) (md : List Byte)
    (adrs : Adrs) (i : ℕ) (hi : i < vp.params.k) :
    ((opFors T pkSeed md adrs)[i]).auth =
      (PerfectMerkleTree.intrinsicAuthPathM
        (forsLeafWithSecret prims.core (fun a x => (prims.F pkSeed a x : Id prims.Y))
          (fun a => (secretOf vp prims T a : Id prims.Y)) adrs)
        (forsNodeHashWith (fun a l r => (prims.H pkSeed a l r : Id prims.Y)) adrs)
        (i * 2 ^ vp.params.a + forsIdx vp.params md i) vp.params.a : Id _) := by
  unfold opFors forsSignWithSecret
  exact congrArg ForsTreeSigCore.auth (op_ofFnM_id_getElem _ i hi)

theorem forsSigFromImages_auth_eq (pkSeed : prims.PkSeed) (ys : List prims.Y) (md : List Byte)
    (adrs : Adrs) (i : ℕ) (hi : i < vp.params.k) :
    ((forsSigFromImages (vp := vp) pkSeed ys md adrs)[i]).auth =
      (PerfectMerkleTree.intrinsicAuthPathM
        (fun t => (leafImage (vp := vp) ys (forsNodeAdrs adrs 0 t) : Id prims.Y))
        (forsNodeHashWith (fun a l r => (prims.H pkSeed a l r : Id prims.Y)) adrs)
        (i * 2 ^ vp.params.a + forsIdx vp.params md i) vp.params.a : Id _) := by
  unfold forsSigFromImages forsSignWithSecret
  exact congrArg ForsTreeSigCore.auth (op_ofFnM_id_getElem _ i hi)

/-- The leaf `(tree i, index j)` of the FORS instance of `parts` is in the ledger. -/
theorem op_leaf_mem (parts : DigestParts vp.params) (j : ℕ)
    (hj : j < vp.params.k * 2 ^ vp.params.a) :
    forsNodeAdrs parts.forsAdrs 0 j ∈ forsLeafAddresses vp := by
  have hpos : 0 < 2 ^ vp.params.a := by positivity
  have h1 : j / 2 ^ vp.params.a < vp.params.k := by
    rw [Nat.div_lt_iff_lt_mul hpos]; exact hj
  have h := mem_forsLeafAddresses vp (BottomPosition.ofDigestParts vp parts)
    ⟨j / 2 ^ vp.params.a, h1⟩ ⟨j % 2 ^ vp.params.a, Nat.mod_lt _ hpos⟩
  have e : j / 2 ^ vp.params.a * vp.params.t + j % 2 ^ vp.params.a = j := by
    show j / 2 ^ vp.params.a * 2 ^ vp.params.a + j % 2 ^ vp.params.a = j
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  simpa only [e, BottomPosition.forsAdrs_ofDigestParts] using h

theorem op_leafIndex_lt (parts : DigestParts vp.params) (i : Fin vp.params.k) :
    leafIndex parts i < vp.params.k * 2 ^ vp.params.a := by
  have h1 := forsIdx_lt vp.params parts.md.toList i.val
  have h2 : (i.val + 1) * 2 ^ vp.params.a ≤ vp.params.k * 2 ^ vp.params.a :=
    Nat.mul_le_mul_right _ i.isLt
  unfold leafIndex
  rw [Nat.add_mul] at h2
  omega

end Det

/-! ## Lemmas -/

/-- The committed tweaks are distinct and there are `openPreTargets vp` of them. -/
theorem forsLeafKeys_nodup_length (hS : Structural vp prims) :
    (forsLeafKeys vp prims).Nodup ∧ (forsLeafKeys vp prims).length = openPreTargets vp := by
  refine ⟨?_, by simp [forsLeafKeys, openPreTargets]⟩
  refine List.Nodup.map_on (fun a ha b hb hab => ?_) (forsLeafAddresses_nodup vp)
  exact hS.keyInj (addressFacts_forsLeafAddresses vp hS.bounds a ha)
    (addressFacts_forsLeafAddresses vp hS.bounds b hb) hab

/-- Key generation reads no FORS secret: the root depends only on the WOTS+ entries. -/
theorem idealRoot_congr (hS : Structural vp prims) (tbl tbl' : SecretTable vp prims)
    (pkSeed : prims.PkSeed)
    (h : ∀ a : Adrs, a.type = AddrType.wotsPrf.toCode →
      secretOf vp prims tbl a = secretOf vp prims tbl' a) :
    idealRoot vp prims tbl pkSeed = idealRoot vp prims tbl' pkSeed := by
  exact op_idealRoot_congr hS.bounds tbl tbl' pkSeed (fun a _ _ hty => h a hty)

theorem op_auth (tbl : SecretTable vp prims)
    (pk : PublicKeyCore prims.core) (msg : List Byte) (R : prims.Y) (ys : List prims.Y)
    (hys : ∀ leaf ∈ forsLeafAddresses vp, leafImage (vp := vp) ys leaf =
      prims.F pk.pkSeed leaf (secretOf vp prims tbl (skOf leaf)))
    (i : Fin vp.params.k) :
    ((forsSigFromImages (vp := vp) pk.pkSeed ys (digestParts pk R msg).md.toList
        (digestParts pk R msg).forsAdrs)[i.val]).auth =
      ((opFors tbl pk.pkSeed (digestParts pk R msg).md.toList
        (digestParts pk R msg).forsAdrs)[i.val]).auth := by
  rw [forsSigFromImages_auth_eq _ _ _ _ _ i.isLt, opFors_auth _ _ _ _ _ i.isLt]
  refine op_authPathM_congr _ _ _ _ vp.params.a (fun j hj => ?_) _ le_rfl
  rw [op_fors_idx_div] at hj
  have hjlt : j < vp.params.k * 2 ^ vp.params.a := by
    have hpos : 0 < 2 ^ vp.params.a := by positivity
    have := (Nat.div_lt_iff_lt_mul hpos).1 (hj ▸ i.isLt)
    exact this
  exact hys _ (op_leaf_mem (digestParts pk R msg) j hjlt)

/-- Simulation correctness of the FORS part: with the images of the table's own FORS secrets,
`forsSigFromImages` has the authentication paths of the honest FORS signature. -/
theorem forsSigFromImages_auth (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pk : PublicKeyCore prims.core) (msg : List Byte) (R : prims.Y) (ys : List prims.Y)
    (hys : ∀ leaf ∈ forsLeafAddresses vp, leafImage (vp := vp) ys leaf =
      prims.F pk.pkSeed leaf (secretOf vp prims tbl
        ⟨leaf.layer, leaf.tree, AddrType.forsPrf.toCode, leaf.word1, 0, leaf.word3⟩))
    (i : Fin vp.params.k) :
    ((forsSigFromImages (vp := vp) pk.pkSeed ys (digestParts pk R msg).md.toList
        (digestParts pk R msg).forsAdrs)[i.val]).auth =
      ((idealSign vp prims tbl msg pk R).fors[i.val]).auth := by
  rw [op_idealSign_eq]
  exact op_auth tbl pk msg R ys hys i

/-! ## Simulation: `bOpenPre` inside the OpenPRE game is `G2` -/

section Sim

open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity

variable (targets : List (prims.AdrsKey × prims.Y))

/-- The answer of the opening oracle at index `j`. -/
def openAns (j : ℕ) : prims.Y := (targets[j]?.map Prod.snd).getD default

theorem op_find_liftM_run {α : Type} (oa : ProbComp α) (opened : List ℕ) :
    (simulateQ (findOracles targets) (liftM oa : OracleComp (openSpecY prims) α)).run opened =
      (fun a => (a, opened)) <$> oa := by
  have h : simulateQ (findOracles targets) (liftM oa : OracleComp (openSpecY prims) α) =
      liftM oa := by
    simp [findOracles, QueryImpl.simulateQ_add_liftM_left]
  rw [h]
  simp

theorem op_find_query_run (j : ℕ) (opened : List ℕ) :
    (simulateQ (findOracles targets)
      ((openSpecY prims).query (Sum.inr j) : OracleComp (openSpecY prims) prims.Y)).run opened =
      pure (openAns targets j, opened ++ [j]) := by
  erw [simulateQ_spec_query]
  simp [findOracles, openOracle, openAns]

theorem op_ofFnM_open {α : Type} : ∀ {n : ℕ} (g : Fin n → ℕ) (h : Fin n → prims.Y → α)
    (opened : List ℕ),
    (simulateQ (findOracles targets) (Vector.ofFnM fun i : Fin n => do
      let x ← ((openSpecY prims).query (Sum.inr (g i)) : OracleComp (openSpecY prims) prims.Y)
      pure (h i x))).run opened =
      pure (Vector.ofFn fun i => h i (openAns targets (g i)),
        opened ++ (List.finRange n).map g)
  | 0, g, h, opened => by
      simp only [Vector.ofFnM_zero, simulateQ_pure, StateT.run_pure]
      congr 1
      simp
  | n + 1, g, h, opened => by
      simp only [Vector.ofFnM_succ, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure]
      rw [op_ofFnM_open (fun i => g i.castSucc) (fun i => h i.castSucc) opened]
      simp only [pure_bind]
      rw [op_find_query_run]
      simp only [pure_bind]
      congr 1
      refine Prod.ext ?_ ?_
      · ext i hi
        by_cases hlt : i < n
        · simp [Vector.getElem_push_lt hlt]
        · have : i = n := by omega
          subst this
          simp [Fin.last]
      · simp [List.finRange_succ_last, List.append_assoc]

end Sim

section Sim2

open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity

/-- The target indices opened by signing `(m, R)`. -/
def openIdx (pk : PublicKeyCore prims.core) (m : List Byte) (R : prims.Y) : List ℕ :=
  (List.finRange vp.params.k).map fun i => leafTarget vp prims
    (forsNodeAdrs (digestParts pk R m).forsAdrs 0 (leafIndex (digestParts pk R m) i))

/-- The opening-oracle state as a function of the `G2` transcript. -/
def openedOf (pk : PublicKeyCore prims.core) (log : G2Log prims) : List ℕ :=
  log.flatMap fun e => openIdx pk e.1 e.2.2

theorem openedOf_append (pk : PublicKeyCore prims.core) (log : G2Log prims)
    (e : List Byte × prims.Y × prims.Y) :
    openedOf pk (log ++ [e]) = openedOf pk log ++ openIdx pk e.1 e.2.2 := by
  simp [openedOf]

/-- What the simulation needs: `tbl` (used for the hypertree) and `T` (the table of the simulated
`G2`) agree on WOTS+ cells; the opening oracle returns `T`'s FORS secrets; the leaf images are the
images of `T`'s FORS secrets. -/
structure SimHyp (pk : PublicKeyCore prims.core) (tbl T : SecretTable vp prims)
    (ys : List prims.Y) (targets : List (prims.AdrsKey × prims.Y)) : Prop where
  bounds : CanonicalAddressBounds vp.params
  wots : WotsAgree (m := Id) (fun a => secretOf vp prims tbl a) (fun a => secretOf vp prims T a)
  opens : ∀ leaf ∈ forsLeafAddresses vp,
    openAns targets (leafTarget vp prims leaf) = secretOf vp prims T (skOf leaf)
  imgs : ∀ leaf ∈ forsLeafAddresses vp,
    leafImage (vp := vp) ys leaf = prims.F pk.pkSeed leaf (secretOf vp prims T (skOf leaf))

variable {pk : PublicKeyCore prims.core} {tbl T : SecretTable vp prims} {ys : List prims.Y}
  {targets : List (prims.AdrsKey × prims.Y)}

theorem op_forsTreeSig_ext (a b : ForsTreeSigCore vp.params prims.core) (h1 : a.sk = b.sk)
    (h2 : a.auth = b.auth) : a = b := by
  cases a; cases b; simp_all

theorem op_sign_run (H : SimHyp pk tbl T ys targets) (m : List Byte) (R : prims.Y)
    (opened : List ℕ) :
    (simulateQ (findOracles targets) (openSign pk tbl ys m R)).run opened =
      pure (idealSign vp prims T m pk R, opened ++ openIdx pk m R) := by
  unfold openSign
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [op_ofFnM_open targets]
  simp only [pure_bind]
  have hV : (Vector.ofFn fun i : Fin vp.params.k =>
      (⟨openAns targets (leafTarget vp prims
          (forsNodeAdrs (digestParts pk R m).forsAdrs 0 (leafIndex (digestParts pk R m) i))),
        ((forsSigFromImages (vp := vp) pk.pkSeed ys (digestParts pk R m).md.toList
          (digestParts pk R m).forsAdrs)[i.val]).auth⟩ : ForsTreeSigCore vp.params prims.core)) =
      opFors T pk.pkSeed (digestParts pk R m).md.toList (digestParts pk R m).forsAdrs := by
    ext i hi
    rw [Vector.getElem_ofFn]
    refine op_forsTreeSig_ext _ _ ?_ ?_
    · rw [opFors_sk _ _ _ _ _ hi]
      exact H.opens _ (op_leaf_mem _ _ (op_leafIndex_lt (digestParts pk R m) ⟨i, hi⟩))
    · exact op_auth T pk m R ys H.imgs ⟨i, hi⟩
  rw [hV, op_idealSign_eq]
  have hht : ∀ m0, opHt tbl pk.pkSeed m0 (digestParts pk R m) =
      opHt T pk.pkSeed m0 (digestParts pk R m) := fun m0 =>
    op_signWithSecret_congr (m := Id) H.bounds prims.core (fun a x => prims.F pk.pkSeed a x)
      (fun a xs => prims.Tl pk.pkSeed a xs) (fun a l r => prims.H pk.pkSeed a l r)
      (fun a => secretOf vp prims tbl a) (fun a => secretOf vp prims T a) H.wots m0 _
  rw [hht]
  rfl

variable (optRand) (pk) (tbl) (ys)

/-- The handler `bOpenPre` runs the forger against. -/
noncomputable abbrev opImplB :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (openSpecY prims))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (openSpecY prims))).liftTarget
      (StateT (G2Log prims) (OracleComp (openSpecY prims))) +
    logSignOracle optRand pk lazyRandomizerLift (openSign pk tbl ys)

/-- The handler of `G2`. -/
noncomputable abbrev opImplG (signR : List Byte → prims.Y →
      GeneralScheme.SignatureCore vp prims.core) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
    g2SignOracle optRand pk signR

theorem op_sim_step (H : SimHyp pk tbl T ys targets) (t : ℕ ⊕ List Byte) (log : G2Log prims) :
    (simulateQ (findOracles targets)
        ((opImplB optRand pk tbl ys t).run log)).run (openedOf pk log) =
      (fun z => (z, openedOf pk z.2)) <$>
        (opImplG optRand pk (fun m R => idealSign vp prims T m pk R) t).run log := by
  rcases t with n | msg
  · have h := op_find_liftM_run (prims := prims) targets
      (liftM (unifSpec.query n) : ProbComp _) (openedOf pk log)
    simp [opImplB, opImplG]
    erw [h]
    simp
  · simp only [opImplB, opImplG, logSignOracle, g2SignOracle, QueryImpl.add_apply_inr]
    simp
    erw [op_find_liftM_run]
    simp only [bind_map_left]
    refine bind_congr (m := ProbComp) fun addrnd => ?_
    unfold lazyRandomizerLift
    erw [op_find_liftM_run]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
    refine bind_congr (m := ProbComp) fun R => ?_
    rw [op_sign_run H]
    simp [openedOf_append]

theorem op_sim_run (H : SimHyp pk tbl T ys targets) {α : Type}
    (oa : OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) α)
    (log : G2Log prims) :
    (simulateQ (findOracles targets)
        ((simulateQ (opImplB optRand pk tbl ys) oa).run log)).run (openedOf pk log) =
      (fun z => (z, openedOf pk z.2)) <$>
        (simulateQ (opImplG optRand pk (fun m R => idealSign vp prims T m pk R)) oa).run log := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [op_sim_step optRand pk tbl ys H]
    simp only [bind_map_left, map_bind]
    exact bind_congr fun z => ih z.1 z.2

end Sim2

/-! ## Table cells of the FORS secrets -/

section Cells

theorem op_secIdx_val (a : Adrs) :
    (secIdx a).val = (a.layer + 2 ^ 32 * (a.tree + 2 ^ 96 * (a.type + 2 ^ 32 *
      (a.word1 + 2 ^ 32 * (a.word2 + 2 ^ 32 * a.word3))))) % 2 ^ 256 := rfl

/-- A `WOTS_PRF` cell with in-range layer and tree is not a `FORS_PRF` cell with in-range layer
and tree. -/
theorem op_secIdx_ne (a b : Adrs) (hal : a.layer < 2 ^ 32) (hat : a.tree < 2 ^ 96)
    (ha : a.type = 5) (hbl : b.layer < 2 ^ 32) (hbt : b.tree < 2 ^ 96) (hb : b.type = 6) :
    secIdx a ≠ secIdx b := by
  intro h
  have h1 := congrArg Fin.val h
  rw [op_secIdx_val, op_secIdx_val, ha, hb] at h1
  generalize a.word1 + 2 ^ 32 * (a.word2 + 2 ^ 32 * a.word3) = ua at h1
  generalize b.word1 + 2 ^ 32 * (b.word2 + 2 ^ 32 * b.word3) = ub at h1
  omega

/-- The packing is injective on addresses whose six fields are in range. -/
theorem op_secIdx_inj (a b : Adrs) (ha : a.isCanonical = true) (hb : b.isCanonical = true)
    (h : secIdx a = secIdx b) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := Adrs.fits_of_isCanonical a ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := Adrs.fits_of_isCanonical b hb
  rw [Adrs.fits_iff] at a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
  have h1 := congrArg Fin.val h
  rw [op_secIdx_val, op_secIdx_val] at h1
  norm_num at a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6
  apply Adrs.ext <;> omega

end Cells

/-! ## Targets, images and cells by ledger position -/

section Index

/-- The table cells of the FORS secrets, in ledger order. -/
def forsSkIdx (vp : ValidatedParams) : List SecIdx :=
  (forsLeafAddresses vp).map fun leaf => secIdx (skOf leaf)

/-- The images of the hidden inputs `xs` under the committed tweaks. -/
def imgsOf (pkSeed : prims.PkSeed) (xs : List prims.Y) : List prims.Y :=
  List.zipWith (fun t x => prims.Thash pkSeed t [x]) (forsLeafKeys vp prims) xs

theorem op_skOf_canonical (hS : Structural vp prims) {leaf : Adrs}
    (h : leaf ∈ forsLeafAddresses vp) :
    (skOf leaf).isCanonical = true ∧ (skOf leaf).layer < 2 ^ 32 ∧ (skOf leaf).tree < 2 ^ 96 := by
  have hc := (addressFacts_forsLeafAddresses vp hS.bounds leaf h).canonical
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := Adrs.fits_of_isCanonical leaf hc
  have b1 := a1
  have b2 := a2
  rw [Adrs.fits_iff] at b1 b2
  refine ⟨?_, by simpa [skOf] using b1, by simpa [skOf] using b2⟩
  rw [Adrs.fits_iff] at a1 a2 a4 a6
  norm_num at a1 a2 a4 a6
  simp [Adrs.isCanonical, skOf, a1, a2, a4, a6, AddrType.toCode, AddrType.ofCode, Adrs.Fits]

theorem forsSkIdx_nodup (hS : Structural vp prims) : (forsSkIdx vp).Nodup := by
  refine List.Nodup.map_on (fun a ha b hb hab => ?_) (forsLeafAddresses_nodup vp)
  have h := op_secIdx_inj _ _ (op_skOf_canonical hS ha).1 (op_skOf_canonical hS hb).1 hab
  have ta := type_of_mem_forsLeafAddresses vp ha
  have tb := type_of_mem_forsLeafAddresses vp hb
  have wa := word2_of_mem_forsLeafAddresses vp ha
  have wb := word2_of_mem_forsLeafAddresses vp hb
  simp only [skOf, Adrs.mk.injEq] at h
  exact Adrs.ext h.1 h.2.1 (ta.trans tb.symm) h.2.2.2.1 (wa.trans wb.symm) h.2.2.2.2.2

theorem forsSkIdx_length : (forsSkIdx vp).length = (forsLeafAddresses vp).length := by
  simp [forsSkIdx]

theorem op_leafTarget_getElem (hS : Structural vp prims) (j : ℕ)
    (hj : j < (forsLeafAddresses vp).length) :
    leafTarget vp prims (forsLeafAddresses vp)[j] = j := by
  unfold leafTarget
  have h : prims.adrsToKey (forsLeafAddresses vp)[j] =
      (forsLeafKeys vp prims)[j]'(by simpa [forsLeafKeys] using hj) := by
    simp [forsLeafKeys]
  rw [h]
  exact (forsLeafKeys_nodup_length hS).1.idxOf_getElem _ _

theorem op_openAns_getElem (hS : Structural vp prims) (xs : List prims.Y)
    (hlen : xs.length = (forsLeafAddresses vp).length) (j : ℕ)
    (hj : j < (forsLeafAddresses vp).length) :
    ((forsLeafKeys vp prims).zip xs)[leafTarget vp prims (forsLeafAddresses vp)[j]]? =
      some (prims.adrsToKey (forsLeafAddresses vp)[j], xs[j]'(hlen ▸ hj)) := by
  rw [op_leafTarget_getElem hS j hj,
    List.getElem?_eq_getElem (by simpa [forsLeafKeys, hlen] using hj)]
  simp [forsLeafKeys]

theorem op_leafImage_getElem (hS : Structural vp prims) (pkSeed : prims.PkSeed)
    (xs : List prims.Y) (hlen : xs.length = (forsLeafAddresses vp).length) (j : ℕ)
    (hj : j < (forsLeafAddresses vp).length) :
    leafImage (vp := vp) (imgsOf (vp := vp) pkSeed xs) (forsLeafAddresses vp)[j] =
      prims.F pkSeed (forsLeafAddresses vp)[j] (xs[j]'(hlen ▸ hj)) := by
  unfold leafImage imgsOf
  rw [op_leafTarget_getElem hS j hj, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa [forsLeafKeys, hlen] using hj)]
  simp [forsLeafKeys]

theorem op_leafTarget_inj (hS : Structural vp prims) {a b : Adrs}
    (ha : a ∈ forsLeafAddresses vp) (hb : b ∈ forsLeafAddresses vp)
    (h : leafTarget vp prims a = leafTarget vp prims b) : a = b := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  rw [op_leafTarget_getElem hS i hi, op_leafTarget_getElem hS j hj] at h
  subst h
  rfl

end Index

/-! ## The game at `bOpenPre` -/

section Game

open TweakableHash TweakableHash.SM_DT_OpenPRE_SourceFinalValidity

theorem op_simHyp (hS : Structural vp prims) (tbl : SecretTable vp prims)
    (pk : PublicKeyCore prims.core) (xs : List prims.Y)
    (hlen : xs.length = (forsSkIdx vp).length) :
    SimHyp pk tbl (Tables.updateList tbl (forsSkIdx vp) xs)
      (imgsOf (vp := vp) pk.pkSeed xs) ((forsLeafKeys vp prims).zip xs) := by
  have hlen' : xs.length = (forsLeafAddresses vp).length := hlen.trans forsSkIdx_length
  have key : ∀ (j : ℕ) (hj : j < (forsLeafAddresses vp).length),
      secretOf vp prims (Tables.updateList tbl (forsSkIdx vp) xs)
        (skOf (forsLeafAddresses vp)[j]) = xs[j]'(hlen' ▸ hj) := by
    intro j hj
    have hj' : j < (forsSkIdx vp).length := by rw [forsSkIdx_length]; exact hj
    have h := Tables.updateList_getElem tbl (forsSkIdx_nodup hS) hlen j hj'
    have e : (forsSkIdx vp)[j] = secIdx (skOf (forsLeafAddresses vp)[j]) := by
      simp [forsSkIdx]
    rw [e] at h
    exact h
  refine ⟨hS.bounds, ?_, ?_, ?_⟩
  · intro a hl ht hty
    show tbl (secIdx a) = Tables.updateList tbl (forsSkIdx vp) xs (secIdx a)
    refine (Tables.updateList_apply_of_not_mem tbl (forsSkIdx vp) xs ?_).symm
    intro hmem
    obtain ⟨leaf, hleaf, heq⟩ := List.mem_map.1 hmem
    have hc := op_skOf_canonical hS hleaf
    exact op_secIdx_ne a (skOf leaf) hl ht hty hc.2.1 hc.2.2 rfl heq.symm
  · intro leaf hleaf
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hleaf
    unfold openAns
    rw [op_openAns_getElem hS xs hlen' j hj, key j hj]
    rfl
  · intro leaf hleaf
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hleaf
    rw [op_leafImage_getElem hS pk.pkSeed xs hlen' j hj, key j hj]

/-- The state after target sampling, as a function of the sampled inputs. -/
def initSt (n : ℕ) : List prims.AdrsKey → List prims.Y → State prims.AdrsKey prims.Y →
    State prims.AdrsKey prims.Y
  | t :: ts, x :: xs, st => initSt n ts xs (st.recordTarget n Prod.fst (t, x))
  | [], _, st => st
  | _ :: _, [], st => st

theorem op_init_run (pkSeed : prims.PkSeed) : ∀ (ts : List prims.AdrsKey)
    (st : State prims.AdrsKey prims.Y),
    (initializeTargets (forsOpenPreProblem vp prims pkSeedDist) pkSeed ts).run st =
      Tables.sampleList prims.Y ts.length >>= fun xs =>
        pure (List.zipWith (fun t x => prims.Thash pkSeed t [x]) ts xs,
          initSt (openPreTargets vp) ts xs st)
  | [], st => by
      simp [initializeTargets, Tables.sampleList, initSt]
  | t :: ts, st => by
      simp only [initializeTargets, Tables.sampleList, List.length_cons, bind_assoc, pure_bind,
        StateT.run_bind]
      simp [op_init_run pkSeed ts, initSt]
      rfl

theorem op_initSt_spec (n : ℕ) : ∀ (ts : List prims.AdrsKey) (xs : List prims.Y)
    (st : State prims.AdrsKey prims.Y), xs.length = ts.length →
    SourceFinalValidity.Invariant n Prod.fst st →
    (initSt n ts xs st).challenges = st.challenges ++ ts.zip xs ∧
      (initSt n ts xs st).collectionTweaks = st.collectionTweaks ∧
      SourceFinalValidity.Invariant n Prod.fst (initSt n ts xs st)
  | [], xs, st, _, hinv => by simp [initSt, hinv]
  | t :: ts, [], st, hlen, _ => by simp at hlen
  | t :: ts, x :: xs, st, hlen, hinv => by
      have ih := op_initSt_spec n ts xs (st.recordTarget n Prod.fst (t, x))
        (by simpa using hlen) (hinv.recordTarget n Prod.fst st (t, x))
      refine ⟨?_, ?_, ih.2.2⟩
      · rw [initSt, ih.1]
        simp [SourceFinalValidity.State.recordTarget]
      · rw [initSt, ih.2.1]
        rfl

theorem op_initSt_initial (hS : Structural vp prims) (xs : List prims.Y)
    (hlen : xs.length = (forsLeafKeys vp prims).length) :
    initSt (openPreTargets vp) (forsLeafKeys vp prims) xs .initial =
      ⟨(forsLeafKeys vp prims).zip xs, [], true⟩ := by
  obtain ⟨h1, h2, h3⟩ := op_initSt_spec (openPreTargets vp) (forsLeafKeys vp prims) xs .initial
    hlen (SourceFinalValidity.invariant_initial _ _)
  have hv : (initSt (openPreTargets vp) (forsLeafKeys vp prims) xs .initial).valid = true := by
    rw [h3, SourceFinalValidity.validBool_eq_true_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      simp [SourceFinalValidity.State.initial, hlen, (forsLeafKeys_nodup_length hS).2]
    · rw [h1]
      simp only [SourceFinalValidity.State.initial, List.nil_append]
      rw [List.map_fst_zip (by rw [hlen])]
      exact (forsLeafKeys_nodup_length hS).1
    · rw [h2]
      simp [SourceFinalValidity.State.initial]
  generalize initSt (openPreTargets vp) (forsLeafKeys vp prims) xs .initial = st at h1 h2 hv
  cases st
  simp only [SourceFinalValidity.State.initial, List.nil_append] at h1 h2 hv
  simp [h1, h2, hv]

/-- The final check of the experiment. -/
def expWin (st : State prims.AdrsKey prims.Y) (pkSeed : prims.PkSeed)
    (r : (ℕ × prims.Y) × List ℕ) : ProbComp Bool :=
  match st.challenges[r.1.1]? with
  | none => return false
  | some (t, x) =>
      return st.valid && decide (r.1.1 ∉ r.2) &&
        decide (prims.Thash pkSeed t [r.1.2] = prims.Thash pkSeed t [x])

theorem op_experiment (hS : Structural vp prims) (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) :
    experiment (bOpenPreWith my A) = pkSeedDist >>= fun pkSeed => my >>= fun tbl =>
      Tables.sampleList prims.Y (forsSkIdx vp).length >>= fun xs =>
        (simulateQ (findOracles
            (initSt (openPreTargets vp) (forsLeafKeys vp prims) xs .initial).challenges)
          ((bOpenPreWith my A).find tbl pkSeed (imgsOf (vp := vp) pkSeed xs))).run [] >>=
        expWin (initSt (openPreTargets vp) (forsLeafKeys vp prims) xs .initial) pkSeed := by
  unfold experiment
  show pkSeedDist >>= _ = _
  refine bind_congr fun pkSeed => ?_
  have hpick : (simulateQ (pickOracles (forsOpenPreProblem vp prims pkSeedDist) pkSeed)
      (bOpenPreWith my A).pick).run .initial =
      my >>= fun tbl => pure ((tbl, forsLeafKeys vp prims), .initial) := by
    simp [bOpenPreWith, pickOracles, QueryImpl.simulateQ_add_liftM_left]
  rw [hpick]
  refine (bind_assoc _ _ _).trans ?_
  refine bind_congr (m := ProbComp) fun tbl => ?_
  refine (pure_bind _ _).trans ?_
  dsimp only
  rw [List.take_of_length_le (by
    rw [(forsLeafKeys_nodup_length hS).2]; exact le_rfl)]
  rw [op_init_run]
  refine (bind_assoc _ _ _).trans ?_
  rw [show (forsLeafKeys vp prims).length = (forsSkIdx vp).length by
    simp [forsLeafKeys, forsSkIdx]]
  refine bind_congr (m := ProbComp) fun xs => ?_
  refine (pure_bind _ _).trans ?_
  refine bind_congr (m := ProbComp) fun r => ?_
  unfold expWin
  dsimp only
  rcases (initSt (openPreTargets vp) (forsLeafKeys vp prims) xs
    SourceFinalValidity.State.initial).challenges[r.1.1]? with _ | ⟨t, x⟩ <;> rfl

/-- The winning condition as a Boolean (on a valid target state). -/
def opWin (ch : List (prims.AdrsKey × prims.Y)) (pkSeed : prims.PkSeed) (jm : ℕ × prims.Y)
    (opened : List ℕ) : Bool :=
  match ch[jm.1]? with
  | none => false
  | some (t, x) =>
      decide (jm.1 ∉ opened) && decide (prims.Thash pkSeed t [jm.2] = prims.Thash pkSeed t [x])

/-- The winning condition of the game at `bOpenPre`, as a function of the `G2` sample
`(PK.seed, table, forgery, transcript)`. -/
def opW (pkSeed : prims.PkSeed) (T : SecretTable vp prims)
    (z : (List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) : Bool :=
  opWin ((forsLeafKeys vp prims).zip ((forsSkIdx vp).map T)) pkSeed
    (openPreAnswer (idealPk vp prims T pkSeed) (imgsOf (vp := vp) pkSeed ((forsSkIdx vp).map T))
      z.2 z.1.1 z.1.2)
    (openedOf (idealPk vp prims T pkSeed) z.2)

theorem op_tail (hS : Structural vp prims) (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed)
    (tbl : SecretTable vp prims) (xs : List prims.Y)
    (hlen : xs.length = (forsSkIdx vp).length) :
    ((simulateQ (findOracles
          (initSt (openPreTargets vp) (forsLeafKeys vp prims) xs .initial).challenges)
        ((bOpenPreWith my A).find tbl pkSeed (imgsOf (vp := vp) pkSeed xs))).run [] >>=
      expWin (initSt (openPreTargets vp) (forsLeafKeys vp prims) xs .initial) pkSeed) =
    g2Run A (Tables.updateList tbl (forsSkIdx vp) xs)
        (idealPk vp prims (Tables.updateList tbl (forsSkIdx vp) xs) pkSeed) >>= fun z =>
      pure (opW pkSeed (Tables.updateList tbl (forsSkIdx vp) xs) z) := by
  have hlenK : xs.length = (forsLeafKeys vp prims).length := by
    rw [hlen]; simp [forsLeafKeys, forsSkIdx]
  rw [op_initSt_initial hS xs hlenK]
  have H := op_simHyp hS tbl (idealPk vp prims tbl pkSeed) xs hlen
  have hpk : idealPk vp prims tbl pkSeed =
      idealPk vp prims (Tables.updateList tbl (forsSkIdx vp) xs) pkSeed := by
    unfold idealPk
    rw [op_idealRoot_congr hS.bounds tbl _ pkSeed H.wots]
  have hxs : (forsSkIdx vp).map (Tables.updateList tbl (forsSkIdx vp) xs) = xs :=
    Tables.map_updateList tbl (forsSkIdx_nodup hS) hlen
  have hsim := op_sim_run optRand (idealPk vp prims tbl pkSeed) tbl
    (imgsOf (vp := vp) pkSeed xs) H (A.main (idealPk vp prims tbl pkSeed)) []
  unfold opW g2Run g2RunWith
  rw [hxs, ← hpk]
  show (simulateQ (findOracles ((forsLeafKeys vp prims).zip xs))
    (runForgerLog A (idealPk vp prims tbl pkSeed) lazyRandomizerLift
      (openSign (idealPk vp prims tbl pkSeed) tbl (imgsOf (vp := vp) pkSeed xs)) >>= fun z =>
      pure (openPreAnswer (idealPk vp prims tbl pkSeed) (imgsOf (vp := vp) pkSeed xs)
        z.2 z.1.1 z.1.2))).run [] >>= _ = _
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc,
    pure_bind]
  unfold runForgerLog
  erw [hsim]
  simp only [bind_map_left]
  refine bind_congr (m := ProbComp) fun z => ?_
  unfold expWin opWin
  dsimp only
  rcases ((forsLeafKeys vp prims).zip xs)[(openPreAnswer (idealPk vp prims tbl pkSeed)
    (imgsOf (vp := vp) pkSeed xs) z.2 z.1.1 z.1.2).1]? with _ | ⟨t, x⟩
  · rfl
  · simp

end Game

/-! ## The deterministic core: a forgery of class `openpre` wins -/

section Win

theorem op_forsNode_inj (p1 p2 : DigestParts vp.params) (i1 i2 : ℕ)
    (h : forsNodeAdrs p1.forsAdrs 0 i1 = forsNodeAdrs p2.forsAdrs 0 i2) :
    p1.forsAdrs = p2.forsAdrs ∧ i1 = i2 := by
  simp only [forsNodeAdrs, DigestParts.forsAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
    Adrs.setTreeHeight, Adrs.setTreeIndex, Adrs.setTreeAddress, Adrs.getKeyPairAddress, Adrs.zero,
    Adrs.mk.injEq] at h ⊢
  tauto

theorem op_answer_spec (pk : PublicKeyCore prims.core) (ys : List prims.Y) (log : G2Log prims)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) (i0 : Fin vp.params.k)
    (h0 : (((digestParts pk sig.randomness msg : DigestParts vp.params).forsAdrs,
        leafIndex (digestParts pk sig.randomness msg : DigestParts vp.params) i0) ∉
          openedLeaves pk (G2Log.signed log)) ∧
      prims.F pk.pkSeed (forsNodeAdrs (digestParts pk sig.randomness msg :
          DigestParts vp.params).forsAdrs 0
          (leafIndex (digestParts pk sig.randomness msg : DigestParts vp.params) i0))
        (sig.fors[i0.val]).sk =
        leafImage (vp := vp) ys (forsNodeAdrs (digestParts pk sig.randomness msg :
          DigestParts vp.params).forsAdrs 0
          (leafIndex (digestParts pk sig.randomness msg : DigestParts vp.params) i0))) :
    ∃ i : Fin vp.params.k,
      ((((digestParts pk sig.randomness msg : DigestParts vp.params).forsAdrs,
        leafIndex (digestParts pk sig.randomness msg : DigestParts vp.params) i) ∉
          openedLeaves pk (G2Log.signed log)) ∧
      prims.F pk.pkSeed (forsNodeAdrs (digestParts pk sig.randomness msg :
          DigestParts vp.params).forsAdrs 0
          (leafIndex (digestParts pk sig.randomness msg : DigestParts vp.params) i))
        (sig.fors[i.val]).sk =
        leafImage (vp := vp) ys (forsNodeAdrs (digestParts pk sig.randomness msg :
          DigestParts vp.params).forsAdrs 0
          (leafIndex (digestParts pk sig.randomness msg : DigestParts vp.params) i))) ∧
      openPreAnswer pk ys log msg sig =
        (leafTarget vp prims (forsNodeAdrs (digestParts pk sig.randomness msg :
          DigestParts vp.params).forsAdrs 0
          (leafIndex (digestParts pk sig.randomness msg : DigestParts vp.params) i)),
          (sig.fors[i.val]).sk) := by
  unfold openPreAnswer
  dsimp only
  generalize hfs : (List.finRange vp.params.k).findSome? _ = r
  rcases r with _ | ans
  · rw [List.findSome?_eq_none_iff] at hfs
    have := hfs i0 (List.mem_finRange _)
    rw [if_pos h0] at this
    exact absurd this (by simp)
  · obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some hfs
    split_ifs at hi with hPi
    refine ⟨i, hPi, ?_⟩
    rw [← Option.some.inj hi]
    rfl

theorem op_win (hS : Structural vp prims) (pkSeed : prims.PkSeed) (T : SecretTable vp prims)
    (z : (List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims)
    (h : g2ClassOf T (idealPk vp prims T pkSeed) z.2 z.1.1 z.1.2 = .openpre) :
    opW pkSeed T z = true := by
  obtain ⟨⟨msg, sig⟩, log⟩ := z
  dsimp only at h
  have hxl : ((forsSkIdx vp).map T).length = (forsLeafAddresses vp).length := by
    simp [forsSkIdx]
  have hch : ∀ leaf ∈ forsLeafAddresses vp,
      ((forsLeafKeys vp prims).zip ((forsSkIdx vp).map T))[leafTarget vp prims leaf]? =
        some (prims.adrsToKey leaf, secretOf vp prims T (skOf leaf)) := by
    intro leaf hl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    rw [op_openAns_getElem hS _ hxl j hj]
    simp [forsSkIdx, secretOf]
  have himg : ∀ leaf ∈ forsLeafAddresses vp,
      leafImage (vp := vp) (imgsOf (vp := vp) pkSeed ((forsSkIdx vp).map T)) leaf =
        prims.F pkSeed leaf (secretOf vp prims T (skOf leaf)) := by
    intro leaf hl
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    rw [op_leafImage_getElem hS pkSeed _ hxl j hj]
    simp [forsSkIdx, secretOf]
  have hmem : ∀ (parts : DigestParts vp.params) (i : Fin vp.params.k),
      forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i) ∈ forsLeafAddresses vp :=
    fun parts i => op_leaf_mem parts _ (op_leafIndex_lt parts i)
  have hopen : (openTree? (idealPk vp prims T pkSeed)
      (digestParts (idealPk vp prims T pkSeed) sig.randomness msg)
      (openedLeaves (idealPk vp prims T pkSeed) (G2Log.signed log)) sig
      (idealSign vp prims T msg (idealPk vp prims T pkSeed) sig.randomness)).isSome = true := by
    unfold g2ClassOf classify at h
    dsimp only at h
    split_ifs at h with h1 h2 h3
    exact h3
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hopen
  have hP := List.find?_some hi
  simp only [decide_eq_true_eq] at hP
  have hsk : ((idealSign vp prims T msg (idealPk vp prims T pkSeed) sig.randomness).fors[i.val]).sk =
      secretOf vp prims T (skOf (forsNodeAdrs
        (digestParts (idealPk vp prims T pkSeed) sig.randomness msg : DigestParts vp.params).forsAdrs
        0 (leafIndex (digestParts (idealPk vp prims T pkSeed) sig.randomness msg) i))) := by
    rw [op_idealSign_eq]
    exact opFors_sk _ _ _ _ _ i.isLt
  obtain ⟨i', hP', hans⟩ := op_answer_spec (idealPk vp prims T pkSeed)
    (imgsOf (vp := vp) pkSeed ((forsSkIdx vp).map T)) log msg sig i
    ⟨hP.1, by rw [himg _ (hmem _ i), ← hsk]; exact hP.2⟩
  unfold opW
  dsimp only
  rw [hans]
  unfold opWin
  dsimp only
  rw [hch _ (hmem _ i')]
  dsimp only
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun hin => ?_, ?_⟩
  · unfold openedOf at hin
    rw [List.mem_flatMap] at hin
    obtain ⟨e, he, hin⟩ := hin
    unfold openIdx at hin
    rw [List.mem_map] at hin
    obtain ⟨i'', -, heq⟩ := hin
    have hleaf := op_leafTarget_inj hS (hmem _ i'') (hmem _ i') heq
    obtain ⟨hfa, hidx⟩ := op_forsNode_inj _ _ _ _ hleaf
    apply hP'.1
    unfold openedLeaves G2Log.signed
    rw [List.mem_flatMap]
    refine ⟨(e.1, e.2.2), List.mem_map.2 ⟨e, he, rfl⟩, ?_⟩
    unfold forsIndices
    rw [List.mem_map]
    refine ⟨i''.val, List.mem_range.2 i''.isLt, ?_⟩
    rw [← hfa, ← hidx]
    rfl
  · have h2 := hP'.2
    rw [himg _ (hmem _ i')] at h2
    exact h2

end Win

/-! ## Step 5 -/

/-- Step 5 for an abstract table sampler `my` with the coordinate-extraction property. -/
theorem op_main (hS : Structural vp prims) (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist)
    (hmy : ∀ f : SecretTable vp prims → ProbComp Bool,
      prTrue (my >>= fun tbl => Tables.sampleList prims.Y (forsSkIdx vp).length >>= fun xs =>
        f (Tables.updateList tbl (forsSkIdx vp) xs)) = prTrue (my >>= f)) :
    prTrue (pkSeedDist >>= fun pkSeed => my >>= fun tbl =>
      g2Run A tbl (idealPk vp prims tbl pkSeed) >>= fun z =>
        pure (g2Valid (idealPk vp prims tbl pkSeed) z.2 z.1.1 z.1.2 &&
          decide (g2ClassOf tbl (idealPk vp prims tbl pkSeed) z.2 z.1.1 z.1.2 = .openpre))) ≤
      prTrue (TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.experiment (bOpenPreWith my A)) := by
  rw [op_experiment hS my A]
  refine le_trans (prTrue_bind_mono _ _ _ fun pkSeed _ => prTrue_bind_mono my _ _ fun tbl _ =>
    prTrue_bind_pure_mono _ _ (opW pkSeed tbl) fun z _ h =>
      op_win hS pkSeed tbl z (by simpa using (Bool.and_eq_true_iff.1 h).2)) ?_
  refine le_of_eq (prTrue_bind_congr _ _ _ fun pkSeed _ => ?_)
  refine (hmy (fun T => g2Run A T (idealPk vp prims T pkSeed) >>= fun z =>
    pure (opW pkSeed T z))).symm.trans ?_
  refine prTrue_bind_congr my _ _ fun tbl _ => prTrue_bind_congr _ _ _ fun xs hxs => ?_
  rw [op_tail hS my A pkSeed tbl xs (Tables.length_of_mem_support_sampleList hxs)]

/-- **Step 5.** -/
theorem stepOpenPRE (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    StepOpenPRE A (bOpenPre A) := by
  unfold StepOpenPRE
  exact op_main hS (sampleTable vp prims) A (fun f =>
    prTrue_congr (evalDist_sampleTable_extract_list (forsSkIdx_nodup hS) (fun _ => f)))

end Reduction

#print axioms Reduction.forsLeafKeys_nodup_length
#print axioms Reduction.idealRoot_congr
#print axioms Reduction.forsSigFromImages_auth
#print axioms Reduction.stepOpenPRE
