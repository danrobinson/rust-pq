/-
Work package OPEN, items R3 / R7 for the WOTS adversaries (second phases only).

The second phases of `rUd pkSeedDist (Lazy.bWotsS A)`, `rPre pkSeedDist (Lazy.bWotsS A)`,
`rTcrT pkSeedDist (Lazy.bWotsS A)` as `tblImpl`-interpretations of open programs in which EVERY
`Thash` / `H_msg` evaluation is a hash-kind oracle query, including the `wotsAnswer` tail that
`Resources2Wots` kept as a pure function.

* `wotsAnswerOpen hist pk msg sig` — the tail, memoised (each layer's chain ends and the next
  layer message are computed once, in one pass per signature); `wotsAnswerOpen_tbl`;
  `wotsAnswerOpen_kindBound`; `wotsAnswerHashes vp` (`= 129714` at 128s).
* `wotsUdOpenAll`, `wotsPreOpenAll`, `wotsTcrOpenAll` — forge + tail + the wrapper's chain
  completions; `wotsUd_phase2_open_eq` etc.: the second phase EQUALS the interpretation, with no
  post-processing at all.  `*_hashfree`: the open programs do not depend on `Thash` / `H_msg`
  (invariance under `withTH prims T H`, by `rfl`).
* `wotsUd_phase2_open_hashes` etc. and the 128s numerals.
-/
import Reduction.Open.WithHash
import Reduction.Resources2Wots
import Reduction.TightCapsHeadline

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Open

open Resources2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {ι : Type} {gspec : OracleSpec ι}

attribute [local instance] Lazy.openQ Lazy.closedQ

/-! ## 1. Generic transfer: hash-polymorphic programs under the table -/

/-- A program that is natural for the two hash-preserving morphisms (table interpretation of the
open program, evaluation of the free program) is interpreted as the `pure` evaluation by
`prims`. -/
theorem tbl_of_natural {α : Type} (tbl : SecretTable vp prims)
    (xo : OracleComp (Lazy.OSpec prims gspec) α) (xc : OracleComp (unifSpec + gspec) α)
    (xf : OracleComp (publicHashSpec prims.core) α)
    (h1 : (Lazy.tblHom (gspec := gspec) tbl).toMonadHom xo = xc)
    (h2 : (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
      (m := OracleComp (unifSpec + gspec))).toMonadHom xf = xc) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) xo =
      pure (simulateQ (PublicHash.impl prims) xf) := by
  rw [Lazy.free_apply] at h2
  exact h1.trans h2.symm

theorem forsPkO_tbl (tbl : SecretTable vp prims) (sig : ForsSigCore vp.params prims.core)
    (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (forsPkFromSigM prims.core sig md pk adrs) = pure (forsPkFromSig prims sig md pk adrs) :=
  tbl_of_natural tbl _ _ _
    (forsPkFromSigM_natural prims.core (Lazy.tblHom (gspec := gspec) tbl) sig md pk adrs)
    (forsPkFromSigM_natural prims.core
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
        (m := OracleComp (unifSpec + gspec))) sig md pk adrs)

/-! ## 2. One hypertree layer: chain ends and recovered root in one pass -/

/-- One layer of hypertree verification returning BOTH the recovered WOTS+ chain ends and the
recovered XMSS root (the chains are completed once). -/
def layerStepM (core : CorePrimitives vp.params) {m : Type → Type} [Monad m]
    [HasQuery (publicHashSpec core) m] (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ)
    (sig : XmssSig vp.params core) (msg : core.Y) : m (Vector core.Y vp.params.len × core.Y) := do
  let tops ← wotsPkFromSigTopsM core sig.wots msg pk (wotsLeafAdrs adrs idx)
  let leaf ← PublicHash.tl core pk (wotsPkAdrs (wotsLeafAdrs adrs idx)) tops.toList
  let root ← PerfectMerkleTree.climbM (xmssNodeHashM core pk adrs) idx leaf sig.auth.toList
  pure (tops, root)

theorem layerStepM_natural (core : CorePrimitives vp.params) {m n : Type → Type} [Monad m]
    [LawfulMonad m] [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n] (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) (sig : XmssSig vp.params core) (msg : core.Y) :
    F.toMonadHom (layerStepM core pk adrs idx sig msg) = layerStepM core pk adrs idx sig msg := by
  unfold layerStepM
  rw [MonadHom.mmap_bind, wotsPkFromSigTopsM_natural core F]
  refine bind_congr fun tops => ?_
  rw [MonadHom.mmap_bind, PublicHash.tl_natural core F]
  refine bind_congr fun leaf => ?_
  rw [MonadHom.mmap_bind, PerfectMerkleTree.climbM_natural F.toMonadHom _
    (xmssNodeHashM core pk adrs) (fun z t l r => xmssNodeHashM_natural core F pk adrs z t l r)]
  refine bind_congr fun root => ?_
  exact MonadHom.mmap_pure _ _

theorem layerStepM_impl (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ)
    (sig : XmssSig vp.params prims.core) (msg : prims.Y) :
    simulateQ (PublicHash.impl prims)
      (layerStepM prims.core pk adrs idx sig msg :
        OracleComp (publicHashSpec prims.core) (Vector prims.Y vp.params.len × prims.Y)) =
      (wotsPkFromSigTops prims sig.wots msg pk (wotsLeafAdrs adrs idx),
        xmssPkFromSig prims idx sig msg pk adrs) := by
  rw [xmssPkFromSig_eq_climb, wotsPkFromSig_eq_tl]
  unfold layerStepM
  simp only [simulateQ_bind, simulateQ_pure, PerfectMerkleTree.simulateQ_climbM]
  rfl

theorem layerStepO_tbl (tbl : SecretTable vp prims) (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ)
    (sig : XmssSig vp.params prims.core) (msg : prims.Y) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (layerStepM prims.core pk adrs idx sig msg) =
      pure (wotsPkFromSigTops prims sig.wots msg pk (wotsLeafAdrs adrs idx),
        xmssPkFromSig prims idx sig msg pk adrs) := by
  rw [← layerStepM_impl]
  exact tbl_of_natural tbl _ _ _
    (layerStepM_natural prims.core (Lazy.tblHom (gspec := gspec) tbl) pk adrs idx sig msg)
    (layerStepM_natural prims.core
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
        (m := OracleComp (unifSpec + gspec))) pk adrs idx sig msg)

/-- Budget of one layer step, `c` per hash evaluation: `len` chains of at most `w - 1` steps,
one `T_len`, `h'` node hashes. -/
def layerStepB (vp : ValidatedParams) (c : ℕ) : ℕ :=
  vp.params.len * ((vp.params.w - 1) * c) + c + vp.params.hp * c

theorem layerStepO_kindBound (K : Lazy.Kind) (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ)
    (sig : XmssSig vp.params prims.core) (msg : prims.Y) :
    IsQueryBoundP (layerStepM prims.core pk adrs idx sig msg :
        OracleComp (Lazy.OSpec prims gspec) (Vector prims.Y vp.params.len × prims.Y))
      (fun t => Lazy.kind t = K) (layerStepB vp (Lazy.ind K .hash)) := by
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsQueryBoundP (PublicHash.tl prims.core pk a ys :
      OracleComp (Lazy.OSpec prims gspec) prims.Y) (fun t => Lazy.kind t = K)
        (Lazy.ind K .hash) :=
    fun _ _ => Lazy.query_kindBound K _
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pk a l r :
      OracleComp (Lazy.OSpec prims gspec) prims.Y) (fun t => Lazy.kind t = K)
        (Lazy.ind K .hash) :=
    fun _ _ _ => Lazy.query_kindBound K _
  have hc : ∀ leaf, IsQueryBoundP (PerfectMerkleTree.climbM
      (xmssNodeHashWith (PublicHash.h prims.core pk) adrs) idx leaf sig.auth.toList :
        OracleComp (Lazy.OSpec prims gspec) prims.Y) (fun t => Lazy.kind t = K)
      (vp.params.hp * Lazy.ind K .hash) := fun leaf => by
    have h := Lazy.qb_climb (fun t => Lazy.kind t = K)
      (xmssNodeHashWith (PublicHash.h prims.core pk) adrs :
        ℕ → ℕ → prims.Y → prims.Y → OracleComp (Lazy.OSpec prims gspec) prims.Y)
      (Lazy.ind K .hash) (fun h i l r => hh _ l r) idx leaf sig.auth.toList
    rwa [Vector.length_toList] at h
  unfold layerStepM
  refine (Lazy.qb_bind _
    (Lazy.qb_ofFnM _ _ ((vp.params.w - 1) * Lazy.ind K .hash) fun i =>
      (Lazy.qb_chain _ prims.core _ (fun _ _ => Lazy.query_kindBound K _) _ _ _ _).mono
        (Nat.mul_le_mul_right _ (Nat.sub_le _ _))) fun tops =>
    Lazy.qb_bind _ (htl _ _) fun leaf =>
    Lazy.qb_bind _ (m := 0) (hc leaf) fun root => isQueryBoundP_pure _ _ _).mono ?_
  unfold layerStepB
  omega

/-! ## 3. The memoised layer trace -/

/-- The pairs `(layer message, recovered chain ends)` of layers `j < min n d`, and the layer
message `n`, computed in one pass (`n` layer steps). -/
def layerTraceM (core : CorePrimitives vp.params) {m : Type → Type} [Monad m]
    [HasQuery (publicHashSpec core) m] (pkSeed : core.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params core) (m0 : core.Y) :
    ℕ → m (List (core.Y × Vector core.Y vp.params.len) × core.Y)
  | 0 => pure ([], m0)
  | n + 1 => do
    let r ← layerTraceM core pkSeed parts s m0 n
    if h : n < vp.params.d then do
      let x ← layerStepM core pkSeed (LayerPosition.atLayer vp parts ⟨n, h⟩).toAdrs
        (LayerPosition.atLayer vp parts ⟨n, h⟩).leaf.val s[n] r.2
      pure (r.1 ++ [(r.2, x.1)], x.2)
    else pure r

/-- `layerTraceM` as an open program (every hash evaluation a query). -/
abbrev layerTraceO (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (n : ℕ) :
    OracleComp (Lazy.OSpec prims gspec)
      (List (prims.Y × Vector prims.Y vp.params.len) × prims.Y) :=
  layerTraceM prims.core pkSeed parts s m0 n

/-- The list `[(layerMsg j, layerTops j) | j < min n d]`. -/
def layerList (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) :
    ℕ → List (prims.Y × Vector prims.Y vp.params.len)
  | 0 => []
  | n + 1 =>
    if h : n < vp.params.d then
      layerList pkSeed parts s m0 n ++
        [(layerMsg pkSeed parts s m0 n, layerTops pkSeed parts s m0 ⟨n, h⟩)]
    else layerList pkSeed parts s m0 n

set_option linter.deprecated false in
theorem layerTraceO_tbl (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed)
    (parts : DigestParts vp.params) (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (n : ℕ) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (layerTraceO pkSeed parts s m0 n) =
      pure (layerList pkSeed parts s m0 n, layerMsg pkSeed parts s m0 n) := by
  induction n with
  | zero => simp [layerTraceM, layerList, layerMsg]
  | succ n ih =>
    unfold layerTraceO at ih ⊢
    rw [layerTraceM, simulateQ_bind, ih, pure_bind]
    by_cases h : n < vp.params.d
    · rw [dif_pos h, simulateQ_bind, layerStepO_tbl, pure_bind, simulateQ_pure, layerList,
        dif_pos h, layerMsg, dif_pos h]
      rfl
    · rw [dif_neg h, simulateQ_pure, layerList, dif_neg h, layerMsg, dif_neg h]

theorem layerList_length (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (n : ℕ) :
    (layerList pkSeed parts s m0 n).length = min n vp.params.d := by
  induction n with
  | zero => simp [layerList]
  | succ n ih =>
    rw [layerList]
    split_ifs with h
    · rw [List.length_append, List.length_singleton, ih]; omega
    · rw [ih]; omega

theorem layerList_get (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (n : ℕ) (j : Fin vp.params.d)
    (hj : j.val < n) :
    (layerList pkSeed parts s m0 n)[j.val]? =
      some (layerMsg pkSeed parts s m0 j.val, layerTops pkSeed parts s m0 j) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [layerList]
    split_ifs with h
    · by_cases hjn : j.val < n
      · rw [List.getElem?_append_left (by rw [layerList_length]; omega)]
        exact ih hjn
      · have hjeq : j = ⟨n, h⟩ := Fin.ext (by simp only; omega)
        subst hjeq
        rw [List.getElem?_append_right (by rw [layerList_length]; simp only; omega)]
        simp [layerList_length, Nat.min_eq_left (le_of_lt h)]
    · exact ih (by have := j.isLt; omega)

theorem layerTraceO_kindBound (K : Lazy.Kind) (pkSeed : prims.PkSeed)
    (parts : DigestParts vp.params) (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (n : ℕ) :
    IsQueryBoundP (layerTraceO (gspec := gspec) pkSeed parts s m0 n) (fun t => Lazy.kind t = K)
      (n * layerStepB vp (Lazy.ind K .hash)) := by
  induction n with
  | zero => exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  | succ n ih =>
    unfold layerTraceO at ih ⊢
    rw [layerTraceM]
    refine (Lazy.qb_bind _ ih fun r => ?_).mono (le_of_eq (Nat.succ_mul _ _).symm)
    split_ifs with h
    · exact Lazy.qb_bind _ (m := 0) (layerStepO_kindBound K _ _ _ _ _) fun x =>
        isQueryBoundP_pure _ _ _
    · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)

/-! ## 4. The `wotsAnswer` tail as an open program -/

/-- The hash-free end of `wotsAnswer`: from the two layer traces (forged, reference) find the
first layer with different messages and equal chain ends, and return the WOTS-game answer.
No `Thash` / `H_msg` evaluation (comparisons and list lookups only). -/
def wotsAnswerOf (hist : List (WotsGame.Entry prims)) (parts : DigestParts vp.params)
    (sig : GeneralScheme.SignatureCore vp prims.core)
    (fl rl : List (prims.Y × Vector prims.Y vp.params.len)) :
    ℕ × prims.Y × WotsSig vp.params prims.core :=
  match (List.finRange vp.params.d).find? fun j =>
      decide ((fl.getD j.val (default, Vector.replicate vp.params.len default)).1 ≠
          (rl.getD j.val (default, Vector.replicate vp.params.len default)).1 ∧
        (fl.getD j.val (default, Vector.replicate vp.params.len default)).2 =
          (rl.getD j.val (default, Vector.replicate vp.params.len default)).2) with
  | none => (0, default, Vector.replicate vp.params.len default)
  | some j =>
    (hist.findIdx (fun e => decide (e.1 = layerWotsAdrs parts j)),
      (fl.getD j.val (default, Vector.replicate vp.params.len default)).1,
      (sig.hypertree[j.val]).wots)

theorem wotsAnswerOf_eq (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    wotsAnswerOf hist (digestParts pk sig.randomness msg) sig
      (layerList pk.pkSeed (digestParts pk sig.randomness msg) sig.hypertree
        (forsPkFromSig prims sig.fors (digestParts pk sig.randomness msg).md.toList pk.pkSeed
          (digestParts pk sig.randomness msg).forsAdrs) vp.params.d)
      (layerList pk.pkSeed (digestParts pk sig.randomness msg)
        (signFromHist tbl hist pk msg sig.randomness).hypertree
        (forsPkFromSig prims (signFromHist tbl hist pk msg sig.randomness).fors
          (digestParts pk sig.randomness msg).md.toList pk.pkSeed
          (digestParts pk sig.randomness msg).forsAdrs) vp.params.d) =
      wotsAnswer tbl hist pk msg sig := by
  have key : ∀ (parts : DigestParts vp.params) (s : HtSigCore vp.params prims.core) (m0 : prims.Y)
      (j : Fin vp.params.d),
      (layerList pk.pkSeed parts s m0 vp.params.d).getD j.val
        (default, Vector.replicate vp.params.len default) =
      (layerMsg pk.pkSeed parts s m0 j.val, layerTops pk.pkSeed parts s m0 j) := fun parts s m0 j => by
    rw [List.getD_eq_getElem?_getD, layerList_get pk.pkSeed parts s m0 _ j j.isLt]
    rfl
  unfold wotsAnswerOf wotsAnswer wotsLayer?
  simp only [key]
  rfl

/-- **The `wotsAnswer` tail as an open program.**  `H_msg` of the forgery is a hash query; the
reference signature is recomputed by the open signer `wotsSignFromHistO` (hash queries and
secret reads); the two FORS public keys are recovered by `F`/`H`/`T_k` queries; the two
hypertree verifications are done layer by layer (`layerTraceO`: every chain step, `T_len` and
node hash a query, each layer's chains completed once); the rest (`wotsAnswerOf`) is
comparisons.  The table is not an argument: it is read through the secret oracle. -/
def wotsAnswerOpen (hist : List (WotsGame.Entry prims)) (pk : PublicKeyCore prims.core)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × prims.Y × WotsSig vp.params prims.core) := do
  let digest ← PublicHash.hmsg prims.core sig.randomness pk.pkSeed pk.pkRoot msg
  let ref ← wotsSignFromHistO hist pk msg sig.randomness
  let fm0 ← forsPkFromSigM prims.core sig.fors (splitDigest vp.params digest).md.toList pk.pkSeed
    (splitDigest vp.params digest).forsAdrs
  let hm0 ← forsPkFromSigM prims.core ref.fors (splitDigest vp.params digest).md.toList pk.pkSeed
    (splitDigest vp.params digest).forsAdrs
  let fl ← layerTraceO pk.pkSeed (splitDigest vp.params digest) sig.hypertree fm0 vp.params.d
  let rl ← layerTraceO pk.pkSeed (splitDigest vp.params digest) ref.hypertree hm0 vp.params.d
  pure (wotsAnswerOf hist (splitDigest vp.params digest) sig fl.1 rl.1)

/-- **R3, interpretation of the tail**: under the table, `wotsAnswerOpen` is `wotsAnswer`. -/
theorem wotsAnswerOpen_tbl (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsAnswerOpen hist pk msg sig) =
      pure (wotsAnswer tbl hist pk msg sig) := by
  have hm : simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (PublicHash.hmsg prims.core sig.randomness pk.pkSeed pk.pkRoot msg) =
      pure (prims.Hmsg sig.randomness pk.pkSeed pk.pkRoot msg) :=
    (Lazy.tblHom (gspec := gspec) tbl).map_query' _
  unfold wotsAnswerOpen
  rw [simulateQ_bind, hm, pure_bind, simulateQ_bind, wotsSignFromHistO_tbl, pure_bind,
    simulateQ_bind, forsPkO_tbl, pure_bind, simulateQ_bind, forsPkO_tbl, pure_bind,
    simulateQ_bind, layerTraceO_tbl, pure_bind, simulateQ_bind, layerTraceO_tbl, pure_bind,
    simulateQ_pure]
  exact congrArg pure (wotsAnswerOf_eq tbl hist pk msg sig)

/-- Budget of `wotsAnswerOpen`: `cS` per secret read, `c` per hash evaluation. -/
def wotsAnswerB (vp : ValidatedParams) (cS c : ℕ) : ℕ :=
  c + wotsSignHistB vp cS c + 2 * (vp.params.k * (c + vp.params.a * c) + c) +
    2 * (vp.params.d * layerStepB vp c)

theorem wotsAnswerOpen_kindBound (K : Lazy.Kind) (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    IsQueryBoundP (wotsAnswerOpen (gspec := gspec) hist pk msg sig) (fun t => Lazy.kind t = K)
      (wotsAnswerB vp (Lazy.ind K .sec) (Lazy.ind K .hash)) := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pk.pkSeed a y :
      OracleComp (Lazy.OSpec prims gspec) prims.Y) (fun t => Lazy.kind t = K)
        (Lazy.ind K .hash) :=
    fun _ _ => Lazy.query_kindBound K _
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsQueryBoundP (PublicHash.tl prims.core pk.pkSeed a ys :
      OracleComp (Lazy.OSpec prims gspec) prims.Y) (fun t => Lazy.kind t = K)
        (Lazy.ind K .hash) :=
    fun _ _ => Lazy.query_kindBound K _
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pk.pkSeed a l r :
      OracleComp (Lazy.OSpec prims gspec) prims.Y) (fun t => Lazy.kind t = K)
        (Lazy.ind K .hash) :=
    fun _ _ _ => Lazy.query_kindBound K _
  have hm : IsQueryBoundP (PublicHash.hmsg prims.core sig.randomness pk.pkSeed pk.pkRoot msg :
      OracleComp (Lazy.OSpec prims gspec) _) (fun t => Lazy.kind t = K) (Lazy.ind K .hash) :=
    Lazy.query_kindBound K _
  unfold wotsAnswerOpen
  refine (Lazy.qb_bind _ hm fun digest =>
    Lazy.qb_bind _ (wotsSignFromHistO_kindBound (gspec := gspec) K hist pk msg sig.randomness)
      fun ref =>
    Lazy.qb_bind _ (Lazy.qb_forsPk _ prims.core _ _ _ hf htl hh _ _ _) fun fm0 =>
    Lazy.qb_bind _ (Lazy.qb_forsPk _ prims.core _ _ _ hf htl hh _ _ _) fun hm0 =>
    Lazy.qb_bind _ (layerTraceO_kindBound K _ _ _ _ _) fun fl =>
    Lazy.qb_bind _ (m := 0) (layerTraceO_kindBound K _ _ _ _ _) fun rl =>
      isQueryBoundP_pure _ _ _).mono ?_
  unfold wotsAnswerB
  omega

/-- Hash evaluations of the (memoised) `wotsAnswer` tail: one `H_msg`, one history-based
signature, two FORS public-key recoveries, two hypertree verifications. -/
def wotsAnswerHashes (vp : ValidatedParams) : ℕ :=
  1 + wotsSignHistHashes vp + 2 * (vp.params.k * (1 + vp.params.a) + 1) +
    2 * (vp.params.d * (vp.params.len * (vp.params.w - 1) + 1 + vp.params.hp))

theorem wotsAnswerB_hash : wotsAnswerB vp 0 1 ≤ wotsAnswerHashes vp := by
  have h := wotsSignHistB_hash (vp := vp)
  unfold wotsAnswerB wotsAnswerHashes layerStepB
  simp only [Nat.mul_one]
  omega

theorem wotsAnswerB_sec : wotsAnswerB vp 1 0 ≤ vp.params.k * 2 ^ vp.params.a := by
  have h := wotsSignHistB_sec (vp := vp)
  unfold wotsAnswerB layerStepB
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  omega

theorem wotsAnswerB_game : wotsAnswerB vp 0 0 = 0 := by
  simp [wotsAnswerB, layerStepB, wotsSignHistB_game]

/-- **R3, hash-kind bound of the tail.** -/
theorem wotsAnswerOpen_hashes (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    IsQueryBoundP (wotsAnswerOpen (gspec := gspec) hist pk msg sig)
      (fun t => Lazy.kind t = .hash) (wotsAnswerHashes vp) :=
  (wotsAnswerOpen_kindBound .hash hist pk msg sig).mono
    (by simpa [Lazy.ind] using wotsAnswerB_hash (vp := vp))

theorem wotsAnswerHashes_128s : wotsAnswerHashes Link.vp = 129714 := by decide

/-! ## 5. The complete open second phases -/

/-- The complete second phase: run the forger (`wotsForgeOpen`), extract the WOTS-game answer
(`wotsAnswerOpen`), continue with the wrapper's open tail. -/
noncomputable def wotsPhase2All (A : Forger vp prims optRand pkSeedDist)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β) :
    OracleComp (Lazy.OSpec prims gspec) β :=
  wotsForgeOpen A hist root pk >>= fun r =>
    wotsAnswerOpen hist ⟨pk, root⟩ r.1.1 r.1.2 >>= tail

theorem wotsPhase2All_tbl (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β)
    (tailP : ℕ × prims.Y × WotsSig vp.params prims.core → β)
    (h : ∀ x, simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) (tail x) =
      pure (tailP x)) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2All A hist root pk tail) =
      (liftM ((Lazy.bWotsWith my A).forge (tbl, hist, root) pk >>= fun x => pure (tailP x)) :
        OracleComp (unifSpec + gspec) β) := by
  unfold wotsPhase2All
  rw [simulateQ_bind, wotsForgeOpen_tbl, wots_bWotsWith_forge_eq, bind_assoc, liftM_bind]
  refine bind_congr fun r => ?_
  rw [simulateQ_bind, wotsAnswerOpen_tbl, pure_bind, h, pure_bind]
  rfl

theorem wotsPhase2All_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Lazy.Kind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β)
    (c : ℕ) (htail : ∀ x, IsQueryBoundP (tail x) (fun t => Lazy.kind t = K) c) :
    IsQueryBoundP (wotsPhase2All A hist root pk tail) (fun t => Lazy.kind t = K)
      (qs * wotsSignHistB vp (Lazy.ind K .sec) (Lazy.ind K .hash) +
        (wotsAnswerB vp (Lazy.ind K .sec) (Lazy.ind K .hash) + c)) :=
  Lazy.qb_bind _ (wotsForgeOpen_kindBound A K hK qs hA hist root pk) fun r =>
    Lazy.qb_bind _ (wotsAnswerOpen_kindBound K hist ⟨pk, root⟩ r.1.1 r.1.2) htail

/-- The complete open second phase of `rUd pkSeedDist (Lazy.bWotsS A)`. -/
noncomputable def wotsUdOpenAll (A : Forger vp prims optRand pkSeedDist)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec) Bool :=
  wotsPhase2All A hist root pk fun x => wotsWinO pk hist2 x.1 x.2.1 x.2.2

/-- The complete open second phase of `rPre pkSeedDist (Lazy.bWotsS A)`. -/
noncomputable def wotsPreOpenAll (A : Forger vp prims optRand pkSeedDist)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × prims.Y) :=
  wotsPhase2All A hist root pk fun x => wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2

/-- The complete open second phase of `rTcr(T) pkSeedDist (Lazy.bWotsS A)`. -/
noncomputable def wotsTcrOpenAll (A : Forger vp prims optRand pkSeedDist)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × prims.Y) :=
  wotsPhase2All A hist root pk fun x => wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2

/-! ### The open programs do not depend on `Thash` / `H_msg` -/

section HashFree

variable (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
  (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)

theorem lazyRandomizer_hashfree (log : G2Log prims) (msg : List Byte) (addrnd : prims.Y) :
    lazyRandomizer (prims := withTH prims T H) log msg addrnd = lazyRandomizer log msg addrnd := by
  unfold lazyRandomizer
  split <;> rename_i h1 <;> split <;> rename_i h2
  · have h3 := h1.symm.trans h2
    cases h3
    rfl
  · exact absurd (h1.symm.trans h2) (by simp)
  · exact absurd (h2.symm.trans h1) (by simp)
  · rfl

theorem wotsForgeOpen_hashfree (A : Forger vp prims optRand pkSeedDist)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    wotsForgeOpen (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist root pk =
      wotsForgeOpen (gspec := gspec) A hist root pk := by
  have h : (lazyRandomizerLift (prims := withTH prims T H)
        (spec := gspec + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core)) :
        G2Log prims → List Byte → prims.Y → _) =
      lazyRandomizerLift (prims := prims) := by
    funext log msg addrnd
    unfold lazyRandomizerLift
    rw [lazyRandomizer_hashfree]
  exact congrArg (fun rz => runForgerLog (prims := prims) A ⟨pk, root⟩ rz
    (wotsSignFromHistO hist ⟨pk, root⟩)) h

theorem wotsPhase2All_hashfree (A : Forger vp prims optRand pkSeedDist)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β) :
    wotsPhase2All (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist root pk
      tail = wotsPhase2All (gspec := gspec) A hist root pk tail := by
  unfold wotsPhase2All
  rw [wotsForgeOpen_hashfree]
  rfl

theorem wotsWinO_hashfree (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ)
    (m' : prims.Y) (sig' : WotsSig vp.params prims.core) :
    wotsWinO (prims := withTH prims T H) (gspec := gspec) pk hist j m' sig' =
      wotsWinO (gspec := gspec) pk hist j m' sig' := by
  unfold wotsWinO
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · rfl
  · dsimp only

theorem preTargetIndex_hashfree :
    @preTargetIndex vp (withTH prims T H) = @preTargetIndex vp prims := by
  funext hist j i
  unfold preTargetIndex
  rcases hist[j]? with _ | e <;> rfl

theorem tcrTargetIndex_hashfree :
    @tcrTargetIndex vp (withTH prims T H) = @tcrTargetIndex vp prims := by
  funext hist j i t
  unfold tcrTargetIndex
  rcases hist[j]? with _ | e <;> rfl

theorem wotsPreAnswerO_hashfree (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ)
    (m' : prims.Y) (sig' : WotsSig vp.params prims.core) :
    wotsPreAnswerO (prims := withTH prims T H) (gspec := gspec) pk hist j m' sig' =
      wotsPreAnswerO (gspec := gspec) pk hist j m' sig' := by
  unfold wotsPreAnswerO
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · rfl
  · dsimp only
    rw [preTargetIndex_hashfree]
    rfl

theorem wotsTcrAnswerO_hashfree (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ)
    (m' : prims.Y) (sig' : WotsSig vp.params prims.core) :
    wotsTcrAnswerO (prims := withTH prims T H) (gspec := gspec) pk hist j m' sig' =
      wotsTcrAnswerO (gspec := gspec) pk hist j m' sig' := by
  unfold wotsTcrAnswerO
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · rfl
  · dsimp only
    rw [tcrTargetIndex_hashfree]
    rfl

/-- The tail `wotsAnswerOpen` does not depend on `Thash` / `H_msg`. -/
theorem wotsAnswerOpen_hashfree (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    wotsAnswerOpen (prims := withTH prims T H) (gspec := gspec) hist pk msg sig =
      wotsAnswerOpen (gspec := gspec) hist pk msg sig := rfl

/-- **`wotsUdOpenAll` is hash-free**: it is the same program over `withTH prims T H`, for all
`T`, `H`. -/
theorem wotsUdOpenAll_hashfree (A : Forger vp prims optRand pkSeedDist)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    wotsUdOpenAll (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist hist2
      root pk = wotsUdOpenAll (gspec := gspec) A hist hist2 root pk :=
  (congrArg (wotsPhase2All (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist
      root pk)
    (funext fun x => wotsWinO_hashfree T H pk hist2 x.1 x.2.1 x.2.2)).trans
    (wotsPhase2All_hashfree T H A hist root pk _)

theorem wotsPreOpenAll_hashfree (A : Forger vp prims optRand pkSeedDist)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    wotsPreOpenAll (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist hist2
      root pk = wotsPreOpenAll (gspec := gspec) A hist hist2 root pk :=
  (congrArg (wotsPhase2All (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist
      root pk)
    (funext fun x => wotsPreAnswerO_hashfree T H pk hist2 x.1 x.2.1 x.2.2)).trans
    (wotsPhase2All_hashfree T H A hist root pk _)

theorem wotsTcrOpenAll_hashfree (A : Forger vp prims optRand pkSeedDist)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    wotsTcrOpenAll (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist hist2
      root pk = wotsTcrOpenAll (gspec := gspec) A hist hist2 root pk :=
  (congrArg (wotsPhase2All (prims := withTH prims T H) (gspec := gspec) (castForger T H A) hist
      root pk)
    (funext fun x => wotsTcrAnswerO_hashfree T H pk hist2 x.1 x.2.1 x.2.2)).trans
    (wotsPhase2All_hashfree T H A hist root pk _)

end HashFree

/-! ## 6. Summary lemmas -/

/-- **SM-UD, second phase (R3/R7).**  The second phase of `rUd pkSeedDist (Lazy.bWotsS A)` IS
the table interpretation of the open program `wotsUdOpenAll`; nothing is left outside. -/
theorem wotsUd_phase2_open_eq (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((rUd pkSeedDist (Lazy.bWotsS A)).distinguish ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) Bool) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsUdOpenAll A hist hist2 root pk) :=
  (wotsPhase2All_tbl _ A tbl hist root pk _ (fun x => WotsGame.win pk hist2 x.1 x.2.1 x.2.2)
    (fun x => wotsWinO_tbl tbl pk hist2 x.1 x.2.1 x.2.2)).symm

/-- **SM-PRE, second phase.** -/
theorem wotsPre_phase2_open_eq (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((rPre pkSeedDist (Lazy.bWotsS A)).invert ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPreOpenAll A hist hist2 root pk) :=
  (wotsPhase2All_tbl _ A tbl hist root pk _ (fun x => preAnswer pk hist2 x.1 x.2.1 x.2.2)
    (fun x => wotsPreAnswerO_tbl tbl pk hist2 x.1 x.2.1 x.2.2)).symm

/-- **SM-TCR (`rTcr`), second phase.** -/
theorem wotsTcr_phase2_open_eq (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((rTcr pkSeedDist (Lazy.bWotsS A)).forge ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsTcrOpenAll A hist hist2 root pk) :=
  (wotsPhase2All_tbl _ A tbl hist root pk _ (fun x => tcrAnswer pk hist2 x.1 x.2.1 x.2.2)
    (fun x => wotsTcrAnswerO_tbl tbl pk hist2 x.1 x.2.1 x.2.2)).symm

/-- **SM-TCR against the tight-cap game (`rTcrT`), second phase.** -/
theorem wotsTcrT_phase2_open_eq (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).forge ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsTcrOpenAll A hist hist2 root pk) :=
  wotsTcr_phase2_open_eq A tbl hist hist2 root pk

/-- **R7**: the same equalities with the forger given by an arbitrary program `main` (a
`Forger` is exactly its `main`). -/
theorem wotsUd_phase2_open_eq_main
    (main : PublicKeyCore prims.core → OracleComp
      (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (List Byte × GeneralScheme.SignatureCore vp prims.core))
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((rUd pkSeedDist (Lazy.bWotsS (optRand := optRand) (pkSeedDist := pkSeedDist)
        ⟨main⟩)).distinguish ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) Bool) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsUdOpenAll (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨main⟩ hist hist2 root
          pk) :=
  wotsUd_phase2_open_eq _ tbl hist hist2 root pk

theorem wotsPre_phase2_open_eq_main
    (main : PublicKeyCore prims.core → OracleComp
      (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (List Byte × GeneralScheme.SignatureCore vp prims.core))
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((rPre pkSeedDist (Lazy.bWotsS (optRand := optRand) (pkSeedDist := pkSeedDist)
        ⟨main⟩)).invert ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPreOpenAll (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨main⟩ hist hist2 root
          pk) :=
  wotsPre_phase2_open_eq _ tbl hist hist2 root pk

theorem wotsTcrT_phase2_open_eq_main
    (main : PublicKeyCore prims.core → OracleComp
      (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (List Byte × GeneralScheme.SignatureCore vp prims.core))
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS (optRand := optRand)
        (pkSeedDist := pkSeedDist) ⟨main⟩)).forge ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsTcrOpenAll (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨main⟩ hist hist2 root
          pk) :=
  wotsTcrT_phase2_open_eq _ tbl hist hist2 root pk

/-- **R7**: the open programs depend on the forger only through the program `A.main ⟨pk, root⟩`,
which is run once under a fixed handler (uniform bits forwarded; signing queries answered by the
open signer `wotsSignFromHistO`, with `optRand` and the lazy randomizer). -/
theorem wotsForgeOpen_eq_main (A : Forger vp prims optRand pkSeedDist)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    wotsForgeOpen (gspec := gspec) A hist root pk =
      StateT.run (simulateQ
        (((QueryImpl.ofLift unifSpec (OracleComp (Lazy.OSpec prims gspec))).liftTarget
            (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims gspec))) +
          logSignOracle (spec := gspec + ((SecIdx →ₒ prims.Y) + publicHashSpec prims.core))
            optRand ⟨pk, root⟩ lazyRandomizerLift (wotsSignFromHistO hist ⟨pk, root⟩) :
          QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
            (StateT (G2Log prims) (OracleComp (Lazy.OSpec prims gspec)))))
        (A.main ⟨pk, root⟩)) [] := rfl

/-! ### Hash-kind bounds -/

/-- **SM-UD, second phase: hash-kind queries**
`≤ qs · wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsWinHashes vp)`. -/
theorem wotsUd_phase2_open_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    IsQueryBoundP (wotsUdOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsWinHashes vp)) :=
  (wotsPhase2All_kindBound A .hash (by decide) qs hA hist root pk _ _
    (fun x => wotsWinO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2)).mono
    (Nat.add_le_add (Nat.mul_le_mul_left _ wotsSignHistB_ind_hash)
      (Nat.add_le_add (by simpa [Lazy.ind] using wotsAnswerB_hash (vp := vp))
        (by simp [Lazy.ind, wotsWinHashes])))

/-- **SM-PRE, second phase: hash-kind queries.** -/
theorem wotsPre_phase2_open_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    IsQueryBoundP (wotsPreOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsPreHashes vp)) :=
  (wotsPhase2All_kindBound A .hash (by decide) qs hA hist root pk _ _
    (fun x => wotsPreAnswerO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2)).mono
    (Nat.add_le_add (Nat.mul_le_mul_left _ wotsSignHistB_ind_hash)
      (Nat.add_le_add (by simpa [Lazy.ind] using wotsAnswerB_hash (vp := vp))
        (by simp [Lazy.ind, wotsPreHashes])))

/-- **SM-TCR (`rTcr` / `rTcrT`), second phase: hash-kind queries.** -/
theorem wotsTcrT_phase2_open_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    IsQueryBoundP (wotsTcrOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp + (wotsAnswerHashes vp + wotsTcrHashes vp)) :=
  (wotsPhase2All_kindBound A .hash (by decide) qs hA hist root pk _ _
    (fun x => wotsTcrAnswerO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2)).mono
    (Nat.add_le_add (Nat.mul_le_mul_left _ wotsSignHistB_ind_hash)
      (Nat.add_le_add (by simpa [Lazy.ind] using wotsAnswerB_hash (vp := vp)) (by
        have h1 : Lazy.ind Lazy.Kind.hash Lazy.Kind.hash = 1 := rfl
        rw [h1, wotsTcrHashes]
        exact le_of_eq (by ring))))

/-! ### Secret reads and game queries of the complete second phases -/

/-- Table reads of the complete second phase, whatever the (read-free) tail:
`≤ (qs + 1) · k · 2^a`. -/
theorem wotsPhase2All_reads (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β)
    (htail : ∀ x, IsQueryBoundP (tail x) (fun t => Lazy.kind t = .sec) 0) :
    IsQueryBoundP (wotsPhase2All A hist root pk tail) (fun t => Lazy.kind t = .sec)
      ((qs + 1) * (vp.params.k * 2 ^ vp.params.a)) :=
  (wotsPhase2All_kindBound A .sec (by decide) qs hA hist root pk tail 0 htail).mono (by
    have h1 : wotsSignHistB vp (Lazy.ind .sec .sec) (Lazy.ind .sec .hash) ≤
        vp.params.k * 2 ^ vp.params.a := by simpa [Lazy.ind] using wotsSignHistB_sec (vp := vp)
    have h2 : wotsAnswerB vp (Lazy.ind .sec .sec) (Lazy.ind .sec .hash) ≤
        vp.params.k * 2 ^ vp.params.a := by simpa [Lazy.ind] using wotsAnswerB_sec (vp := vp)
    rw [Nat.add_mul, Nat.one_mul, Nat.add_zero]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2)

/-- The complete second phase makes no game query, whatever the (game-free) tail. -/
theorem wotsPhase2All_game (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β)
    (htail : ∀ x, IsQueryBoundP (tail x) (fun t => Lazy.kind t = .game) 0) :
    IsQueryBoundP (wotsPhase2All A hist root pk tail) (fun t => Lazy.kind t = .game) 0 :=
  (wotsPhase2All_kindBound A .game (by decide) qs hA hist root pk tail 0 htail).mono
    (by simp [Lazy.ind, wotsSignHistB_game, wotsAnswerB_game])

/-! ### Numerals at SLH-DSA-SHA2-128s -/

/-- SM-UD second phase at 128s: `≤ qs·121857 + 130239` hash-kind queries. -/
theorem wotsUd_phase2_open_hashes_128s {ι : Type} {gspec : OracleSpec ι}
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist hist2 : List (WotsGame.Entry Link.prims)) (root : Link.prims.Y)
    (pk : Link.prims.PkSeed) :
    IsQueryBoundP (wotsUdOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash) (qs * 121857 + 130239) := by
  have h := wotsUd_phase2_open_hashes (gspec := gspec) A qs hA hist hist2 root pk
  rwa [wotsSignHistHashes_128s, wotsAnswerHashes_128s, wotsWinHashes_128s] at h

/-- SM-PRE second phase at 128s: `≤ qs·121857 + 130274` hash-kind queries. -/
theorem wotsPre_phase2_open_hashes_128s {ι : Type} {gspec : OracleSpec ι}
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist hist2 : List (WotsGame.Entry Link.prims)) (root : Link.prims.Y)
    (pk : Link.prims.PkSeed) :
    IsQueryBoundP (wotsPreOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash) (qs * 121857 + 130274) := by
  have h := wotsPre_phase2_open_hashes (gspec := gspec) A qs hA hist hist2 root pk
  rwa [wotsSignHistHashes_128s, wotsAnswerHashes_128s, wotsPreHashes_128s] at h

/-- SM-TCR second phase at 128s: `≤ qs·121857 + 146514` hash-kind queries. -/
theorem wotsTcrT_phase2_open_hashes_128s {ι : Type} {gspec : OracleSpec ι}
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist hist2 : List (WotsGame.Entry Link.prims)) (root : Link.prims.Y)
    (pk : Link.prims.PkSeed) :
    IsQueryBoundP (wotsTcrOpenAll (gspec := gspec) A hist hist2 root pk)
      (fun t => Lazy.kind t = .hash) (qs * 121857 + 146514) := by
  have h := wotsTcrT_phase2_open_hashes (gspec := gspec) A qs hA hist hist2 root pk
  rwa [wotsSignHistHashes_128s, wotsAnswerHashes_128s, wotsTcrHashes_128s] at h

end Open
end Reduction

#print axioms Reduction.Open.wotsAnswerOpen_tbl
#print axioms Reduction.Open.wotsAnswerOpen_kindBound
#print axioms Reduction.Open.wotsAnswerOpen_hashes
#print axioms Reduction.Open.wotsAnswerHashes_128s
#print axioms Reduction.Open.wotsUdOpenAll_hashfree
#print axioms Reduction.Open.wotsPreOpenAll_hashfree
#print axioms Reduction.Open.wotsTcrOpenAll_hashfree
#print axioms Reduction.Open.wotsUd_phase2_open_eq
#print axioms Reduction.Open.wotsPre_phase2_open_eq
#print axioms Reduction.Open.wotsTcr_phase2_open_eq
#print axioms Reduction.Open.wotsTcrT_phase2_open_eq
#print axioms Reduction.Open.wotsUd_phase2_open_eq_main
#print axioms Reduction.Open.wotsPre_phase2_open_eq_main
#print axioms Reduction.Open.wotsTcrT_phase2_open_eq_main
#print axioms Reduction.Open.wotsForgeOpen_eq_main
#print axioms Reduction.Open.wotsAnswerOpen_hashfree
#print axioms Reduction.Open.wotsUd_phase2_open_hashes
#print axioms Reduction.Open.wotsPre_phase2_open_hashes
#print axioms Reduction.Open.wotsTcrT_phase2_open_hashes
#print axioms Reduction.Open.wotsPhase2All_reads
#print axioms Reduction.Open.wotsPhase2All_game
#print axioms Reduction.Open.wotsUd_phase2_open_hashes_128s
#print axioms Reduction.Open.wotsPre_phase2_open_hashes_128s
#print axioms Reduction.Open.wotsTcrT_phase2_open_hashes_128s
