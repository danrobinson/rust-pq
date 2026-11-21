import Reduction.Lazy.OpenPreSparse
import Reduction.Lazy.ItsrLazy
import Reduction.ForsTightFinal

/-!
# Local hash evaluations of the second phase of `toDspr (bOpenPreS A)` / `toTcr (bOpenPreS A)`

The second phase of both adversaries is one run of `B.find s pk ys` (`B = Lazy.bOpenPreS A`)
under `findOracles tg`, plus (DSPR) one comparison (`toTcr_forge`, `toDspr_guess`).  This file
counts the hash evaluations `B.find` performs itself, by writing it as an open program over
`Lazy.OSpec prims (openSpec prims.Y)` in which every hash evaluation is a hash query.

## Programs

* `forsSignOpen pk ys m R` — open form of `Reduction.openSign`: `H_msg` (query); FORS
  authentication paths from the leaf images (`forsSignWithSecret` with leaf callback
  `forsImgHashO` = identity at tree height `0`, `H` queries on inner nodes); `k` opening (game)
  queries; FORS root recovery (`forsPkFromSigM`); hypertree signature (`signWithSecretM`, WOTS+
  secrets by secret queries).
* `findOpen A pkSeed ys` — `Lazy.openKeygen`, the forger's run with `forsSignOpen`, and the
  answer extraction `openPreAnswer` as a *pure* tail (not counted).
* `findAnswerO` — open form of `openPreAnswer` (`H_msg` for the forgery, `H_msg` once per signed
  message, `k` `F` queries), and `findOpenFull A pkSeed ys` — as `findOpen` with `findAnswerO`
  as tail: **every** hash evaluation of the `find` phase is a hash query of `findOpenFull`.

## Theorems (all for an arbitrary table sampler `my`; no hypotheses besides the forger's bound)

* `forsSignOpen_tbl`, `findAnswerO_tbl`, `findOpen_tbl`, `findOpenFull_tbl`:
  `simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (findOpenFull A pkSeed ys) =
    (bOpenPreWith my A).find tbl pkSeed ys`; `…_bOpenPreS` at `Lazy.bOpenPreS A`.
* `forsSignOpen_kindBound`, `findRun_kindBound`, `findOpen_kindBound`, `findOpenFull_kindBound`:
  queries of each kind `K ≠ .unif`, budget `forsSignB vp cG cS c` per signature.
* Closed forms, for a forger with at most `qs` signing queries:
  - `findOpenFull_hashes`: hash queries `≤ keygenHashes vp + qs * forsSignHashes vp + (1 + qs + k)`,
    `forsSignHashes vp = 1 + k(2^a − 1) + (k(1+a) + 1) + d(2^h'(len(w−1)+2) + len(w−1) + 1 + h')`;
    `findOpen_hashes` is the same without the last summand (pure tail);
  - `findOpenFull_openings`: opening queries `≤ qs * k`;
  - `findOpenFull_reads`: secret reads `≤ 2^h' len + qs * d * 2^h' * len` (WOTS+ cells only).
  - SLH-DSA-SHA2-128s: `forsSignHashes_128s : forsSignHashes Link.vp = 1950027`,
    `findOpen_hashes_128s : 269824 + qs * 1950027`,
    `findOpenFull_hashes_128s : 269839 + qs * 1950028`.
* `toTcr_bOpenPreS_forge_full`, `toDspr_bOpenPreS_guess_full` (and the `findOpen` versions
  `toTcr_bOpenPreS_forge`, `toDspr_bOpenPreS_guess`): the second phases of the headline
  adversaries are one run of `simulateQ (tblImpl … tbl) (findOpenFull A pk ys)` under
  `findOracles tg`, followed by a projection / one comparison and list-membership test.

## What is and is not counted

Counted formally (as hash queries of `findOpenFull`): everything `B.find` hashes — key
generation, all signing simulations, answer extraction.  The count is an upper bound: the open
answer extraction asks all `k` `F` queries where the pure `openPreAnswer` may stop early.
Not counted (no hashing): the forger's own computation; the opening simulation `findOracles tg`
(a list lookup per opening); the DSPR comparison; the first phases (`pick`, target sampling),
which are treated elsewhere.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Resources2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

attribute [local instance] Lazy.openQ Lazy.closedQ

/-! ## 1. The open program -/

/-- The game oracle of the `find` phase: the opening oracle. -/
abbrev forsG (prims : Primitives vp.params) : OracleSpec ℕ :=
  TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.openSpec prims.Y

/-- The monad morphism `Id → n` (`pure`). -/
def forsIdHom (n : Type → Type) [Monad n] [LawfulMonad n] : Id →ᵐ n where
  toFun {_} x := pure (Id.run x)
  toFun_pure' _ := rfl
  toFun_bind' x f := by simp

/-- The leaf callback of `forsSigFromImages`, open form: the identity at tree height `0` (the
"secret" at a leaf is already its image), an explicit `F` query otherwise (never reached). -/
def forsImgHashO (pkSeed : prims.PkSeed) (a : Adrs) (x : prims.Y) :
    OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y :=
  if a.word2 = 0 then pure x else PublicHash.f prims.core pkSeed a x

/-- Open form of `Reduction.openSign`: every hash evaluation is a hash query, every WOTS+ secret
read a secret query, every opening an opening (game) query. -/
def forsSignOpen (pk : PublicKeyCore prims.core) (ys : List prims.Y) (m : List Byte)
    (R : prims.Y) :
    OracleComp (Lazy.OSpec prims (forsG prims)) (GeneralScheme.SignatureCore vp prims.core) := do
  let digest ← PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot m
  let parts : DigestParts vp.params := splitDigest vp.params digest
  let img ← forsSignWithSecret prims.core (forsImgHashO pk.pkSeed)
    (PublicHash.h prims.core pk.pkSeed)
    (fun a => (pure (leafImage (vp := vp) ys (skToLeaf a)) :
      OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y)) parts.md.toList parts.forsAdrs
  let forsSig ← Vector.ofFnM fun i : Fin vp.params.k => do
    let x ← Lazy.gameQ prims (forsG prims)
      (leafTarget vp prims (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)))
    pure (⟨x, (img[i.val]).auth⟩ : ForsTreeSigCore vp.params prims.core)
  let forsPk ← forsPkFromSigM prims.core forsSig parts.md.toList pk.pkSeed parts.forsAdrs
  let htSig ← GeneralHypertree.signWithSecretM prims.core (Lazy.secQ prims (forsG prims)) forsPk
    pk.pkSeed parts
  return ⟨R, forsSig, htSig⟩

/-- The open program of the `find` phase of `bOpenPreWith my A`. -/
noncomputable def findOpen (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed)
    (ys : List prims.Y) : OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y) := do
  let root ← Lazy.openKeygen prims (forsG prims) pkSeed
  let z ← runForgerLog A ⟨pkSeed, root⟩ lazyRandomizerLift (forsSignOpen ⟨pkSeed, root⟩ ys)
  return openPreAnswer ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2

/-! ## 2. Interpretation by a table -/

theorem forsSignOpen_tbl (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core)
    (ys : List prims.Y) (m : List Byte) (R : prims.Y) :
    simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (forsSignOpen pk ys m R) = Reduction.openSign pk tbl ys m R := by
  have hf : ∀ (a : Adrs) (y : prims.Y), (Lazy.tblHom (gspec := forsG prims) tbl).toMonadHom
      (PublicHash.f prims.core pk.pkSeed a y) = pure (prims.F pk.pkSeed a y) := fun a y =>
    (Lazy.tblHom (gspec := forsG prims) tbl).map_query' _
  have hh : ∀ (a : Adrs) (l r : prims.Y), (Lazy.tblHom (gspec := forsG prims) tbl).toMonadHom
      (PublicHash.h prims.core pk.pkSeed a l r) = pure (prims.H pk.pkSeed a l r) := fun a l r =>
    (Lazy.tblHom (gspec := forsG prims) tbl).map_query' _
  have htl : ∀ (a : Adrs) (xs : List prims.Y),
      (Lazy.tblHom (gspec := forsG prims) tbl).toMonadHom
      (PublicHash.tl prims.core pk.pkSeed a xs) = pure (prims.Tl pk.pkSeed a xs) := fun a xs =>
    (Lazy.tblHom (gspec := forsG prims) tbl).map_query' _
  have hm : simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
      (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot m) =
      pure (prims.Hmsg R pk.pkSeed pk.pkRoot m) :=
    (Lazy.tblHom (gspec := forsG prims) tbl).map_query' _
  have himg : ∀ (md : List Byte) (adrs : Adrs),
      simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (forsSignWithSecret prims.core (forsImgHashO pk.pkSeed)
          (PublicHash.h prims.core pk.pkSeed)
          (fun a => (pure (leafImage (vp := vp) ys (skToLeaf a)) :
            OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y)) md adrs) =
      pure (forsSigFromImages (vp := vp) pk.pkSeed ys md adrs) := fun md adrs =>
    (forsSignWithSecret_natural prims.core (Lazy.tblHom (gspec := forsG prims) tbl).toMonadHom
      (forsImgHashO pk.pkSeed)
      (fun a x => pure (if a.word2 = 0 then x else prims.F pk.pkSeed a x))
      _ (fun a l r => pure (prims.H pk.pkSeed a l r))
      (fun a => (pure (leafImage (vp := vp) ys (skToLeaf a)) :
        OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y))
      (fun a => pure (leafImage (vp := vp) ys (skToLeaf a)))
      (fun a y => by
        unfold forsImgHashO
        by_cases h : a.word2 = 0
        · simp only [h, ↓reduceIte]
          exact simulateQ_pure (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl) y
        · simp only [h, ↓reduceIte]
          exact hf a y) hh
      (fun a _ => simulateQ_pure
        (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl) _) md adrs).trans
    (forsSignWithSecret_natural prims.core (forsIdHom (OracleComp (unifSpec + forsG prims)))
      (fun a x => if a.word2 = 0 then x else prims.F pk.pkSeed a x)
      (fun a x => pure (if a.word2 = 0 then x else prims.F pk.pkSeed a x))
      (fun a l r => prims.H pk.pkSeed a l r) (fun a l r => pure (prims.H pk.pkSeed a l r))
      (fun a => leafImage (vp := vp) ys (skToLeaf a))
      (fun a => pure (leafImage (vp := vp) ys (skToLeaf a)))
      (fun a y => rfl) (fun a l r => rfl) (fun a _ => rfl) md adrs).symm
  have hpk : ∀ (sig : ForsSigCore vp.params prims.core) (md : List Byte) (adrs : Adrs),
      simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (forsPkFromSigM prims.core sig md pk.pkSeed adrs) =
      pure (forsPkFromSig prims sig md pk.pkSeed adrs) := fun sig md adrs => by
    have h1 := forsPkFromSigM_natural prims.core (Lazy.tblHom (gspec := forsG prims) tbl)
      sig md pk.pkSeed adrs
    have h2 := forsPkFromSigM_natural prims.core
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
        (m := OracleComp (unifSpec + forsG prims))) sig md pk.pkSeed adrs
    rw [Lazy.free_apply] at h2
    exact h1.trans h2.symm
  have hht : ∀ (m0 : prims.Y) (parts : DigestParts vp.params),
      simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (GeneralHypertree.signWithSecretM prims.core (Lazy.secQ prims (forsG prims)) m0
          pk.pkSeed parts) =
      pure (opHt tbl pk.pkSeed m0 parts) := fun m0 parts =>
    (GeneralHypertree.signWithSecret_natural prims.core
      (Lazy.tblHom (gspec := forsG prims) tbl).toMonadHom
      _ (fun a x => pure (prims.F pk.pkSeed a x))
      _ (fun a xs => pure (prims.Tl pk.pkSeed a xs))
      _ (fun a l r => pure (prims.H pk.pkSeed a l r))
      (Lazy.secQ prims (forsG prims)) (fun a => pure (secretOf vp prims tbl a))
      hf htl hh (fun a _ => Lazy.simulateQ_tblImpl_secQ tbl a) m0 parts).trans
    (GeneralHypertree.signWithSecret_natural prims.core
      (forsIdHom (OracleComp (unifSpec + forsG prims)))
      (fun a x => prims.F pk.pkSeed a x) (fun a x => pure (prims.F pk.pkSeed a x))
      (fun a xs => prims.Tl pk.pkSeed a xs) (fun a xs => pure (prims.Tl pk.pkSeed a xs))
      (fun a l r => prims.H pk.pkSeed a l r) (fun a l r => pure (prims.H pk.pkSeed a l r))
      (fun a => secretOf vp prims tbl a) (fun a => pure (secretOf vp prims tbl a))
      (fun a y => rfl) (fun a ys => rfl) (fun a l r => rfl) (fun a _ => rfl) m0 parts).symm
  have hvec : ∀ (parts : DigestParts vp.params) (img : ForsSigCore vp.params prims.core),
      simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (Vector.ofFnM fun i : Fin vp.params.k => do
          let x ← Lazy.gameQ prims (forsG prims)
            (leafTarget vp prims (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)))
          pure (⟨x, (img[i.val]).auth⟩ : ForsTreeSigCore vp.params prims.core)) =
      (Vector.ofFnM fun i : Fin vp.params.k => do
        let x ← ((openSpecY prims).query (Sum.inr (leafTarget vp prims
            (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)))) :
          OracleComp (openSpecY prims) prims.Y)
        pure (⟨x, (img[i.val]).auth⟩ : ForsTreeSigCore vp.params prims.core)) :=
    fun parts img =>
      Vector.ofFnM_natural (Lazy.tblHom (gspec := forsG prims) tbl).toMonadHom _ _ (fun i => by
        refine (simulateQ_bind _ _ _).trans ?_
        rw [Lazy.simulateQ_tblImpl_gameQ]
        refine bind_congr fun x => ?_
        exact simulateQ_pure _ _)
  unfold forsSignOpen
  rw [simulateQ_bind, hm, pure_bind, simulateQ_bind, himg, pure_bind, simulateQ_bind, hvec]
  unfold Reduction.openSign
  refine bind_congr fun forsSig => ?_
  rw [simulateQ_bind, hpk, pure_bind, simulateQ_bind, hht, pure_bind, simulateQ_pure]
  rfl

/-- `Lazy.runForgerLog_tbl` for an arbitrary game spec. -/
theorem fors_runForgerLog_tbl {ι : Type} {gspec : OracleSpec ι}
    (A : Forger vp prims optRand pkSeedDist) (g : SecretTable vp prims)
    (pk : PublicKeyCore prims.core)
    (randO : G2Log prims → List Byte → prims.Y → OracleComp (Lazy.OSpec prims gspec) prims.Y)
    (signO : List Byte → prims.Y → OracleComp (Lazy.OSpec prims gspec)
      (GeneralScheme.SignatureCore vp prims.core))
    (randC : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + gspec) prims.Y)
    (signC : List Byte → prims.Y → OracleComp (unifSpec + gspec)
      (GeneralScheme.SignatureCore vp prims.core))
    (hrand : ∀ log m a, simulateQ (Lazy.tblImpl (PublicHash.impl prims) g) (randO log m a) =
      randC log m a)
    (hsign : ∀ m R, simulateQ (Lazy.tblImpl (PublicHash.impl prims) g) (signO m R) = signC m R) :
    simulateQ (Lazy.tblImpl (PublicHash.impl prims) g) (runForgerLog A pk randO signO) =
      runForgerLog A pk randC signC := by
  unfold runForgerLog
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  congr 2
  funext t
  cases t with
  | inl n =>
    refine StateT.ext fun s => ?_
    simp [QueryImpl.mapStateTBase]
    exact Lazy.simulateQ_tblImpl_liftM (PublicHash.impl prims) g (liftM (unifSpec.query n))
  | inr m =>
    refine StateT.ext fun s => ?_
    simp [QueryImpl.mapStateTBase, logSignOracle, hrand, hsign, Lazy.simulateQ_tblImpl_liftM]

/-- **The open program is the `find` phase.**  Interpreting the secret oracle of `findOpen` by
the table `tbl` and its hash queries by `prims` gives exactly the second phase of
`bOpenPreWith my A` (for every table sampler `my`). -/
theorem findOpen_tbl (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (findOpen A pkSeed ys) =
      (bOpenPreWith my A).find tbl pkSeed ys := by
  unfold findOpen
  rw [simulateQ_bind, Lazy.openKeygen_tbl, pure_bind, simulateQ_bind]
  have hrun := fors_runForgerLog_tbl A tbl ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩
    (gspec := forsG prims) lazyRandomizerLift
    (forsSignOpen ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ ys)
    lazyRandomizerLift
    (Reduction.openSign ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ tbl ys)
    (fun log m a => Lazy.simulateQ_tblImpl_liftM (PublicHash.impl prims) tbl
      (lazyRandomizer log m a))
    (fun m R => forsSignOpen_tbl tbl ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ ys m R)
  rw [hrun]
  simp only [simulateQ_pure]
  rfl

/-- `findOpen_tbl` at the sparse-table adversary `Lazy.bOpenPreS A`. -/
theorem findOpen_tbl_bOpenPreS (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (findOpen A pkSeed ys) =
      (Lazy.bOpenPreS A).find tbl pkSeed ys :=
  findOpen_tbl _ A tbl pkSeed ys

/-! ## 3. Counting -/

theorem forsImgHashO_leaf (pkSeed : prims.PkSeed) (adrs : Adrs) (j : ℕ) (x : prims.Y) :
    forsImgHashO pkSeed (forsNodeAdrs adrs 0 j) x = pure x :=
  rfl

/-- Budget of one simulated signature: `cG` per opening query, `cS` per secret read, `c` per
hash evaluation.  Summands: `H_msg`; FORS authentication paths from the leaf images (`H` on
inner nodes only); the `k` openings; FORS root recovery; the hypertree signature. -/
def forsSignB (vp : ValidatedParams) (cG cS c : ℕ) : ℕ :=
  c + vp.params.k * Lazy.authB 0 c vp.params.a + vp.params.k * cG +
    (vp.params.k * (c + vp.params.a * c) + c) +
    vp.params.d * (Lazy.xmssSignB vp c c c cS + Lazy.xmssPkB vp c c c)

theorem forsSignOpen_kindBound (K : Lazy.Kind) (pk : PublicKeyCore prims.core)
    (ys : List prims.Y) (m : List Byte) (R : prims.Y) :
    IsQueryBoundP (forsSignOpen pk ys m R) (fun t => Lazy.kind t = K)
      (forsSignB vp (Lazy.ind K .game) (Lazy.ind K .sec) (Lazy.ind K .hash)) := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pk.pkSeed a y :
      OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y) (fun t => Lazy.kind t = K)
        (Lazy.ind K .hash) :=
    fun _ _ => Lazy.query_kindBound K _
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsQueryBoundP (PublicHash.tl prims.core pk.pkSeed a ys :
      OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y) (fun t => Lazy.kind t = K)
        (Lazy.ind K .hash) :=
    fun _ _ => Lazy.query_kindBound K _
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pk.pkSeed a l r :
      OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y) (fun t => Lazy.kind t = K)
        (Lazy.ind K .hash) :=
    fun _ _ _ => Lazy.query_kindBound K _
  have hs : ∀ a : Adrs, IsQueryBoundP (Lazy.secQ prims (forsG prims) a)
      (fun t => Lazy.kind t = K) (Lazy.ind K .sec) :=
    fun _ => Lazy.query_kindBound K _
  have hm : IsQueryBoundP (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot m :
      OracleComp (Lazy.OSpec prims (forsG prims)) _) (fun t => Lazy.kind t = K)
        (Lazy.ind K .hash) :=
    Lazy.query_kindBound K _
  have himg : ∀ (md : List Byte) (adrs : Adrs),
      IsQueryBoundP (forsSignWithSecret prims.core (forsImgHashO pk.pkSeed)
          (PublicHash.h prims.core pk.pkSeed)
          (fun a => (pure (leafImage (vp := vp) ys (skToLeaf a)) :
            OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y)) md adrs)
        (fun t => Lazy.kind t = K)
        (vp.params.k * Lazy.authB 0 (Lazy.ind K .hash) vp.params.a) := by
    intro md adrs
    refine Lazy.qb_ofFnM _ _ _ fun i => ?_
    have h := Lazy.qb_authPath (fun t => Lazy.kind t = K)
      (forsLeafWithSecret prims.core (forsImgHashO pk.pkSeed)
        (fun a => (pure (leafImage (vp := vp) ys (skToLeaf a)) :
          OracleComp (Lazy.OSpec prims (forsG prims)) prims.Y)) adrs)
      (forsNodeHashWith (PublicHash.h prims.core pk.pkSeed) adrs) 0 (Lazy.ind K .hash)
      (i.val * 2 ^ vp.params.a + forsIdx vp.params md i.val) vp.params.a
      (fun j => by
        unfold forsLeafWithSecret
        rw [pure_bind, forsImgHashO_leaf]
        exact isQueryBoundP_pure _ _ _)
      (fun h i l r => hh _ l r)
    exact (Lazy.qb_bind _ (n := 0) (isQueryBoundP_pure _ _ _) fun sk =>
      Lazy.qb_bind _ (m := 0) h fun path => isQueryBoundP_pure _ _ _).mono (by omega)
  unfold forsSignOpen
  refine (Lazy.qb_bind _ hm fun digest =>
    Lazy.qb_bind _ (himg _ _) fun img =>
      Lazy.qb_bind _ (Lazy.qb_ofFnM _ _ (Lazy.ind K .game) fun i =>
          Lazy.qb_bind _ (m := 0) (Lazy.gameQ_kindBound K _) fun x =>
            isQueryBoundP_pure _ _ _) fun forsSig =>
        Lazy.qb_bind _ (Lazy.qb_forsPk _ prims.core _ _ _ hf htl hh forsSig _ _) fun forsPk =>
          Lazy.qb_bind _ (m := 0)
            (Lazy.qb_signFromPos _ prims.core _ _ _ _ hf htl hh hs _ _ _ _ _)
            fun htSig => isQueryBoundP_pure _ _ _).mono ?_
  unfold forsSignB
  omega

/-- Queries of kind `K` of the forger's run with all signing simulations. -/
theorem findRun_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Lazy.Kind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) (root : prims.Y) :
    IsQueryBoundP (runForgerLog A ⟨pkSeed, root⟩ lazyRandomizerLift
        (forsSignOpen ⟨pkSeed, root⟩ ys)) (fun t => Lazy.kind t = K)
      (qs * forsSignB vp (Lazy.ind K .game) (Lazy.ind K .sec) (Lazy.ind K .hash)) := by
  unfold runForgerLog
  refine IsQueryBoundP.simulateQ_run_of_step_le (hA _) (fun t ht s => ?_) (fun t ht s => ?_) []
  · cases t with
    | inl n => simp at ht
    | inr m =>
      have hstep := Lazy.qb_bind (fun t => Lazy.kind t = K)
        (Lazy.liftM_kindBound (gspec := forsG prims) (D := SecIdx) (V := prims.Y)
          (hspec := publicHashSpec prims.core) K hK (optRand ⟨pkSeed, root⟩)) fun addrnd =>
        Lazy.qb_bind (fun t => Lazy.kind t = K)
          (Lazy.liftM_kindBound (gspec := forsG prims) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) K hK (lazyRandomizer s m addrnd)) fun R =>
          Lazy.qb_bind (fun t => Lazy.kind t = K) (m := 0)
            (forsSignOpen_kindBound K ⟨pkSeed, root⟩ ys m R)
            fun sig => isQueryBoundP_pure _ (sig, s ++ [(m, addrnd, R)]) _
      simpa [logSignOracle, lazyRandomizerLift] using hstep
  · cases t with
    | inl n =>
      simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
      have h0 := Lazy.qb_bind (fun t => Lazy.kind t = K) (m := 0)
        (Lazy.liftM_kindBound (gspec := forsG prims) (D := SecIdx) (V := prims.Y)
          (hspec := publicHashSpec prims.core) K hK
          (liftM (unifSpec.query n) : ProbComp _)) fun x => isQueryBoundP_pure _ (x, s) _
      exact h0
    | inr m => simp at ht

/-- **Queries of kind `K` (opening / secret / hash) of `findOpen`**, for a forger with at most
`qs` signing queries. -/
theorem findOpen_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Lazy.Kind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (findOpen A pkSeed ys) (fun t => Lazy.kind t = K)
      (Lazy.keygenB vp (Lazy.ind K .sec) (Lazy.ind K .hash) +
        qs * forsSignB vp (Lazy.ind K .game) (Lazy.ind K .sec) (Lazy.ind K .hash)) := by
  unfold findOpen
  exact (Lazy.qb_bind _ (Lazy.openKeygen_kindBound K pkSeed) fun root =>
      Lazy.qb_bind _ (m := 0) (findRun_kindBound A K hK qs hA pkSeed ys root) fun z =>
        isQueryBoundP_pure _ _ _).mono (by omega)

/-! ### Closed forms -/

/-- Hash evaluations of one simulated signature (an upper bound): `H_msg`; `k` FORS
authentication paths from the leaf images (`2^a - 1` inner nodes each, no leaf hash); FORS root
recovery (`k·(1+a)` and one `T_k`); per hypertree layer one XMSS signature and one XMSS root
recovery. -/
def forsSignHashes (vp : ValidatedParams) : ℕ :=
  1 + vp.params.k * (2 ^ vp.params.a - 1) + (vp.params.k * (1 + vp.params.a) + 1) +
    vp.params.d * (2 ^ vp.params.hp * (vp.params.len * (vp.params.w - 1) + 2) +
      (vp.params.len * (vp.params.w - 1) + 1 + vp.params.hp))

theorem forsSignB_game : forsSignB vp 1 0 0 = vp.params.k := by
  simp [forsSignB, Lazy.xmssSignB, Lazy.xmssPkB, Lazy.wotsB, Lazy.authB_zero]

theorem forsSignB_sec : forsSignB vp 0 1 0 ≤ vp.params.d * (2 ^ vp.params.hp * vp.params.len) := by
  have h2 := Lazy.authB_add (Lazy.wotsB vp 0 1 + 0) 0 vp.params.hp
  have hw : Lazy.wotsB vp 0 1 = vp.params.len := by simp [Lazy.wotsB]
  have hx : Lazy.xmssSignB vp 0 0 0 1 + Lazy.xmssPkB vp 0 0 0 ≤
      2 ^ vp.params.hp * vp.params.len := by
    unfold Lazy.xmssSignB Lazy.xmssPkB
    simp only [hw, Nat.add_zero, Nat.mul_zero] at h2 ⊢
    omega
  have := Nat.mul_le_mul_left vp.params.d hx
  simpa [forsSignB, Lazy.authB_zero] using this

theorem forsSignB_hash : forsSignB vp 0 0 1 ≤ forsSignHashes vp := by
  have h1 := Lazy.authB_add 0 1 vp.params.a
  have h2 := Lazy.authB_add (Lazy.wotsB vp 1 0 + 1) 1 vp.params.hp
  have hw : Lazy.wotsB vp 1 0 = vp.params.len * (vp.params.w - 1) := by simp [Lazy.wotsB]
  have ha : Lazy.authB 0 1 vp.params.a ≤ 2 ^ vp.params.a - 1 := by
    simp only [Nat.zero_add, Nat.mul_one] at h1
    omega
  have hx : Lazy.xmssSignB vp 1 1 1 0 + Lazy.xmssPkB vp 1 1 1 ≤
      2 ^ vp.params.hp * (vp.params.len * (vp.params.w - 1) + 2) +
        (vp.params.len * (vp.params.w - 1) + 1 + vp.params.hp) := by
    unfold Lazy.xmssSignB Lazy.xmssPkB
    simp only [hw, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] at h2 ⊢
    omega
  have h3 := Nat.mul_le_mul_left vp.params.k ha
  have h4 := Nat.mul_le_mul_left vp.params.d hx
  unfold forsSignB forsSignHashes
  simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
  omega

/-- **Hash evaluations of `findOpen`**: key generation plus `qs` simulated signatures. -/
theorem findOpen_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (findOpen A pkSeed ys) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * forsSignHashes vp) :=
  (findOpen_kindBound A .hash (by decide) qs hA pkSeed ys).mono
    (Nat.add_le_add Lazy.keygenB_hash (Nat.mul_le_mul_left _ (by
      simpa [Lazy.ind] using forsSignB_hash (vp := vp))))

/-- **Opening queries of `findOpen`**: `k` per simulated signature. -/
theorem findOpen_openings (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (findOpen A pkSeed ys) (fun t => Lazy.kind t = .game) (qs * vp.params.k) :=
  (findOpen_kindBound A .game (by decide) qs hA pkSeed ys).mono
    (by simp [Lazy.ind, Lazy.keygenB_game, forsSignB_game])

/-- **Secret (table) reads of `findOpen`**: WOTS+ start values only. -/
theorem findOpen_reads (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (findOpen A pkSeed ys) (fun t => Lazy.kind t = .sec)
      (2 ^ vp.params.hp * vp.params.len +
        qs * (vp.params.d * (2 ^ vp.params.hp * vp.params.len))) :=
  (findOpen_kindBound A .sec (by decide) qs hA pkSeed ys).mono
    (Nat.add_le_add Lazy.keygenB_sec (Nat.mul_le_mul_left _ (by
      simpa [Lazy.ind] using forsSignB_sec (vp := vp))))

/-- Hash evaluations of one simulated signature at SLH-DSA-SHA2-128s. -/
theorem forsSignHashes_128s : forsSignHashes Link.vp = 1950027 := by decide

/-- Hash evaluations of `findOpen` at SLH-DSA-SHA2-128s: `269824 + qs · 1950027`. -/
theorem findOpen_hashes_128s (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : Link.prims.PkSeed) (ys : List Link.prims.Y) :
    IsQueryBoundP (findOpen A pkSeed ys) (fun t => Lazy.kind t = .hash)
      (269824 + qs * 1950027) := by
  have h := findOpen_hashes A qs hA pkSeed ys
  rwa [forsSignHashes_128s, show Lazy.keygenHashes Link.vp = 269824 by decide] at h

/-! ## 4. The second phases of `toTcr` / `toDspr` -/

open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity in
/-- Generic form: if `B.find` is the table interpretation of an open program `P`, the forge
phase of `toTcr B` is one run of that interpretation under the opening simulation. -/
theorem fors_toTcr_forge_of (B : ForsOpenPreAdv vp prims pkSeedDist) (s : B.State)
    (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y) (pk : prims.PkSeed)
    (tbl : SecretTable vp prims)
    (P : OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y))
    (hB : simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) P = B.find s pk ys) :
    (toTcr B).forge (s, tg, ys) pk =
      (simulateQ (findOracles tg)
        (simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) P)).run [] >>=
          fun z => pure z.1 := by
  rw [hB]
  exact toTcr_forge B s tg ys pk

open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity in
/-- Generic form for the guess phase of `toDspr B`. -/
theorem fors_toDspr_guess_of (B : ForsOpenPreAdv vp prims pkSeedDist) (s : B.State)
    (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y) (pk : prims.PkSeed)
    (tbl : SecretTable vp prims)
    (P : OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y))
    (hB : simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) P = B.find s pk ys) :
    (toDspr B).guess (s, tg, ys) pk =
      (simulateQ (findOracles tg)
        (simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) P)).run [] >>= fun z =>
          pure (z.1.1,
            decide ((tg[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2)) := by
  rw [hB]
  exact toDspr_guess B s tg ys pk

open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity in
/-- **Forge phase of the SM-TCR adversary `toTcr (bOpenPreS A)`**: one run of the open program
`findOpen A pk ys` (secret oracle = the table, hash queries evaluated) under the opening
simulation; the output is forwarded. -/
theorem toTcr_bOpenPreS_forge (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pk : prims.PkSeed) :
    (toTcr (Lazy.bOpenPreS A)).forge (tbl, tg, ys) pk =
      (simulateQ (findOracles tg)
        (simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (findOpen A pk ys))).run [] >>=
          fun z => pure z.1 :=
  fors_toTcr_forge_of (Lazy.bOpenPreS A) tbl tg ys pk tbl _ (findOpen_tbl_bOpenPreS A tbl pk ys)

open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity in
/-- **Guess phase of the SM-DSPR adversary `toDspr (bOpenPreS A)`**: the same single run of
`findOpen A pk ys`, then one comparison and one list-membership test. -/
theorem toDspr_bOpenPreS_guess (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pk : prims.PkSeed) :
    (toDspr (Lazy.bOpenPreS A)).guess (tbl, tg, ys) pk =
      (simulateQ (findOracles tg)
        (simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (findOpen A pk ys))).run [] >>=
          fun z => pure (z.1.1,
            decide ((tg[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2)) :=
  fors_toDspr_guess_of (Lazy.bOpenPreS A) tbl tg ys pk tbl _ (findOpen_tbl_bOpenPreS A tbl pk ys)

/-! ## 5. The answer extraction as an open program, and the full `find` phase -/

/-- Open form of `openPreAnswer`: `H_msg` once for the forgery, once per signed message (to
recompute the opened leaves), and one `F` query per FORS tree of the forgery (all `k`; the pure
`openPreAnswer` stops at the first hit). -/
def findAnswerO (pk : PublicKeyCore prims.core) (ys : List prims.Y) (log : G2Log prims)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y) := do
  let digest ← PublicHash.hmsg prims.core sig.randomness pk.pkSeed pk.pkRoot msg
  let parts : DigestParts vp.params := splitDigest vp.params digest
  let opened ← (G2Log.signed log).mapM fun e => do
    let d ← PublicHash.hmsg prims.core e.2 pk.pkSeed pk.pkRoot e.1
    pure (forsIndices vp (splitDigest vp.params d))
  let imgs ← Vector.ofFnM fun i : Fin vp.params.k =>
    PublicHash.f prims.core pk.pkSeed (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i))
      (sig.fors[i.val]).sk
  return ((List.finRange vp.params.k).findSome? fun i =>
    if (parts.forsAdrs, leafIndex parts i) ∉ opened.flatten ∧
        imgs[i.val] = leafImage (vp := vp) ys
          (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)) then
      some (leafTarget vp prims (forsNodeAdrs parts.forsAdrs 0 (leafIndex parts i)),
        (sig.fors[i.val]).sk)
    else none).getD (0, default)

theorem findAnswerO_tbl (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core)
    (ys : List prims.Y) (log : G2Log prims) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (findAnswerO pk ys log msg sig) = pure (openPreAnswer pk ys log msg sig) := by
  have hf : ∀ (a : Adrs) (y : prims.Y), (Lazy.tblHom (gspec := forsG prims) tbl).toMonadHom
      (PublicHash.f prims.core pk.pkSeed a y) = pure (prims.F pk.pkSeed a y) := fun a y =>
    (Lazy.tblHom (gspec := forsG prims) tbl).map_query' _
  have hm : ∀ (R : prims.Y) (m : List Byte),
      simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot m) =
      pure (prims.Hmsg R pk.pkSeed pk.pkRoot m) := fun R m =>
    (Lazy.tblHom (gspec := forsG prims) tbl).map_query' _
  have hopened : ∀ l : List (List Byte × prims.Y),
      simulateQ (Lazy.tblImpl (gspec := forsG prims) (PublicHash.impl prims) tbl)
        (l.mapM fun e => do
          let d ← PublicHash.hmsg prims.core e.2 pk.pkSeed pk.pkRoot e.1
          pure (forsIndices vp (splitDigest vp.params d))) =
      pure (l.map fun e => forsIndices vp (digestParts pk e.2 e.1)) := by
    intro l
    induction l with
    | nil => simp
    | cons e l ih =>
      rw [List.mapM_cons, simulateQ_bind, simulateQ_bind, hm, pure_bind, simulateQ_pure,
        pure_bind, simulateQ_bind, ih, pure_bind, simulateQ_pure]
      rfl
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
  unfold findAnswerO
  rw [simulateQ_bind, hm, pure_bind, simulateQ_bind, hopened, pure_bind, simulateQ_bind, himgs,
    pure_bind, simulateQ_pure]
  unfold openPreAnswer openedLeaves digestParts
  simp only [Vector.getElem_ofFn, List.flatMap_def]

theorem fors_qb_mapM {κ' : Type} {spec : OracleSpec κ'} (p : κ' → Prop) [DecidablePred p]
    {α β : Type} (f : α → OracleComp spec β) (c : ℕ) (h : ∀ a, IsQueryBoundP (f a) p c) :
    ∀ l : List α, IsQueryBoundP (l.mapM f) p (l.length * c)
  | [] => by
      rw [List.mapM_nil]
      exact isQueryBoundP_pure _ _ _
  | a :: l => by
      rw [List.mapM_cons]
      refine (Lazy.qb_bind p (h a) fun b => Lazy.qb_bind p (m := 0) (fors_qb_mapM p f c h l)
        fun bs => isQueryBoundP_pure _ _ _).mono ?_
      rw [List.length_cons, Nat.succ_mul]
      omega

/-- Queries of `findAnswerO`: `c·(1 + |log| + k)` with `c = 1` for the hash kind, `0` for the
opening and secret kinds. -/
theorem findAnswerO_kindBound (K : Lazy.Kind) (pk : PublicKeyCore prims.core)
    (ys : List prims.Y) (log : G2Log prims) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    IsQueryBoundP (findAnswerO pk ys log msg sig) (fun t => Lazy.kind t = K)
      (Lazy.ind K .hash + log.length * Lazy.ind K .hash + vp.params.k * Lazy.ind K .hash) := by
  have hm : ∀ (R : prims.Y) (m : List Byte),
      IsQueryBoundP (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot m :
      OracleComp (Lazy.OSpec prims (forsG prims)) _) (fun t => Lazy.kind t = K)
        (Lazy.ind K .hash) :=
    fun _ _ => Lazy.query_kindBound K _
  have hl : (G2Log.signed log).length = log.length := List.length_map _
  unfold findAnswerO
  refine (Lazy.qb_bind _ (hm _ _) fun digest =>
    Lazy.qb_bind _ (fors_qb_mapM _ _ (Lazy.ind K .hash) (fun e =>
        Lazy.qb_bind _ (m := 0) (hm _ _) fun d => isQueryBoundP_pure _ _ _)
        (G2Log.signed log)) fun opened =>
      Lazy.qb_bind _ (m := 0) (Lazy.qb_ofFnM _ _ (Lazy.ind K .hash) fun i =>
          Lazy.query_kindBound K _) fun imgs => isQueryBoundP_pure _ _ _).mono ?_
  rw [hl]
  omega

/-- **The full open program of the `find` phase**: `findOpen` with the answer extraction also
expressed by hash queries.  Every hash evaluation of the `find` phase is a hash query of this
program. -/
noncomputable def findOpenFull (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed)
    (ys : List prims.Y) : OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y) := do
  let root ← Lazy.openKeygen prims (forsG prims) pkSeed
  let z ← runForgerLog A ⟨pkSeed, root⟩ lazyRandomizerLift (forsSignOpen ⟨pkSeed, root⟩ ys)
  findAnswerO ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2

/-- **The full open program is the `find` phase** (for every table sampler `my`). -/
theorem findOpenFull_tbl (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (findOpenFull A pkSeed ys) =
      (bOpenPreWith my A).find tbl pkSeed ys := by
  unfold findOpenFull
  rw [simulateQ_bind, Lazy.openKeygen_tbl, pure_bind, simulateQ_bind]
  have hrun := fors_runForgerLog_tbl A tbl ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩
    (gspec := forsG prims) lazyRandomizerLift
    (forsSignOpen ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ ys)
    lazyRandomizerLift
    (Reduction.openSign ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ tbl ys)
    (fun log m a => Lazy.simulateQ_tblImpl_liftM (PublicHash.impl prims) tbl
      (lazyRandomizer log m a))
    (fun m R => forsSignOpen_tbl tbl ⟨pkSeed, idealRoot vp prims tbl pkSeed⟩ ys m R)
  rw [hrun]
  simp only [findAnswerO_tbl]
  rfl

/-- `findOpenFull_tbl` at the sparse-table adversary `Lazy.bOpenPreS A`. -/
theorem findOpenFull_tbl_bOpenPreS (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (findOpenFull A pkSeed ys) =
      (Lazy.bOpenPreS A).find tbl pkSeed ys :=
  findOpenFull_tbl _ A tbl pkSeed ys

/-- The transcript of a forger with at most `qs` signing queries has at most `qs` entries. -/
theorem fors_log_length {ι : Type} {spec : OracleSpec ι}
    (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pk : PublicKeyCore prims.core)
    (rand : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (sign : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    ∀ z ∈ support (runForgerLog A pk rand sign), z.2.length ≤ qs := by
  intro z hz
  have h := (hA pk).cost_le_of_mem_support_run_simulateQ
    (impl := (QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT (G2Log prims) (OracleComp (unifSpec + spec))) +
      logSignOracle optRand pk rand sign) List.length
    (fun t ht s w hw => by
      cases t with
      | inl n => simp at ht
      | inr m =>
        simp [logSignOracle] at hw
        obtain ⟨a, _, R, _, sg, _, rfl⟩ := hw
        simp)
    (fun t ht s w hw => by
      cases t with
      | inl n =>
        simp at hw
        obtain ⟨x, _, rfl⟩ := hw
        simp
      | inr m => simp at ht) [] z hz
  simpa using h

/-- **Queries of kind `K` of `findOpenFull`**, for a forger with at most `qs` signing
queries. -/
theorem findOpenFull_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Lazy.Kind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (findOpenFull A pkSeed ys) (fun t => Lazy.kind t = K)
      (Lazy.keygenB vp (Lazy.ind K .sec) (Lazy.ind K .hash) +
        qs * forsSignB vp (Lazy.ind K .game) (Lazy.ind K .sec) (Lazy.ind K .hash) +
        (Lazy.ind K .hash + qs * Lazy.ind K .hash + vp.params.k * Lazy.ind K .hash)) := by
  unfold findOpenFull
  refine (isQueryBoundP_bind (Lazy.openKeygen_kindBound K pkSeed) fun root _ =>
    isQueryBoundP_bind
      (m := Lazy.ind K .hash + qs * Lazy.ind K .hash + vp.params.k * Lazy.ind K .hash)
      (findRun_kindBound A K hK qs hA pkSeed ys root) fun z hz =>
      (findAnswerO_kindBound K ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2).mono ?_).mono (by omega)
  have hlen := fors_log_length A qs hA ⟨pkSeed, root⟩ lazyRandomizerLift
    (forsSignOpen ⟨pkSeed, root⟩ ys) z hz
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) _) _

/-- **Hash evaluations of the whole `find` phase**: key generation, `qs` simulated signatures,
and the answer extraction (`1 + qs + k`). -/
theorem findOpenFull_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (findOpenFull A pkSeed ys) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * forsSignHashes vp + (1 + qs + vp.params.k)) :=
  (findOpenFull_kindBound A .hash (by decide) qs hA pkSeed ys).mono
    (Nat.add_le_add (Nat.add_le_add Lazy.keygenB_hash (Nat.mul_le_mul_left _ (by
      simpa [Lazy.ind] using forsSignB_hash (vp := vp)))) (by simp [Lazy.ind]))

/-- **Opening queries of the whole `find` phase**: `k` per simulated signature. -/
theorem findOpenFull_openings (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (findOpenFull A pkSeed ys) (fun t => Lazy.kind t = .game)
      (qs * vp.params.k) :=
  (findOpenFull_kindBound A .game (by decide) qs hA pkSeed ys).mono
    (by simp [Lazy.ind, Lazy.keygenB_game, forsSignB_game])

/-- **Secret (table) reads of the whole `find` phase**: WOTS+ start values only. -/
theorem findOpenFull_reads (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (findOpenFull A pkSeed ys) (fun t => Lazy.kind t = .sec)
      (2 ^ vp.params.hp * vp.params.len +
        qs * (vp.params.d * (2 ^ vp.params.hp * vp.params.len))) :=
  (findOpenFull_kindBound A .sec (by decide) qs hA pkSeed ys).mono (by
    have h1 := Lazy.keygenB_sec (vp := vp)
    have h2 := Nat.mul_le_mul_left qs (forsSignB_sec (vp := vp))
    simp only [Lazy.ind, reduceCtorEq, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    omega)

/-- Hash evaluations of the whole `find` phase at SLH-DSA-SHA2-128s:
`269839 + qs · 1950028`. -/
theorem findOpenFull_hashes_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pkSeed : Link.prims.PkSeed) (ys : List Link.prims.Y) :
    IsQueryBoundP (findOpenFull A pkSeed ys) (fun t => Lazy.kind t = .hash)
      (269839 + qs * 1950028) := by
  have h := findOpenFull_hashes A qs hA pkSeed ys
  rw [forsSignHashes_128s, show Lazy.keygenHashes Link.vp = 269824 by decide,
    show Link.vp.params.k = 14 by decide] at h
  exact h.mono (by omega)

open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity in
/-- **Forge phase of the SM-TCR adversary `toTcr (bOpenPreS A)`** as one run of the full open
program `findOpenFull A pk ys` under the opening simulation. -/
theorem toTcr_bOpenPreS_forge_full (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pk : prims.PkSeed) :
    (toTcr (Lazy.bOpenPreS A)).forge (tbl, tg, ys) pk =
      (simulateQ (findOracles tg)
        (simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl)
          (findOpenFull A pk ys))).run [] >>= fun z => pure z.1 :=
  fors_toTcr_forge_of (Lazy.bOpenPreS A) tbl tg ys pk tbl _
    (findOpenFull_tbl_bOpenPreS A tbl pk ys)

open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity in
/-- **Guess phase of the SM-DSPR adversary `toDspr (bOpenPreS A)`** as one run of the full open
program, then one comparison and one list-membership test (no hash evaluation). -/
theorem toDspr_bOpenPreS_guess_full (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pk : prims.PkSeed) :
    (toDspr (Lazy.bOpenPreS A)).guess (tbl, tg, ys) pk =
      (simulateQ (findOracles tg)
        (simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl)
          (findOpenFull A pk ys))).run [] >>= fun z => pure (z.1.1,
            decide ((tg[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2)) :=
  fors_toDspr_guess_of (Lazy.bOpenPreS A) tbl tg ys pk tbl _
    (findOpenFull_tbl_bOpenPreS A tbl pk ys)

end Resources2
end Reduction

#print axioms Reduction.Resources2.findOpen_tbl
#print axioms Reduction.Resources2.findOpen_tbl_bOpenPreS
#print axioms Reduction.Resources2.findOpen_kindBound
#print axioms Reduction.Resources2.findOpen_hashes
#print axioms Reduction.Resources2.findOpen_openings
#print axioms Reduction.Resources2.findOpen_reads
#print axioms Reduction.Resources2.findOpen_hashes_128s
#print axioms Reduction.Resources2.toTcr_bOpenPreS_forge
#print axioms Reduction.Resources2.toDspr_bOpenPreS_guess
#print axioms Reduction.Resources2.findOpenFull_tbl
#print axioms Reduction.Resources2.findOpenFull_tbl_bOpenPreS
#print axioms Reduction.Resources2.findOpenFull_kindBound
#print axioms Reduction.Resources2.findOpenFull_hashes
#print axioms Reduction.Resources2.findOpenFull_openings
#print axioms Reduction.Resources2.findOpenFull_reads
#print axioms Reduction.Resources2.findOpenFull_hashes_128s
#print axioms Reduction.Resources2.toTcr_bOpenPreS_forge_full
#print axioms Reduction.Resources2.toDspr_bOpenPreS_guess_full
