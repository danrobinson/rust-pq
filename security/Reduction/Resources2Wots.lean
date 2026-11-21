import Reduction.Lazy.WotsSparse
import Reduction.Lazy.ItsrLazy
import Reduction.WotsFinal
import Reduction.Resources

/-!
# Own hash evaluations of phase 2 of `rUd` / `rPre` / `rTcr` at `bWotsS A`

Phase 2 (after the public seed is revealed) of the SM-UD / SM-PRE / SM-TCR adversaries
`rUd pkSeedDist W`, `rPre pkSeedDist W`, `rTcr pkSeedDist W` is `W.forge` followed by a pure tail
(`wots_rUd_distinguish_eq`, `wots_rPre_invert_eq`, `wots_rTcr_forge_eq`, all `rfl`).  For
`W = Lazy.bWotsWith my A` (in particular `Lazy.bWotsS A`) this file exhibits phase 2 as the
interpretation `simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) P` of an *open program*
`P : OracleComp (Lazy.OSpec prims gspec) _` (any game spec `gspec`; phase 2 has no oracle) in
which every hash evaluation that is counted is an explicit query of kind `.hash` and every read
of the (FORS part of the) table an explicit query of kind `.sec`, and bounds these queries.

## What is formal

* `wotsSignFromHistO hist pk msg R` — the open signer: `H_msg` is an `hmsg` query, FORS signing
  is `forsSignWithSecret` at `PublicHash.f/h` and `Lazy.secQ`, and per hypertree layer the
  authentication path over the leaves `T_len(recorded chain ends)` at `PublicHash.tl/h`; the
  WOTS+ signatures are read from the history (no chain step).
  `wotsSignFromHistO_tbl`: under the table it is `pure (signFromHist tbl hist pk msg R)`.
* `wots_runForgerLog_pure_eq_liftM_g2RunWith` (generic in `spec`, `signR`):
  `runForgerLog A pk lazyRandomizerLift (fun m R => pure (signR m R)) = liftM (g2RunWith A pk signR)`;
  `wots_runForgerLog_tbl`: `Lazy.runForgerLog_tbl` for an arbitrary game spec.
* `wotsForgeOpen A hist root pkSeed` and `wotsForgeOpen_tbl`: its interpretation is
  `liftM (g2RunWith A ⟨pkSeed, root⟩ (signFromHist tbl hist ⟨pkSeed, root⟩))`.
* Counting (`hA : ∀ pk, IsQueryBoundP (A.main pk) (·.isRight = true) qs`):
  `wotsForgeOpen_hashes` (`≤ qs · wotsSignHistHashes vp`,
  `wotsSignHistHashes vp = 1 + k·(2^a·2) + d·(2^h'·2)`, `= 121857` at 128s),
  `wotsForgeOpen_reads` (`≤ qs · k · 2^a` table reads), `wotsForgeOpen_game` (`0`).
* Tails as open programs, with `…_tbl` (interpretation = `pure` of the pure tail) and
  `…_kindBound`: `wotsWinO` (`WotsGame.win`, `≤ wotsWinHashes vp = len·(w-1)`, 525 at 128s),
  `wotsPreAnswerO` (`preAnswer`, `≤ wotsPreHashes vp = len·((w-1)+1)`, 560),
  `wotsTcrAnswerO` (`tcrAnswer`, `≤ wotsTcrHashes vp = len·((w-1)·(2·(w-1)+2))`, 16800).
* Assembly: `wotsPhase2O A tbl hist root pk tail`, `wotsPhase2O_tbl`, `wotsPhase2O_kindBound`,
  and for the three adversaries `wots_r{Ud,Pre,Tcr}_phase2_eq` (generic sampler `my`),
  `wots_r{Ud,Pre,Tcr}_bWotsS_phase2_eq` (headline terms) and `wots_r{Ud,Pre,Tcr}_phase2_hashes`:
  `≤ qs · wotsSignHistHashes vp + wots{Win,Pre,Tcr}Hashes vp` hash queries; no game query
  (`wotsPhase2O_game`).

## What is NOT counted formally (counting argument only)

* `wotsAnswer tbl hist pk msg sig` is kept as a pure function inside `wotsPhase2O` (it is applied
  once, to the forgery).  Its hash evaluations: `digestParts` (1 `H_msg`); one more
  `signFromHist` (`≤ wotsSignHistHashes vp`); `forsPkFromSig` of the forged and of the reference
  signature (`2·(k·(1+a)+1)`); and `wotsLayer?` / `layerMsg` / `layerTops`, which is two
  hypertree root recoveries (forged and reference), `2·d·(len·(w-1) + 1 + h')` when the layer
  messages are memoised (`layerTops` at layer `j` is the chain completion already done for
  `layerMsg (j+1)`).  Total `≤ 1 + wotsSignHistHashes + 2·(k·(1+a)+1) + 2·d·(len·(w-1)+1+h')`
  (`= 1 + 121857 + 366 + 7490 = 129714` at 128s).  Evaluated literally as written (`layerMsg` is
  recomputed from layer 0 for every `j`) the last term is multiplied by at most `d + 1`.
* The uniform-bit queries (forger's coins, `optRand`, fresh randomizers) and the forger's own
  computation.
* `wotsTcrAnswerO` recomputes each chain prefix for every step `t` exactly as `tcrAnswer` is
  written; an incremental evaluation would need only `len·2·(w-1)` + `len·2·(w-1)` calls.
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
variable {ι : Type} {gspec : OracleSpec ι}

attribute [local instance] Lazy.openQ Lazy.closedQ

/-! ## 1. The open signer -/

/-- The monad morphism `Id → n` (`pure`). -/
def wotsIdHom (n : Type → Type) [Monad n] [LawfulMonad n] : Id →ᵐ n where
  toFun {_} x := pure (Id.run x)
  toFun_pure' _ := rfl
  toFun_bind' x f := by simp

theorem wots_ofFnM_pure {n : Type → Type} [Monad n] [LawfulMonad n] {α : Type} {k : ℕ}
    (f : Fin k → α) : Vector.ofFnM (fun i => (pure (f i) : n α)) = pure (Vector.ofFn f) :=
  Vector.ofFnM_pure_comp (m := n) (f := f)

/-- `signFromHist` as an open program: `H_msg`, `F`, `H`, `T_len` are hash queries, FORS secrets
are read through `Lazy.secQ`; the WOTS+ signatures and chain ends come from the history. -/
def wotsSignFromHistO (hist : List (WotsGame.Entry prims)) (pk : PublicKeyCore prims.core)
    (msg : List Byte) (R : prims.Y) :
    OracleComp (Lazy.OSpec prims gspec) (GeneralScheme.SignatureCore vp prims.core) := do
  let digest ← PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot msg
  let parts : DigestParts vp.params := splitDigest vp.params digest
  let forsSig ← forsSignWithSecret prims.core (PublicHash.f prims.core pk.pkSeed)
    (PublicHash.h prims.core pk.pkSeed) (Lazy.secQ prims gspec) parts.md.toList parts.forsAdrs
  let ht ← Vector.ofFnM fun j : Fin vp.params.d => do
    let path ← PerfectMerkleTree.intrinsicAuthPathM
      (fun t => PublicHash.tl prims.core pk.pkSeed
        (wotsPkAdrs (wotsLeafAdrs (LayerPosition.atLayer vp parts j).toAdrs t))
        (histEntry hist (wotsLeafAdrs (LayerPosition.atLayer vp parts j).toAdrs t)).2.2.2.toList)
      (xmssNodeHashWith (PublicHash.h prims.core pk.pkSeed)
        (LayerPosition.atLayer vp parts j).toAdrs)
      (LayerPosition.atLayer vp parts j).leaf.val vp.params.hp
    pure (⟨(histEntry hist (wotsInstanceAdrs (LayerPosition.atLayer vp parts j))).2.2.1, path⟩ :
      XmssSig vp.params prims.core)
  return ⟨R, forsSig, ht⟩

theorem wotsSignFromHistO_tbl (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte) (R : prims.Y) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsSignFromHistO hist pk msg R) =
      pure (signFromHist tbl hist pk msg R) := by
  have hf : ∀ (a : Adrs) (y : prims.Y), (Lazy.tblHom (gspec := gspec) tbl).toMonadHom
      (PublicHash.f prims.core pk.pkSeed a y) = pure (prims.F pk.pkSeed a y) := fun a y =>
    (Lazy.tblHom (gspec := gspec) tbl).map_query' _
  have hh : ∀ (a : Adrs) (l r : prims.Y), (Lazy.tblHom (gspec := gspec) tbl).toMonadHom
      (PublicHash.h prims.core pk.pkSeed a l r) = pure (prims.H pk.pkSeed a l r) := fun a l r =>
    (Lazy.tblHom (gspec := gspec) tbl).map_query' _
  have htl : ∀ (a : Adrs) (xs : List prims.Y), (Lazy.tblHom (gspec := gspec) tbl).toMonadHom
      (PublicHash.tl prims.core pk.pkSeed a xs) = pure (prims.Tl pk.pkSeed a xs) := fun a xs =>
    (Lazy.tblHom (gspec := gspec) tbl).map_query' _
  have hJ := forsSignWithSecret_natural prims.core (wotsIdHom (OracleComp (unifSpec + gspec)))
    (fun a x => prims.F pk.pkSeed a x) (fun a x => pure (prims.F pk.pkSeed a x))
    (fun a l r => prims.H pk.pkSeed a l r) (fun a l r => pure (prims.H pk.pkSeed a l r))
    (fun a => secretOf vp prims tbl a) (fun a => pure (secretOf vp prims tbl a))
    (fun a y => rfl) (fun a l r => rfl) (fun a _ => rfl)
  have hfors : ∀ (md : List Byte) (adrs : Adrs),
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (forsSignWithSecret prims.core (PublicHash.f prims.core pk.pkSeed)
          (PublicHash.h prims.core pk.pkSeed) (Lazy.secQ prims gspec) md adrs) =
      pure (forsSignWithSecret prims.core (fun a x => prims.F pk.pkSeed a x)
        (fun a l r => prims.H pk.pkSeed a l r) (fun a => secretOf vp prims tbl a)
        md adrs : Id (ForsSigCore vp.params prims.core)) := fun md adrs =>
    (forsSignWithSecret_natural prims.core (Lazy.tblHom (gspec := gspec) tbl).toMonadHom
      _ _ _ _ (Lazy.secQ prims gspec) (fun a => pure (secretOf vp prims tbl a)) hf hh
      (fun a _ => Lazy.simulateQ_tblImpl_secQ tbl a) md adrs).trans (hJ md adrs).symm
  have hauth : ∀ (pos : LayerPosition vp),
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (PerfectMerkleTree.intrinsicAuthPathM
          (fun t => PublicHash.tl prims.core pk.pkSeed (wotsPkAdrs (wotsLeafAdrs pos.toAdrs t))
            (histEntry hist (wotsLeafAdrs pos.toAdrs t)).2.2.2.toList)
          (xmssNodeHashWith (PublicHash.h prims.core pk.pkSeed) pos.toAdrs)
          pos.leaf.val vp.params.hp) =
      pure (Id.run (PerfectMerkleTree.intrinsicAuthPathM
          (fun t => (pure (prims.Tl pk.pkSeed (wotsPkAdrs (wotsLeafAdrs pos.toAdrs t))
            (histEntry hist (wotsLeafAdrs pos.toAdrs t)).2.2.2.toList) : Id prims.Y))
          (xmssNodeHashWith (fun a l r => (pure (prims.H pk.pkSeed a l r) : Id prims.Y))
            pos.toAdrs)
          pos.leaf.val vp.params.hp)) := fun pos =>
    (PerfectMerkleTree.intrinsicAuthPathM_natural (Lazy.tblHom (gspec := gspec) tbl).toMonadHom
      _ _ (fun t => pure (prims.Tl pk.pkSeed (wotsPkAdrs (wotsLeafAdrs pos.toAdrs t))
            (histEntry hist (wotsLeafAdrs pos.toAdrs t)).2.2.2.toList))
      (xmssNodeHashWith (fun a l r => pure (prims.H pk.pkSeed a l r)) pos.toAdrs)
      (fun t => htl _ _) (fun z t l r => hh _ l r) _ _).trans
    (PerfectMerkleTree.intrinsicAuthPathM_natural (wotsIdHom (OracleComp (unifSpec + gspec)))
      (fun t => (pure (prims.Tl pk.pkSeed (wotsPkAdrs (wotsLeafAdrs pos.toAdrs t))
            (histEntry hist (wotsLeafAdrs pos.toAdrs t)).2.2.2.toList) : Id prims.Y))
      (xmssNodeHashWith (fun a l r => (pure (prims.H pk.pkSeed a l r) : Id prims.Y))
            pos.toAdrs) _ _
      (fun t => rfl) (fun z t l r => rfl) _ _).symm
  have hm : simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot msg) =
      pure (prims.Hmsg R pk.pkSeed pk.pkRoot msg) :=
    (Lazy.tblHom (gspec := gspec) tbl).map_query' _
  unfold wotsSignFromHistO
  rw [simulateQ_bind, hm, pure_bind, simulateQ_bind, hfors, pure_bind, simulateQ_bind]
  have hvec : ∀ parts : DigestParts vp.params,
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (Vector.ofFnM fun j : Fin vp.params.d => do
          let path ← PerfectMerkleTree.intrinsicAuthPathM
            (fun t => PublicHash.tl prims.core pk.pkSeed
              (wotsPkAdrs (wotsLeafAdrs (LayerPosition.atLayer vp parts j).toAdrs t))
              (histEntry hist
                (wotsLeafAdrs (LayerPosition.atLayer vp parts j).toAdrs t)).2.2.2.toList)
            (xmssNodeHashWith (PublicHash.h prims.core pk.pkSeed)
              (LayerPosition.atLayer vp parts j).toAdrs)
            (LayerPosition.atLayer vp parts j).leaf.val vp.params.hp
          pure (⟨(histEntry hist
            (wotsInstanceAdrs (LayerPosition.atLayer vp parts j))).2.2.1, path⟩ :
              XmssSig vp.params prims.core)) =
      pure (Vector.ofFn fun j : Fin vp.params.d =>
        (⟨(histEntry hist (wotsInstanceAdrs (LayerPosition.atLayer vp parts j))).2.2.1,
          Id.run (PerfectMerkleTree.intrinsicAuthPathM
            (fun t => (pure (prims.Tl pk.pkSeed
              (wotsPkAdrs (wotsLeafAdrs (LayerPosition.atLayer vp parts j).toAdrs t))
              (histEntry hist
                (wotsLeafAdrs (LayerPosition.atLayer vp parts j).toAdrs t)).2.2.2.toList) :
                  Id prims.Y))
            (xmssNodeHashWith (fun a l r => (pure (prims.H pk.pkSeed a l r) : Id prims.Y))
              (LayerPosition.atLayer vp parts j).toAdrs)
            (LayerPosition.atLayer vp parts j).leaf.val vp.params.hp)⟩ :
              XmssSig vp.params prims.core)) := fun parts =>
    (Vector.ofFnM_natural (Lazy.tblHom (gspec := gspec) tbl).toMonadHom _ _ (fun j => by
      refine (simulateQ_bind _ _ _).trans ?_
      rw [hauth, pure_bind]
      exact simulateQ_pure _ _)).trans (wots_ofFnM_pure _)
  rw [hvec, pure_bind, simulateQ_pure]
  rfl

/-! ## 2. Running the forger -/

theorem wots_logImpl_run_eq {ι' : Type} {spec : OracleSpec ι'} (pk : PublicKeyCore prims.core)
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core) {α : Type}
    (oa : OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) α)
    (log : G2Log prims) :
    StateT.run (simulateQ
      (((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
          (StateT (G2Log prims) (OracleComp (unifSpec + spec))) +
        logSignOracle (spec := spec) optRand pk lazyRandomizerLift (fun m R => pure (signR m R)) :
          QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
            (StateT (G2Log prims) (OracleComp (unifSpec + spec))))) oa) log =
      (liftM (StateT.run (simulateQ
        ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (G2Log prims) ProbComp) +
          g2SignOracle optRand pk signR) oa) log) : OracleComp (unifSpec + spec) _) := by
  induction oa using OracleComp.inductionOn generalizing log with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, liftM_bind]
    cases t with
    | inl n =>
      simp [ih]
      rfl
    | inr m =>
      simp [logSignOracle, g2SignOracle, lazyRandomizerLift, ih]

theorem wots_runForgerLog_pure_eq_liftM_g2RunWith {ι' : Type} {spec : OracleSpec ι'}
    (A : Forger vp prims optRand pkSeedDist) (pk : PublicKeyCore prims.core)
    (signR : List Byte → prims.Y → GeneralScheme.SignatureCore vp prims.core) :
    runForgerLog (spec := spec) A pk lazyRandomizerLift (fun m R => pure (signR m R)) =
      (liftM (g2RunWith A pk signR) : OracleComp (unifSpec + spec) _) :=
  wots_logImpl_run_eq pk signR (A.main pk) []

/-- `Lazy.runForgerLog_tbl` for an arbitrary game spec. -/
theorem wots_runForgerLog_tbl (A : Forger vp prims optRand pkSeedDist) (g : SecretTable vp prims)
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

/-- Phase 2 of `bWotsWith my A` before the final extraction, as an open program: the forger is
run once, its signing queries being answered by `wotsSignFromHistO`. -/
noncomputable def wotsForgeOpen (A : Forger vp prims optRand pkSeedDist)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pkSeed : prims.PkSeed) :
    OracleComp (Lazy.OSpec prims gspec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  runForgerLog A ⟨pkSeed, root⟩ lazyRandomizerLift (wotsSignFromHistO hist ⟨pkSeed, root⟩)

theorem wotsForgeOpen_tbl (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pkSeed : prims.PkSeed) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsForgeOpen A hist root pkSeed) =
      (liftM (g2RunWith A ⟨pkSeed, root⟩ (signFromHist tbl hist ⟨pkSeed, root⟩)) :
        OracleComp (unifSpec + gspec) _) :=
  (wots_runForgerLog_tbl A tbl ⟨pkSeed, root⟩ _ _ lazyRandomizerLift
    (fun m R => pure (signFromHist tbl hist ⟨pkSeed, root⟩ m R))
    (fun log m a => Lazy.simulateQ_tblImpl_liftM (PublicHash.impl prims) tbl _)
    (fun m R => wotsSignFromHistO_tbl tbl hist ⟨pkSeed, root⟩ m R)).trans
  (wots_runForgerLog_pure_eq_liftM_g2RunWith A ⟨pkSeed, root⟩ _)

/-! ## 3. Counting -/

/-- Budget of one `wotsSignFromHistO`: `cS` per secret read, `c` per hash evaluation. -/
def wotsSignHistB (vp : ValidatedParams) (cS c : ℕ) : ℕ :=
  c + vp.params.k * (cS + Lazy.authB (cS + c) c vp.params.a) +
    vp.params.d * Lazy.authB c c vp.params.hp

theorem wotsSignFromHistO_kindBound (K : Lazy.Kind) (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte) (R : prims.Y) :
    IsQueryBoundP (wotsSignFromHistO (gspec := gspec) hist pk msg R) (fun t => Lazy.kind t = K)
      (wotsSignHistB vp (Lazy.ind K .sec) (Lazy.ind K .hash)) := by
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
  have hs : ∀ a : Adrs, IsQueryBoundP (Lazy.secQ prims gspec a) (fun t => Lazy.kind t = K)
      (Lazy.ind K .sec) :=
    fun _ => Lazy.query_kindBound K _
  have hm : IsQueryBoundP (PublicHash.hmsg prims.core R pk.pkSeed pk.pkRoot msg :
      OracleComp (Lazy.OSpec prims gspec) _) (fun t => Lazy.kind t = K) (Lazy.ind K .hash) :=
    Lazy.query_kindBound K _
  unfold wotsSignFromHistO
  refine (Lazy.qb_bind _ hm fun digest =>
    Lazy.qb_bind _ (Lazy.qb_forsSign _ prims.core _ _ _ hf hh hs _ _) fun forsSig =>
      Lazy.qb_bind _ (m := 0) (Lazy.qb_ofFnM _ _ _ fun j =>
        Lazy.qb_bind _ (m := 0) (Lazy.qb_authPath _ _ _ _ _ _ _ (fun t => htl _ _)
          (fun z t l r => hh _ l r)) fun path => isQueryBoundP_pure _ _ _)
        fun ht => isQueryBoundP_pure _ _ _).mono ?_
  unfold wotsSignHistB
  simp only [Nat.add_zero]
  omega

/-- Queries of kind `K` (game / secret / hash) of `wotsForgeOpen`, for a forger with at most
`qs` signing queries. -/
theorem wotsForgeOpen_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Lazy.Kind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (wotsForgeOpen (gspec := gspec) A hist root pkSeed) (fun t => Lazy.kind t = K)
      (qs * wotsSignHistB vp (Lazy.ind K .sec) (Lazy.ind K .hash)) := by
  unfold wotsForgeOpen runForgerLog
  refine IsQueryBoundP.simulateQ_run_of_step_le (hA _) (fun t ht s => ?_) (fun t ht s => ?_) []
  · cases t with
    | inl n => simp at ht
    | inr m =>
      have hstep := Lazy.qb_bind (fun t => Lazy.kind t = K)
        (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
          (hspec := publicHashSpec prims.core) K hK (optRand ⟨pkSeed, root⟩)) fun addrnd =>
        Lazy.qb_bind (fun t => Lazy.kind t = K)
          (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
            (hspec := publicHashSpec prims.core) K hK (lazyRandomizer s m addrnd)) fun R =>
          Lazy.qb_bind (fun t => Lazy.kind t = K) (m := 0)
            (wotsSignFromHistO_kindBound (gspec := gspec) K hist ⟨pkSeed, root⟩ m R)
            fun sig => isQueryBoundP_pure _ (sig, s ++ [(m, addrnd, R)]) _
      simpa [logSignOracle, lazyRandomizerLift] using hstep
  · cases t with
    | inl n =>
      simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
      have h0 := Lazy.qb_bind (fun t => Lazy.kind t = K) (m := 0)
        (Lazy.liftM_kindBound (gspec := gspec) (D := SecIdx) (V := prims.Y)
          (hspec := publicHashSpec prims.core) K hK
          (liftM (unifSpec.query n) : ProbComp _)) fun x => isQueryBoundP_pure _ (x, s) _
      exact h0
    | inr m => simp at ht

/-- Hash evaluations of one history-based signature: one `H_msg`; FORS signing (`k` trees of
`2^a` leaf hashes and nodes); per hypertree layer the authentication path over the `2^h'`
leaves `T_len(recorded chain ends)` (`≤ 2^h'` calls `T_len` and `≤ 2^h'` node hashes).  No chain
step. -/
def wotsSignHistHashes (vp : ValidatedParams) : ℕ :=
  1 + vp.params.k * (2 ^ vp.params.a * 2) + vp.params.d * (2 ^ vp.params.hp * 2)

theorem wotsSignHistB_hash : wotsSignHistB vp 0 1 ≤ wotsSignHistHashes vp := by
  have h1 := Lazy.authB_add 1 1 vp.params.a
  have h2 := Lazy.authB_add 1 1 vp.params.hp
  unfold wotsSignHistB wotsSignHistHashes
  simp only [Nat.zero_add]
  refine Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)
    (Nat.mul_le_mul_left _ (by omega))

theorem wotsSignHistB_ind_hash :
    wotsSignHistB vp (Lazy.ind .hash .sec) (Lazy.ind .hash .hash) ≤ wotsSignHistHashes vp := by
  simpa [Lazy.ind] using wotsSignHistB_hash (vp := vp)

theorem wotsSignHistB_sec : wotsSignHistB vp 1 0 ≤ vp.params.k * 2 ^ vp.params.a := by
  have h1 := Lazy.authB_add 1 0 vp.params.a
  unfold wotsSignHistB
  simp only [Lazy.authB_zero, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  exact Nat.mul_le_mul_left _ (by omega)

theorem wotsSignHistB_game : wotsSignHistB vp 0 0 = 0 := by
  simp [wotsSignHistB, Lazy.authB_zero]

/-- **Own hash evaluations of phase 2**: at most `qs · wotsSignHistHashes vp`. -/
theorem wotsForgeOpen_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (wotsForgeOpen (gspec := gspec) A hist root pkSeed)
      (fun t => Lazy.kind t = .hash) (qs * wotsSignHistHashes vp) :=
  (wotsForgeOpen_kindBound A .hash (by decide) qs hA hist root pkSeed).mono
    (Nat.mul_le_mul_left _ (by simpa [Lazy.ind] using wotsSignHistB_hash (vp := vp)))

/-- Secret (FORS table) reads of phase 2: at most `qs · k · 2^a`. -/
theorem wotsForgeOpen_reads (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (wotsForgeOpen (gspec := gspec) A hist root pkSeed)
      (fun t => Lazy.kind t = .sec) (qs * (vp.params.k * 2 ^ vp.params.a)) :=
  (wotsForgeOpen_kindBound A .sec (by decide) qs hA hist root pkSeed).mono
    (Nat.mul_le_mul_left _ (by simpa [Lazy.ind] using wotsSignHistB_sec (vp := vp)))

/-- Phase 2 makes no game query. -/
theorem wotsForgeOpen_game (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (wotsForgeOpen (gspec := gspec) A hist root pkSeed)
      (fun t => Lazy.kind t = .game) 0 :=
  (wotsForgeOpen_kindBound A .game (by decide) qs hA hist root pkSeed).mono
    (by simp [Lazy.ind, wotsSignHistB_game])

theorem wotsSignHistHashes_128s : wotsSignHistHashes Link.vp = 121857 := by decide

/-! ## 4. The pure tails, as open programs -/

theorem wots_mapM_tbl {α β : Type} (tbl : SecretTable vp prims) (l : List α)
    (f : α → OracleComp (Lazy.OSpec prims gspec) β) (g : α → β)
    (h : ∀ x, simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) (f x) =
      pure (g x)) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) (l.mapM f) =
      pure (l.map g) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.mapM_cons, h, ih]

theorem wots_qb_mapM {κ' : Type} {spec : OracleSpec κ'} (p : κ' → Prop) [DecidablePred p]
    {α β : Type} (l : List α) (f : α → OracleComp spec β) (c : ℕ)
    (h : ∀ x ∈ l, IsQueryBoundP (f x) p c) : IsQueryBoundP (l.mapM f) p (l.length * c) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.mapM_cons]
    refine (Lazy.qb_bind p (h a (List.mem_cons_self ..)) fun y =>
      Lazy.qb_bind p (m := 0) (ih fun x hx => h x (List.mem_cons_of_mem _ hx)) fun ys =>
        isQueryBoundP_pure _ _ _).mono ?_
    simp [Nat.succ_mul]
    omega

/-- A chain, each step a hash query. -/
def wotsChainO (pk : prims.PkSeed) (a : Adrs) (x : prims.Y) (i s : ℕ) :
    OracleComp (Lazy.OSpec prims gspec) prims.Y :=
  chainM prims.core pk a x i s

theorem wotsChainO_tbl (tbl : SecretTable vp prims) (pk : prims.PkSeed) (a : Adrs) (x : prims.Y)
    (i s : ℕ) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (wotsChainO pk a x i s) = pure (chain prims pk a x i s) := by
  have h1 := chainM_natural prims.core (Lazy.tblHom (gspec := gspec) tbl) pk a x i s
  have h2 := chainM_natural prims.core
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
      (m := OracleComp (unifSpec + gspec))) pk a x i s
  rw [Lazy.free_apply] at h2
  exact h1.trans h2.symm

theorem wotsChainO_kindBound (K : Lazy.Kind) (pk : prims.PkSeed) (a : Adrs) (x : prims.Y)
    (i s : ℕ) :
    IsQueryBoundP (wotsChainO (gspec := gspec) pk a x i s) (fun t => Lazy.kind t = K)
      (s * Lazy.ind K .hash) :=
  Lazy.qb_chain _ prims.core _ (fun _ _ => Lazy.query_kindBound K _) a x i s

/-- One `F` evaluation, as a hash query. -/
def wotsFO (pk : prims.PkSeed) (a : Adrs) (x : prims.Y) :
    OracleComp (Lazy.OSpec prims gspec) prims.Y :=
  PublicHash.f prims.core pk a x

theorem wotsFO_tbl (tbl : SecretTable vp prims) (pk : prims.PkSeed) (a : Adrs) (x : prims.Y) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) (wotsFO pk a x) =
      pure (prims.F pk a x) :=
  (Lazy.tblHom (gspec := gspec) tbl).map_query' _

theorem wotsFO_kindBound (K : Lazy.Kind) (pk : prims.PkSeed) (a : Adrs) (x : prims.Y) :
    IsQueryBoundP (wotsFO (gspec := gspec) pk a x) (fun t => Lazy.kind t = K)
      (Lazy.ind K .hash) :=
  Lazy.query_kindBound K _

/-! ### `WotsGame.win` -/

/-- `WotsGame.win` with the chain completions as hash queries. -/
def wotsWinO (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) : OracleComp (Lazy.OSpec prims gspec) Bool :=
  match hist[j]? with
  | none => pure false
  | some (a, m, _, tops) => do
    let t ← wotsPkFromSigTopsM prims.core sig' m' pk a
    pure (decide (m' ≠ m ∧ t = tops))

theorem wotsWinO_tbl (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (wotsWinO pk hist j m' sig') = pure (WotsGame.win pk hist j m' sig') := by
  have ht : ∀ a, simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (wotsPkFromSigTopsM prims.core sig' m' pk a) =
      pure (wotsPkFromSigTops prims sig' m' pk a) := fun a => by
    have h1 := wotsPkFromSigTopsM_natural prims.core (Lazy.tblHom (gspec := gspec) tbl)
      sig' m' pk a
    have h2 := wotsPkFromSigTopsM_natural prims.core
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core)
        (m := OracleComp (unifSpec + gspec))) sig' m' pk a
    rw [Lazy.free_apply] at h2
    exact h1.trans h2.symm
  unfold wotsWinO WotsGame.win
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · simp
  · simp [ht]

theorem wotsWinO_kindBound (K : Lazy.Kind) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) :
    IsQueryBoundP (wotsWinO (gspec := gspec) pk hist j m' sig') (fun t => Lazy.kind t = K)
      (vp.params.len * ((vp.params.w - 1) * Lazy.ind K .hash)) := by
  unfold wotsWinO
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · exact (Lazy.qb_bind _ (m := 0) (Lazy.qb_ofFnM _ _ ((vp.params.w - 1) * Lazy.ind K .hash) fun i =>
      (Lazy.qb_chain _ prims.core _ (fun _ _ => Lazy.query_kindBound K _) _ _ _ _).mono
        (Nat.mul_le_mul_right _ (Nat.sub_le _ _))) fun t => isQueryBoundP_pure _ _ _).mono
      (by omega)

/-! ### `preAnswer` -/

/-- `preAnswer` with every chain step and `F` call a hash query. -/
def wotsPreAnswerO (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ)
    (m' : prims.Y) (sig' : WotsSig vp.params prims.core) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × prims.Y) :=
  match hist[j]? with
  | none => pure (0, default)
  | some (a, m, sig, _) => do
    let ys ← (List.finRange vp.params.len).mapM fun i => do
      let x ← wotsChainO pk (wotsChainAdrs a i.val) sig'[i.val]
        (chainStepsCore prims.core m' i.val)
        (chainStepsCore prims.core m i.val - 1 - chainStepsCore prims.core m' i.val)
      let y ← wotsFO pk ((wotsChainAdrs a i.val).setHashAddress
        (chainStepsCore prims.core m i.val - 1)) x
      pure (i, x, y)
    pure ((ys.findSome? fun z =>
      if chainStepsCore prims.core m' z.1.val < chainStepsCore prims.core m z.1.val ∧
          z.2.2 = sig[z.1.val] then
        some (preTargetIndex hist j z.1.val, z.2.1)
      else none).getD (0, default))

theorem wotsPreAnswerO_tbl (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (wotsPreAnswerO pk hist j m' sig') = pure (preAnswer pk hist j m' sig') := by
  unfold wotsPreAnswerO preAnswer
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · simp
  · dsimp only
    rw [simulateQ_bind, wots_mapM_tbl tbl _ _ (fun i => (i,
        chain prims pk (wotsChainAdrs a i.val) sig'[i.val] (chainStepsCore prims.core m' i.val)
          (chainStepsCore prims.core m i.val - 1 - chainStepsCore prims.core m' i.val),
        prims.F pk ((wotsChainAdrs a i.val).setHashAddress (chainStepsCore prims.core m i.val - 1))
          (chain prims pk (wotsChainAdrs a i.val) sig'[i.val]
            (chainStepsCore prims.core m' i.val)
            (chainStepsCore prims.core m i.val - 1 - chainStepsCore prims.core m' i.val))))
      (fun i => by
        rw [simulateQ_bind, wotsChainO_tbl, pure_bind, simulateQ_bind, wotsFO_tbl, pure_bind,
          simulateQ_pure]),
      pure_bind, simulateQ_pure, List.findSome?_map]
    rfl

theorem wotsPreAnswerO_kindBound (K : Lazy.Kind) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) :
    IsQueryBoundP (wotsPreAnswerO (gspec := gspec) pk hist j m' sig') (fun t => Lazy.kind t = K)
      (vp.params.len * ((vp.params.w - 1) * Lazy.ind K .hash + Lazy.ind K .hash)) := by
  unfold wotsPreAnswerO
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · refine (Lazy.qb_bind _ (m := 0) (wots_qb_mapM _ _ _ _ fun i _ =>
      Lazy.qb_bind _ ((wotsChainO_kindBound K _ _ _ _ _).mono
        (Nat.mul_le_mul_right _ (?_ : _ ≤ vp.params.w - 1))) fun x =>
        Lazy.qb_bind _ (m := 0) (wotsFO_kindBound K _ _ _) fun y => isQueryBoundP_pure _ _ _)
      fun ys => isQueryBoundP_pure _ _ _).mono (by simp)
    have := chainStepsCore_le prims.core m i.val
    omega

/-! ### `tcrAnswer` -/

/-- `tcrAnswer` with every chain step and `F` call a hash query. -/
def wotsTcrAnswerO (pk : prims.PkSeed) (hist : List (WotsGame.Entry prims)) (j : ℕ)
    (m' : prims.Y) (sig' : WotsSig vp.params prims.core) :
    OracleComp (Lazy.OSpec prims gspec) (ℕ × prims.Y) :=
  match hist[j]? with
  | none => pure (0, default)
  | some (a, m, sig, _) => do
    let ys ← (List.finRange vp.params.len).mapM fun i => do
      let zs ← (List.range (vp.params.w - 1)).mapM fun t => do
        let fv ← wotsChainO pk (wotsChainAdrs a i.val) sig'[i.val]
          (chainStepsCore prims.core m' i.val) (t - chainStepsCore prims.core m' i.val)
        let hv ← wotsChainO pk (wotsChainAdrs a i.val) sig[i.val]
          (chainStepsCore prims.core m i.val) (t - chainStepsCore prims.core m i.val)
        let y1 ← wotsFO pk ((wotsChainAdrs a i.val).setHashAddress t) fv
        let y2 ← wotsFO pk ((wotsChainAdrs a i.val).setHashAddress t) hv
        pure (t, fv, hv, y1, y2)
      pure (i, zs)
    pure ((ys.findSome? fun z =>
      z.2.findSome? fun u =>
        if chainStepsCore prims.core m z.1.val ≤ u.1 ∧
            chainStepsCore prims.core m' z.1.val ≤ u.1 ∧ u.2.1 ≠ u.2.2.1 ∧
            u.2.2.2.1 = u.2.2.2.2 then
          some (tcrTargetIndex hist j z.1.val u.1, u.2.1)
        else none).getD (0, default))

theorem wotsTcrAnswerO_tbl (tbl : SecretTable vp prims) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
      (wotsTcrAnswerO pk hist j m' sig') = pure (tcrAnswer pk hist j m' sig') := by
  unfold wotsTcrAnswerO tcrAnswer
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · simp
  · dsimp only
    rw [simulateQ_bind, wots_mapM_tbl tbl _ _ (fun i => (i,
        (List.range (vp.params.w - 1)).map fun t =>
          (t,
            chain prims pk (wotsChainAdrs a i.val) sig'[i.val]
              (chainStepsCore prims.core m' i.val) (t - chainStepsCore prims.core m' i.val),
            chain prims pk (wotsChainAdrs a i.val) sig[i.val]
              (chainStepsCore prims.core m i.val) (t - chainStepsCore prims.core m i.val),
            prims.F pk ((wotsChainAdrs a i.val).setHashAddress t)
              (chain prims pk (wotsChainAdrs a i.val) sig'[i.val]
                (chainStepsCore prims.core m' i.val) (t - chainStepsCore prims.core m' i.val)),
            prims.F pk ((wotsChainAdrs a i.val).setHashAddress t)
              (chain prims pk (wotsChainAdrs a i.val) sig[i.val]
                (chainStepsCore prims.core m i.val) (t - chainStepsCore prims.core m i.val)))))
      (fun i => by
        rw [simulateQ_bind, wots_mapM_tbl tbl _ _ _ (fun t => by
          rw [simulateQ_bind, wotsChainO_tbl, pure_bind, simulateQ_bind, wotsChainO_tbl,
            pure_bind, simulateQ_bind, wotsFO_tbl, pure_bind, simulateQ_bind, wotsFO_tbl,
            pure_bind, simulateQ_pure]), pure_bind, simulateQ_pure]),
      pure_bind, simulateQ_pure, List.findSome?_map]
    simp only [Function.comp_def, List.findSome?_map]

theorem wotsTcrAnswerO_kindBound (K : Lazy.Kind) (pk : prims.PkSeed)
    (hist : List (WotsGame.Entry prims)) (j : ℕ) (m' : prims.Y)
    (sig' : WotsSig vp.params prims.core) :
    IsQueryBoundP (wotsTcrAnswerO (gspec := gspec) pk hist j m' sig') (fun t => Lazy.kind t = K)
      (vp.params.len * ((vp.params.w - 1) *
        ((vp.params.w - 1) * Lazy.ind K .hash + ((vp.params.w - 1) * Lazy.ind K .hash +
          (Lazy.ind K .hash + Lazy.ind K .hash))))) := by
  unfold wotsTcrAnswerO
  rcases hist[j]? with _ | ⟨a, m, sig, tops⟩
  · exact (isQueryBoundP_pure _ _ _).mono (Nat.zero_le _)
  · refine (Lazy.qb_bind _ (m := 0) (wots_qb_mapM _ _ _ _ fun i _ =>
      Lazy.qb_bind _ (m := 0) (wots_qb_mapM _ _ _ _ fun t ht =>
        Lazy.qb_bind _ ((wotsChainO_kindBound K _ _ _ _ _).mono
          (Nat.mul_le_mul_right _ (?_ : _ ≤ vp.params.w - 1))) fun fv =>
        Lazy.qb_bind _ ((wotsChainO_kindBound K _ _ _ _ _).mono
          (Nat.mul_le_mul_right _ (?_ : _ ≤ vp.params.w - 1))) fun hv =>
        Lazy.qb_bind _ (wotsFO_kindBound K _ _ _) fun y1 =>
        Lazy.qb_bind _ (m := 0) (wotsFO_kindBound K _ _ _) fun y2 =>
          isQueryBoundP_pure _ _ _) fun zs => isQueryBoundP_pure _ _ _)
      fun ys => isQueryBoundP_pure _ _ _).mono (by simp)
    · have := List.mem_range.1 ht; omega
    · have := List.mem_range.1 ht; omega

/-! ## 5. Phase 2 of `rUd`, `rPre`, `rTcr` at `bWotsWith my A` / `bWotsS A` -/

theorem wots_rUd_distinguish_eq (W : WotsGame.Adversary prims)
    (st : W.State × List (WotsGame.Entry prims)) (pk : prims.PkSeed) :
    (rUd pkSeedDist W).distinguish st pk =
      W.forge st.1 pk >>= fun x => pure (WotsGame.win pk st.2 x.1 x.2.1 x.2.2) := rfl

theorem wots_rPre_invert_eq (W : WotsGame.Adversary prims)
    (st : W.State × List (WotsGame.Entry prims)) (pk : prims.PkSeed) :
    (rPre pkSeedDist W).invert st pk =
      W.forge st.1 pk >>= fun x => pure (preAnswer pk st.2 x.1 x.2.1 x.2.2) := rfl

theorem wots_rTcr_forge_eq (W : WotsGame.Adversary prims)
    (st : W.State × List (WotsGame.Entry prims)) (pk : prims.PkSeed) :
    (rTcr pkSeedDist W).forge st pk =
      W.forge st.1 pk >>= fun x => pure (tcrAnswer pk st.2 x.1 x.2.1 x.2.2) := rfl

theorem wots_bWotsWith_forge_eq (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    (Lazy.bWotsWith my A).forge (tbl, hist, root) pk =
      g2RunWith A ⟨pk, root⟩ (signFromHist tbl hist ⟨pk, root⟩) >>= fun r =>
        pure (wotsAnswer tbl hist ⟨pk, root⟩ r.1.1 r.1.2) := rfl

/-- Phase 2 as an open program: run the forger (`wotsForgeOpen`), extract the WOTS-game answer
(`wotsAnswer`, pure: see the module docstring), continue with the open tail `tail`. -/
noncomputable def wotsPhase2O (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β) :
    OracleComp (Lazy.OSpec prims gspec) β :=
  wotsForgeOpen A hist root pk >>= fun r => tail (wotsAnswer tbl hist ⟨pk, root⟩ r.1.1 r.1.2)

theorem wotsPhase2O_tbl (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β)
    (tailP : ℕ × prims.Y × WotsSig vp.params prims.core → β)
    (h : ∀ x, simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl) (tail x) =
      pure (tailP x)) :
    simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2O A tbl hist root pk tail) =
      (liftM ((Lazy.bWotsWith my A).forge (tbl, hist, root) pk >>= fun x => pure (tailP x)) :
        OracleComp (unifSpec + gspec) β) := by
  unfold wotsPhase2O
  rw [simulateQ_bind, wotsForgeOpen_tbl, wots_bWotsWith_forge_eq, bind_assoc, liftM_bind]
  refine bind_congr fun r => ?_
  rw [h, pure_bind]
  rfl

/-- The forge step alone (deliverable 4, first form). -/
theorem wots_bWotsWith_forge_open (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    (liftM ((Lazy.bWotsWith my A).forge (tbl, hist, root) pk) :
        OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsForgeOpen A hist root pk >>= fun r =>
          pure (wotsAnswer tbl hist ⟨pk, root⟩ r.1.1 r.1.2)) := by
  rw [simulateQ_bind, wotsForgeOpen_tbl, wots_bWotsWith_forge_eq, liftM_bind]
  refine bind_congr fun r => ?_
  rw [simulateQ_pure]
  rfl

theorem wotsPhase2O_kindBound (A : Forger vp prims optRand pkSeedDist) (K : Lazy.Kind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β)
    (c : ℕ) (htail : ∀ x, IsQueryBoundP (tail x) (fun t => Lazy.kind t = K) c) :
    IsQueryBoundP (wotsPhase2O A tbl hist root pk tail) (fun t => Lazy.kind t = K)
      (qs * wotsSignHistB vp (Lazy.ind K .sec) (Lazy.ind K .hash) + c) :=
  Lazy.qb_bind _ (wotsForgeOpen_kindBound A K hK qs hA hist root pk) fun r => htail _

/-- Hash evaluations of `WotsGame.win`: completing `len` chains. -/
def wotsWinHashes (vp : ValidatedParams) : ℕ := vp.params.len * (vp.params.w - 1)

/-- Hash evaluations of `preAnswer`: per chain at most `w - 1` chain steps and one `F`. -/
def wotsPreHashes (vp : ValidatedParams) : ℕ := vp.params.len * ((vp.params.w - 1) + 1)

/-- Hash evaluations of `tcrAnswer`: per chain and step `t < w - 1`, two chains of at most
`w - 1` steps and two `F`. -/
def wotsTcrHashes (vp : ValidatedParams) : ℕ :=
  vp.params.len * ((vp.params.w - 1) * (2 * (vp.params.w - 1) + 2))

/-! ### SM-UD -/

/-- Phase 2 of `rUd pkSeedDist (bWotsWith my A)` is the interpretation of an open program. -/
theorem wots_rUd_phase2_eq (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    (liftM ((rUd pkSeedDist (Lazy.bWotsWith my A)).distinguish ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) Bool) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2O A tbl hist root pk fun x => wotsWinO pk hist2 x.1 x.2.1 x.2.2) :=
  (wotsPhase2O_tbl my A tbl hist root pk _ (fun x => WotsGame.win pk hist2 x.1 x.2.1 x.2.2)
    (fun x => wotsWinO_tbl tbl pk hist2 x.1 x.2.1 x.2.2)).symm

theorem wots_rUd_phase2_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    IsQueryBoundP (wotsPhase2O (gspec := gspec) A tbl hist root pk
        fun x => wotsWinO pk hist2 x.1 x.2.1 x.2.2) (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp + wotsWinHashes vp) :=
  (wotsPhase2O_kindBound A .hash (by decide) qs hA tbl hist root pk _ _
    (fun x => wotsWinO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2)).mono
    (Nat.add_le_add (Nat.mul_le_mul_left _ wotsSignHistB_ind_hash) (by simp [Lazy.ind, wotsWinHashes]))

/-! ### SM-PRE -/

theorem wots_rPre_phase2_eq (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    (liftM ((rPre pkSeedDist (Lazy.bWotsWith my A)).invert ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2O A tbl hist root pk fun x => wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2) :=
  (wotsPhase2O_tbl my A tbl hist root pk _ (fun x => preAnswer pk hist2 x.1 x.2.1 x.2.2)
    (fun x => wotsPreAnswerO_tbl tbl pk hist2 x.1 x.2.1 x.2.2)).symm

theorem wots_rPre_phase2_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    IsQueryBoundP (wotsPhase2O (gspec := gspec) A tbl hist root pk
        fun x => wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2) (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp + wotsPreHashes vp) :=
  (wotsPhase2O_kindBound A .hash (by decide) qs hA tbl hist root pk _ _
    (fun x => wotsPreAnswerO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2)).mono
    (Nat.add_le_add (Nat.mul_le_mul_left _ wotsSignHistB_ind_hash) (by simp [Lazy.ind, wotsPreHashes]))

/-! ### SM-TCR -/

theorem wots_rTcr_phase2_eq (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (tbl : SecretTable vp prims)
    (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y) (pk : prims.PkSeed) :
    (liftM ((rTcr pkSeedDist (Lazy.bWotsWith my A)).forge ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2O A tbl hist root pk fun x => wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2) :=
  (wotsPhase2O_tbl my A tbl hist root pk _ (fun x => tcrAnswer pk hist2 x.1 x.2.1 x.2.2)
    (fun x => wotsTcrAnswerO_tbl tbl pk hist2 x.1 x.2.1 x.2.2)).symm

theorem wots_rTcr_phase2_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    IsQueryBoundP (wotsPhase2O (gspec := gspec) A tbl hist root pk
        fun x => wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2) (fun t => Lazy.kind t = .hash)
      (qs * wotsSignHistHashes vp + wotsTcrHashes vp) :=
  (wotsPhase2O_kindBound A .hash (by decide) qs hA tbl hist root pk _ _
    (fun x => wotsTcrAnswerO_kindBound .hash pk hist2 x.1 x.2.1 x.2.2)).mono
    (Nat.add_le_add (Nat.mul_le_mul_left _ wotsSignHistB_ind_hash) (by
      have h1 : Lazy.ind Lazy.Kind.hash Lazy.Kind.hash = 1 := rfl
      rw [h1, wotsTcrHashes]
      exact le_of_eq (by ring)))

/-- Phase 2 makes no game query and reads at most `qs·k·2^a` table cells, whatever the tail
(`wotsWinO`, `wotsPreAnswerO`, `wotsTcrAnswerO` make neither). -/
theorem wotsPhase2O_game (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) {β : Type}
    (tail : ℕ × prims.Y × WotsSig vp.params prims.core → OracleComp (Lazy.OSpec prims gspec) β)
    (htail : ∀ x, IsQueryBoundP (tail x) (fun t => Lazy.kind t = .game) 0) :
    IsQueryBoundP (wotsPhase2O A tbl hist root pk tail) (fun t => Lazy.kind t = .game) 0 :=
  (wotsPhase2O_kindBound A .game (by decide) qs hA tbl hist root pk tail 0 htail).mono
    (by simp [Lazy.ind, wotsSignHistB_game])

/-! ### The headline terms (`bWotsS A`) -/

theorem wots_bWotsS_forge_open (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((Lazy.bWotsS A).forge (tbl, hist, root) pk) : OracleComp (unifSpec + gspec) _) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsForgeOpen A hist root pk >>= fun r =>
          pure (wotsAnswer tbl hist ⟨pk, root⟩ r.1.1 r.1.2)) := by
  exact wots_bWotsWith_forge_open _ A tbl hist root pk

theorem wots_rUd_bWotsS_phase2_eq (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((rUd pkSeedDist (Lazy.bWotsS A)).distinguish ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) Bool) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2O A tbl hist root pk fun x => wotsWinO pk hist2 x.1 x.2.1 x.2.2) := by
  exact wots_rUd_phase2_eq _ A tbl hist hist2 root pk

theorem wots_rPre_bWotsS_phase2_eq (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((rPre pkSeedDist (Lazy.bWotsS A)).invert ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2O A tbl hist root pk fun x => wotsPreAnswerO pk hist2 x.1 x.2.1 x.2.2) := by
  exact wots_rPre_phase2_eq _ A tbl hist hist2 root pk

theorem wots_rTcr_bWotsS_phase2_eq (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (hist hist2 : List (WotsGame.Entry prims)) (root : prims.Y)
    (pk : prims.PkSeed) :
    (liftM ((rTcr pkSeedDist (Lazy.bWotsS A)).forge ((tbl, hist, root), hist2) pk) :
        OracleComp (unifSpec + gspec) (ℕ × prims.Y)) =
      simulateQ (Lazy.tblImpl (gspec := gspec) (PublicHash.impl prims) tbl)
        (wotsPhase2O A tbl hist root pk fun x => wotsTcrAnswerO pk hist2 x.1 x.2.1 x.2.2) := by
  exact wots_rTcr_phase2_eq _ A tbl hist hist2 root pk

/-! ### Numerals at SLH-DSA-SHA2-128s -/

theorem wotsWinHashes_128s : wotsWinHashes Link.vp = 525 := by decide
theorem wotsPreHashes_128s : wotsPreHashes Link.vp = 560 := by decide
theorem wotsTcrHashes_128s : wotsTcrHashes Link.vp = 16800 := by decide

end Resources2
end Reduction

#print axioms Reduction.Resources2.wotsSignFromHistO_tbl
#print axioms Reduction.Resources2.wots_runForgerLog_pure_eq_liftM_g2RunWith
#print axioms Reduction.Resources2.wotsForgeOpen_tbl
#print axioms Reduction.Resources2.wotsForgeOpen_hashes
#print axioms Reduction.Resources2.wotsForgeOpen_reads
#print axioms Reduction.Resources2.wotsForgeOpen_game
#print axioms Reduction.Resources2.wotsSignHistHashes_128s
#print axioms Reduction.Resources2.wots_bWotsS_forge_open
#print axioms Reduction.Resources2.wots_rUd_bWotsS_phase2_eq
#print axioms Reduction.Resources2.wots_rPre_bWotsS_phase2_eq
#print axioms Reduction.Resources2.wots_rTcr_bWotsS_phase2_eq
#print axioms Reduction.Resources2.wots_rUd_phase2_hashes
#print axioms Reduction.Resources2.wots_rPre_phase2_hashes
#print axioms Reduction.Resources2.wots_rTcr_phase2_hashes
#print axioms Reduction.Resources2.wotsPhase2O_game
#print axioms Reduction.Resources2.wots_rUd_distinguish_eq
#print axioms Reduction.Resources2.wots_rPre_invert_eq
#print axioms Reduction.Resources2.wots_rTcr_forge_eq
#print axioms Reduction.Resources2.wotsTcrHashes_128s
