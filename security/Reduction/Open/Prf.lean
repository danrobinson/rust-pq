/-
Work package OPEN (R1), part 2: the PRF distinguishers as open programs.

`bPrfOpen A`, `bPrfWOpen wO A : OracleComp (PSpec prims (prims.PkSeed × Adrs)) Bool`
(`PSpec prims D = unifSpec + ((D →ₒ prims.Y) + HSpec prims)`) are `bPrf A`, `bPrfW w A` with
EVERY `Thash`/`H_msg` evaluation (key generation, signing, final verification) a query to
`publicHashSpec prims.core`, and every `PRF_msg` evaluation a `.prfmsg` query.

* equations: `bPrfOpen_close`, `bPrfWOpen_close` (closing by `closeImpl` = forward uniform bits and
  the PRF-game oracle, answer `HSpec` by `HSpec.impl prims`), `bPrfCOpen_close`,
  `bPrfWCOpen_close` (the same behind the domain restriction);
* open final checks: `eufCheckOpen`/`eufCheckW`, `sufCheckOpen` (for `sufCheck`);
* counts by kind: `bPrfOpen_kindBound`, `bPrfWOpen_kindBound` and the corollaries
  `*_hashes`, `*_prfmsg`, `*_game`, with SHA2-128s numerals.
-/
import Reduction.Open.HSpec
import Reduction.Suf
import Reduction.TcrMemo
import Reduction.Instance128sV2

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Reduction
namespace Open

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

attribute [local instance] openQ closedQ

/-! ## The open programs -/

/-- Open key generation: secrets are PRF-game queries at `(PK.seed, ADRS)`, hashes are hash
queries. -/
def openKeygenP (prims : Primitives vp.params) (pkSeed : prims.PkSeed) :
    OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y :=
  GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
    (fun a => gameQ prims (pkSeed, a)) pkSeed

/-- Open signing at a supplied randomizer. -/
def openSignCoreP (prims : Primitives vp.params) (m : List Byte) (pkSeed : prims.PkSeed)
    (pkRoot R : prims.Y) :
    OracleComp (PSpec prims (prims.PkSeed × Adrs)) (GeneralScheme.SignatureCore vp prims.core) :=
  GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core
    (fun a => gameQ prims (pkSeed, a)) m pkSeed pkRoot R

/-- The open signing procedure: `opt_rand`, then `R` by ONE `.prfmsg` query, then open signing. -/
noncomputable def openSignP (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) (m : List Byte) :
    OracleComp (PSpec prims (prims.PkSeed × Adrs)) (GeneralScheme.SignatureCore vp prims.core) :=
  (liftM (optRand pk) : OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y) >>= fun addrnd =>
    prfMsgQ prims (prims.PkSeed × Adrs) skPrf addrnd m >>= fun R =>
      openSignCoreP prims m pk.pkSeed pk.pkRoot R

/-- Everything `bPrfOpen A` does after sampling `PK.seed`. -/
noncomputable def bRestOpen (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed) :
    OracleComp (PSpec prims (prims.PkSeed × Adrs)) Bool :=
  (liftM ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.SkPrf) >>= fun skPrf =>
    openKeygenP prims pkSeed >>= fun root =>
      runForger A ⟨pkSeed, root⟩ (openSignP optRand ⟨pkSeed, root⟩ skPrf) >>= fun z =>
        simulateQ (hashEmb prims (prims.PkSeed × Adrs))
          (GeneralScheme.verifyInternalM vp prims.core z.1.1 z.1.2 ⟨pkSeed, root⟩ :
            OracleComp (publicHashSpec prims.core) Bool) >>= fun v =>
          pure (decide (z.1.1 ∉ z.2) && v)

/-- **`bPrf A` as an open program**: every `Thash`/`H_msg` evaluation (incl. the final
verification) is a hash query, every `PRF_msg` evaluation a `.prfmsg` query. -/
noncomputable def bPrfOpen (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (PSpec prims (prims.PkSeed × Adrs)) Bool :=
  (liftM pkSeedDist : OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.PkSeed) >>=
    bRestOpen A

/-- An open final check: a program over the public hash collection. -/
abbrev OpenCheck (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  PublicKeyCore prims.core → List Byte × GeneralScheme.SignatureCore vp prims.core →
    SigLog vp prims → OracleComp (publicHashSpec prims.core) Bool

/-- Everything `bPrfWOpen wO A` does after sampling `PK.seed`. -/
noncomputable def bRestWOpen (wO : OpenCheck vp prims) (A : Forger vp prims optRand pkSeedDist)
    (pkSeed : prims.PkSeed) : OracleComp (PSpec prims (prims.PkSeed × Adrs)) Bool :=
  (liftM ($ᵗ prims.SkPrf : ProbComp prims.SkPrf) :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.SkPrf) >>= fun skPrf =>
    openKeygenP prims pkSeed >>= fun root =>
      runForgerSig A ⟨pkSeed, root⟩ (openSignP optRand ⟨pkSeed, root⟩ skPrf) >>= fun z =>
        simulateQ (hashEmb prims (prims.PkSeed × Adrs)) (wO ⟨pkSeed, root⟩ z.1 z.2)

/-- **`bPrfW w A` as an open program**, for an open form `wO` of the final check `w`. -/
noncomputable def bPrfWOpen (wO : OpenCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (PSpec prims (prims.PkSeed × Adrs)) Bool :=
  (liftM pkSeedDist : OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.PkSeed) >>=
    bRestWOpen wO A

/-- **`bPrfC A` as an open program**: the open program behind the open domain restriction. -/
noncomputable def bPrfCOpen (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (PSpec prims (prims.PkSeed × SkAdrs vp)) Bool :=
  simulateQ (restrictO (prims := prims) (skRestrict vp prims)) (bPrfOpen A)

/-- **`bPrfWC w A` as an open program.** -/
noncomputable def bPrfWCOpen (wO : OpenCheck vp prims) (A : Forger vp prims optRand pkSeedDist) :
    OracleComp (PSpec prims (prims.PkSeed × SkAdrs vp)) Bool :=
  simulateQ (restrictO (prims := prims) (skRestrict vp prims)) (bPrfWOpen wO A)

/-! ### Open final checks -/

/-- The open strong-unforgeability check: the log test, then open verification. -/
def sufCheckOpen : OpenCheck vp prims := fun pk f log =>
  letI := sigDecEq (vp := vp) (prims := prims)
  (GeneralScheme.verifyInternalM vp prims.core f.1 f.2 pk :
      OracleComp (publicHashSpec prims.core) Bool) >>= fun v =>
    pure (!SignatureAlg.signingLogContains log f.1 f.2 && v)

theorem sufCheckOpen_eq (pk : PublicKeyCore prims.core)
    (f : List Byte × GeneralScheme.SignatureCore vp prims.core) (log : SigLog vp prims) :
    simulateQ (PublicHash.impl prims) (sufCheckOpen pk f log) = sufCheck pk f log := by
  unfold sufCheckOpen sufCheck
  rw [simulateQ_bind]
  rfl

/-- The EUF-CMA check as a `WinCheck`: the message was never queried, and the pair verifies. -/
def eufCheckW : WinCheck vp prims := fun pk f log =>
  !log.wasQueried f.1 && GeneralScheme.verifyInternal vp prims f.1 f.2 pk

/-- The open EUF-CMA check. -/
def eufCheckOpen : OpenCheck vp prims := fun pk f log =>
  (GeneralScheme.verifyInternalM vp prims.core f.1 f.2 pk :
      OracleComp (publicHashSpec prims.core) Bool) >>= fun v =>
    pure (!log.wasQueried f.1 && v)

theorem eufCheckOpen_eq (pk : PublicKeyCore prims.core)
    (f : List Byte × GeneralScheme.SignatureCore vp prims.core) (log : SigLog vp prims) :
    simulateQ (PublicHash.impl prims) (eufCheckOpen pk f log) = eufCheckW pk f log := by
  unfold eufCheckOpen eufCheckW
  rw [simulateQ_bind]
  rfl

/-! ## Equations -/

theorem close_openKeygenP (pkSeed : prims.PkSeed) :
    simulateQ (closeImpl prims (prims.PkSeed × Adrs)) (openKeygenP prims pkSeed) =
      (GeneralScheme.keygenInternalWithSecretM (vp := vp) prims.core
        (fun a => PRFScheme.functionQuery (pkSeed, a)) pkSeed :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y) prims.Y) :=
  GeneralScheme.keygenInternalWithSecretM_natural (vp := vp) prims.core
    (closeHom prims (prims.PkSeed × Adrs))
    (fun a => gameQ prims (pkSeed, a)) (fun a => PRFScheme.functionQuery (pkSeed, a))
    (fun a _ => close_gameQ (pkSeed, a)) pkSeed

theorem close_openSignCoreP (m : List Byte) (pkSeed : prims.PkSeed) (pkRoot R : prims.Y) :
    simulateQ (closeImpl prims (prims.PkSeed × Adrs)) (openSignCoreP prims m pkSeed pkRoot R) =
      (GeneralScheme.signInternalWithSecretRandomizerM (vp := vp) prims.core
        (fun a => PRFScheme.functionQuery (pkSeed, a)) m pkSeed pkRoot R :
        OracleComp (PRFScheme.PRFOracleSpec (prims.PkSeed × Adrs) prims.Y)
          (GeneralScheme.SignatureCore vp prims.core)) :=
  GeneralScheme.signInternalWithSecretRandomizerM_natural (vp := vp) prims.core
    (closeHom prims (prims.PkSeed × Adrs))
    (fun a => gameQ prims (pkSeed, a)) (fun a => PRFScheme.functionQuery (pkSeed, a))
    (fun a _ => close_gameQ (pkSeed, a)) m pkSeed pkRoot R

theorem close_openSignP (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) (m : List Byte) :
    simulateQ (closeImpl prims (prims.PkSeed × Adrs)) (openSignP optRand pk skPrf m) =
      bSignC optRand pk skPrf m := by
  unfold openSignP bSignC
  simp only [simulateQ_bind]
  rw [close_liftM]
  refine bind_congr fun addrnd => ?_
  rw [close_prfMsgQ, pure_bind, close_openSignCoreP]

/-- Closing commutes with the harness. -/
theorem close_runForger {D : Type} (A : Forger vp prims optRand pkSeedDist)
    (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (PSpec prims D) (GeneralScheme.SignatureCore vp prims.core)) :
    simulateQ (closeImpl prims D) (runForger A pk sign) =
      runForger A pk (fun m => simulateQ (closeImpl prims D) (sign m)) := by
  unfold runForger
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  congr 2
  funext t
  cases t with
  | inl n =>
    refine StateT.ext fun s => ?_
    simp [QueryImpl.mapStateTBase]
    exact close_liftM (liftM (unifSpec.query n))
  | inr m =>
    refine StateT.ext fun s => ?_
    simp [QueryImpl.mapStateTBase, harnessSignOracle]

/-- Closing commutes with the signature-recording harness. -/
theorem close_runForgerSig {D : Type} (A : Forger vp prims optRand pkSeedDist)
    (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (PSpec prims D) (GeneralScheme.SignatureCore vp prims.core)) :
    simulateQ (closeImpl prims D) (runForgerSig A pk sign) =
      runForgerSig A pk (fun m => simulateQ (closeImpl prims D) (sign m)) := by
  unfold runForgerSig
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  congr 2
  funext t
  cases t with
  | inl n =>
    refine StateT.ext fun s => ?_
    simp [QueryImpl.mapStateTBase]
    exact close_liftM (liftM (unifSpec.query n))
  | inr m =>
    refine StateT.ext fun s => ?_
    simp [QueryImpl.mapStateTBase, sigSignOracle, appendLog]

/-- **R1, equation for `bPrf`.**  Forwarding uniform bits and the PRF-game oracle and answering
the hash interface by `HSpec.impl prims` turns the open program into `bPrf A`. -/
theorem bPrfOpen_close (A : Forger vp prims optRand pkSeedDist) :
    simulateQ (closeImpl prims (prims.PkSeed × Adrs)) (bPrfOpen A) = bPrf A := by
  rw [bPrf_eq_bRestC]
  unfold bPrfOpen
  rw [simulateQ_bind, close_liftM]
  refine bind_congr fun pkSeed => ?_
  unfold bRestOpen bRestC
  simp only [simulateQ_bind, simulateQ_pure]
  rw [close_liftM]
  refine bind_congr fun skPrf => ?_
  rw [close_openKeygenP]
  refine bind_congr fun root => ?_
  rw [close_runForger]
  have hs : (fun m => simulateQ (closeImpl prims (prims.PkSeed × Adrs))
      (openSignP optRand ⟨pkSeed, root⟩ skPrf m)) = bSignC optRand ⟨pkSeed, root⟩ skPrf :=
    funext fun m => close_openSignP _ _ _
  rw [hs]
  refine bind_congr fun z => ?_
  rw [close_hashEmb, pure_bind]
  rfl

/-- **R1, equation for `bPrfW w`**, for any open form `wO` of `w`. -/
theorem bPrfWOpen_close (w : WinCheck vp prims) (wO : OpenCheck vp prims)
    (hw : ∀ pk f log, simulateQ (PublicHash.impl prims) (wO pk f log) = w pk f log)
    (A : Forger vp prims optRand pkSeedDist) :
    simulateQ (closeImpl prims (prims.PkSeed × Adrs)) (bPrfWOpen wO A) = bPrfW w A := by
  rw [bPrfW_eq_bRestW]
  unfold bPrfWOpen
  rw [simulateQ_bind, close_liftM]
  refine bind_congr fun pkSeed => ?_
  unfold bRestWOpen bRestW
  simp only [simulateQ_bind]
  rw [close_liftM]
  refine bind_congr fun skPrf => ?_
  rw [close_openKeygenP]
  refine bind_congr fun root => ?_
  rw [close_runForgerSig]
  have hs : (fun m => simulateQ (closeImpl prims (prims.PkSeed × Adrs))
      (openSignP optRand ⟨pkSeed, root⟩ skPrf m)) = bSignW optRand ⟨pkSeed, root⟩ skPrf :=
    funext fun m => close_openSignP _ _ _
  rw [hs]
  refine bind_congr fun z => ?_
  rw [close_hashEmb, hw]

/-- **R1, equation for `bPrfW sufCheck`.** -/
theorem bPrfWOpen_close_suf (A : Forger vp prims optRand pkSeedDist) :
    simulateQ (closeImpl prims (prims.PkSeed × Adrs)) (bPrfWOpen sufCheckOpen A) =
      bPrfW sufCheck A :=
  bPrfWOpen_close sufCheck sufCheckOpen sufCheckOpen_eq A

/-- **R1, equation for `bPrfW eufCheckW`.** -/
theorem bPrfWOpen_close_euf (A : Forger vp prims optRand pkSeedDist) :
    simulateQ (closeImpl prims (prims.PkSeed × Adrs)) (bPrfWOpen eufCheckOpen A) =
      bPrfW eufCheckW A :=
  bPrfWOpen_close eufCheckW eufCheckOpen eufCheckOpen_eq A

/-- **R1, equation for `bPrfC`.** -/
theorem bPrfCOpen_close (A : Forger vp prims optRand pkSeedDist) :
    simulateQ (closeImpl prims (prims.PkSeed × SkAdrs vp)) (bPrfCOpen A) = bPrfC A := by
  unfold bPrfCOpen bPrfC
  rw [close_restrictO, bPrfOpen_close]

/-- **R1, equation for `bPrfWC w`**, for any open form `wO` of `w`. -/
theorem bPrfWCOpen_close (w : WinCheck vp prims) (wO : OpenCheck vp prims)
    (hw : ∀ pk f log, simulateQ (PublicHash.impl prims) (wO pk f log) = w pk f log)
    (A : Forger vp prims optRand pkSeedDist) :
    simulateQ (closeImpl prims (prims.PkSeed × SkAdrs vp)) (bPrfWCOpen wO A) = bPrfWC w A := by
  unfold bPrfWCOpen bPrfWC
  rw [close_restrictO, bPrfWOpen_close w wO hw]

/-- **R1, equation for `bPrfWC sufCheck`.** -/
theorem bPrfWCOpen_close_suf (A : Forger vp prims optRand pkSeedDist) :
    simulateQ (closeImpl prims (prims.PkSeed × SkAdrs vp)) (bPrfWCOpen sufCheckOpen A) =
      bPrfWC sufCheck A :=
  bPrfWCOpen_close sufCheck sufCheckOpen sufCheckOpen_eq A

/-! ## Counts -/

theorem openKeygenP_kindBound (K : HKind) (pkSeed : prims.PkSeed) :
    IsQueryBoundP (openKeygenP prims pkSeed) (fun t => hkind t = K)
      (Lazy.keygenB vp (hind K .game) (hind K .hash)) :=
  Lazy.qb_xmssNode (fun t => hkind t = K) prims.core (hind K .hash) (hind K .hash) (hind K .hash)
    (hind K .game)
    (hash := PublicHash.f prims.core pkSeed) (compress := PublicHash.tl prims.core pkSeed)
    (nodeHash := PublicHash.h prims.core pkSeed) (secret := fun a => gameQ prims (pkSeed, a))
    (fun _ _ => query_kindBound K _) (fun _ _ => query_kindBound K _)
    (fun _ _ _ => query_kindBound K _) (fun _ => query_kindBound K _) _ _ _

theorem openSignCoreP_kindBound (K : HKind) (msg : List Byte) (pkSeed : prims.PkSeed)
    (pkRoot R : prims.Y) :
    IsQueryBoundP (openSignCoreP prims msg pkSeed pkRoot R) (fun t => hkind t = K)
      (Lazy.signB vp (hind K .game) (hind K .hash)) := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pkSeed a y :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y) (fun t => hkind t = K)
      (hind K .hash) := fun _ _ => query_kindBound K _
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsQueryBoundP (PublicHash.tl prims.core pkSeed a ys :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y) (fun t => hkind t = K)
      (hind K .hash) := fun _ _ => query_kindBound K _
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pkSeed a l r :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) prims.Y) (fun t => hkind t = K)
      (hind K .hash) := fun _ _ _ => query_kindBound K _
  have hs : ∀ a : Adrs, IsQueryBoundP (gameQ prims (pkSeed, a)) (fun t => hkind t = K)
      (hind K .game) := fun _ => query_kindBound K _
  have hm : IsQueryBoundP (PublicHash.hmsg prims.core R pkSeed pkRoot msg :
      OracleComp (PSpec prims (prims.PkSeed × Adrs)) _) (fun t => hkind t = K) (hind K .hash) :=
    query_kindBound K _
  unfold openSignCoreP GeneralScheme.signInternalWithSecretRandomizerM
  refine (Lazy.qb_bind _ hm fun digest =>
    Lazy.qb_bind _ (Lazy.qb_forsSign _ prims.core _ _ _ hf hh hs _ _) fun forsSig =>
      Lazy.qb_bind _ (Lazy.qb_forsPk _ prims.core _ _ _ hf htl hh forsSig _ _) fun forsPk =>
        Lazy.qb_bind _ (m := 0) (Lazy.qb_signFromPos _ prims.core _ _ _ _ hf htl hh hs _ _ _ _ _)
          fun htSig => isQueryBoundP_pure _ _ _).mono ?_
  unfold Lazy.signB
  omega

theorem openSignP_kindBound (K : HKind) (hK : K ≠ .unif) (pk : PublicKeyCore prims.core)
    (skPrf : prims.SkPrf) (m : List Byte) :
    IsQueryBoundP (openSignP optRand pk skPrf m) (fun t => hkind t = K)
      (hind K .prfmsg + Lazy.signB vp (hind K .game) (hind K .hash)) := by
  have h := Lazy.qb_bind (fun t => hkind t = K)
    (liftM_kindBound (prims := prims) (D := prims.PkSeed × Adrs) K hK (optRand pk)) fun addrnd =>
      Lazy.qb_bind (fun t => hkind t = K)
        (prfMsgQ_kindBound (D := prims.PkSeed × Adrs) K skPrf addrnd m) fun R =>
          openSignCoreP_kindBound K m pk.pkSeed pk.pkRoot R
  rw [Nat.zero_add] at h
  exact h

/-- **The free verification program** (`H_msg`, FORS recovery, hypertree recovery) makes at most
`1 + verifyHashes vp` public-hash queries. -/
theorem verifyInternalM_bound (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core)
    (pk : PublicKeyCore prims.core) :
    IsQueryBoundP (GeneralScheme.verifyInternalM vp prims.core msg sig pk :
      OracleComp (publicHashSpec prims.core) Bool) (fun _ => True)
      (1 + Resources2.verifyHashes vp) := by
  have hf : ∀ (a : Adrs) (y : prims.core.Y), IsQueryBoundP (PublicHash.f prims.core pk.pkSeed a y :
      OracleComp (publicHashSpec prims.core) prims.Y) (fun _ => True) 1 :=
    fun a y => (PublicHash.f_isTotalQueryBound prims.core pk.pkSeed a y).isQueryBoundP
  have htl : ∀ (a : Adrs) (ys : List prims.core.Y),
      IsQueryBoundP (PublicHash.tl prims.core pk.pkSeed a ys :
      OracleComp (publicHashSpec prims.core) prims.Y) (fun _ => True) 1 :=
    fun a ys => (PublicHash.tl_isTotalQueryBound prims.core pk.pkSeed a ys).isQueryBoundP
  have hh : ∀ (a : Adrs) (l r : prims.core.Y),
      IsQueryBoundP (PublicHash.h prims.core pk.pkSeed a l r :
      OracleComp (publicHashSpec prims.core) prims.Y) (fun _ => True) 1 :=
    fun a l r => (PublicHash.h_isTotalQueryBound prims.core pk.pkSeed a l r).isQueryBoundP
  have hm : IsQueryBoundP (PublicHash.hmsg prims.core sig.randomness pk.pkSeed pk.pkRoot msg :
      OracleComp (publicHashSpec prims.core) _) (fun _ => True) 1 :=
    (PublicHash.hmsg_isTotalQueryBound prims.core _ _ _ _).isQueryBoundP
  unfold GeneralScheme.verifyInternalM GeneralHypertree.verifyM GeneralHypertree.pkFromSigM
    GeneralHypertree.recoverFromPositionM forsPkFromSigM
  refine (Lazy.qb_bind _ hm fun digest =>
    Lazy.qb_bind _ (Lazy.qb_forsPk (fun _ => True) prims.core 1 1 1 hf htl hh _ _ _) fun forsPk =>
      Lazy.qb_bind _ (m := 0)
        (Resources2.qb_recover (fun _ => True) prims.core 1 1 1 hf htl hh pk.pkSeed vp.params.d
          _ _ _ _) fun root => isQueryBoundP_pure _ _ _).mono ?_
  unfold Resources2.verifyHashes Lazy.xmssPkB
  simp only [Nat.mul_one]
  omega

theorem sufCheckOpen_bound (pk : PublicKeyCore prims.core)
    (f : List Byte × GeneralScheme.SignatureCore vp prims.core) (log : SigLog vp prims) :
    IsQueryBoundP (sufCheckOpen pk f log) (fun _ => True) (1 + Resources2.verifyHashes vp) :=
  Lazy.qb_bind _ (m := 0) (verifyInternalM_bound f.1 f.2 pk) fun v => isQueryBoundP_pure _ _ _

theorem eufCheckOpen_bound (pk : PublicKeyCore prims.core)
    (f : List Byte × GeneralScheme.SignatureCore vp prims.core) (log : SigLog vp prims) :
    IsQueryBoundP (eufCheckOpen pk f log) (fun _ => True) (1 + Resources2.verifyHashes vp) :=
  Lazy.qb_bind _ (m := 0) (verifyInternalM_bound f.1 f.2 pk) fun v => isQueryBoundP_pure _ _ _

/-- The harness run: `qs` open signatures. -/
theorem runForger_kindBound (A : Forger vp prims optRand pkSeedDist) (K : HKind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) :
    IsQueryBoundP (runForger A pk (openSignP optRand pk skPrf)) (fun t => hkind t = K)
      (qs * (hind K .prfmsg + Lazy.signB vp (hind K .game) (hind K .hash))) := by
  unfold runForger
  refine IsQueryBoundP.simulateQ_run_of_step_le (hA _) (fun t ht s => ?_) (fun t ht s => ?_) []
  · cases t with
    | inl n => simp at ht
    | inr m =>
      have hstep := Lazy.qb_bind (fun t => hkind t = K) (m := 0)
        (openSignP_kindBound (optRand := optRand) K hK pk skPrf m)
        fun sig => isQueryBoundP_pure _ (sig, s ++ [m]) _
      simpa [harnessSignOracle] using hstep
  · cases t with
    | inl n =>
      simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
      exact Lazy.qb_bind (fun t => hkind t = K) (m := 0)
        (liftM_kindBound (prims := prims) (D := prims.PkSeed × Adrs) K hK
          (liftM (unifSpec.query n) : ProbComp _)) fun x => isQueryBoundP_pure _ (x, s) _
    | inr m => simp at ht

theorem runForgerSig_kindBound (A : Forger vp prims optRand pkSeedDist) (K : HKind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pk : PublicKeyCore prims.core) (skPrf : prims.SkPrf) :
    IsQueryBoundP (runForgerSig A pk (openSignP optRand pk skPrf)) (fun t => hkind t = K)
      (qs * (hind K .prfmsg + Lazy.signB vp (hind K .game) (hind K .hash))) := by
  unfold runForgerSig
  refine IsQueryBoundP.simulateQ_run_of_step_le (hA _) (fun t ht s => ?_) (fun t ht s => ?_) []
  · cases t with
    | inl n => simp at ht
    | inr m =>
      have hstep := Lazy.qb_bind (fun t => hkind t = K) (m := 0)
        (openSignP_kindBound (optRand := optRand) K hK pk skPrf m)
        fun sig => isQueryBoundP_pure _ (sig, s ++ [⟨m, sig⟩]) _
      simpa [sigSignOracle, appendLog] using hstep
  · cases t with
    | inl n =>
      simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, StateT.run_monadLift]
      exact Lazy.qb_bind (fun t => hkind t = K) (m := 0)
        (liftM_kindBound (prims := prims) (D := prims.PkSeed × Adrs) K hK
          (liftM (unifSpec.query n) : ProbComp _)) fun x => isQueryBoundP_pure _ (x, s) _
    | inr m => simp at ht

/-- The per-kind budget of the open PRF distinguishers with a final check of `c` hash queries. -/
def prfB (vp : ValidatedParams) (K : HKind) (qs c : ℕ) : ℕ :=
  Lazy.keygenB vp (hind K .game) (hind K .hash) +
    qs * (hind K .prfmsg + Lazy.signB vp (hind K .game) (hind K .hash)) + hind K .hash * c

/-- **Queries of kind `K` of `bPrfOpen A`.** -/
theorem bPrfOpen_kindBound (A : Forger vp prims optRand pkSeedDist) (K : HKind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfOpen A) (fun t => hkind t = K)
      (prfB vp K qs (1 + Resources2.verifyHashes vp)) := by
  unfold bPrfOpen bRestOpen
  refine (Lazy.qb_bind _ (liftM_kindBound K hK pkSeedDist) fun pkSeed =>
    Lazy.qb_bind _ (liftM_kindBound K hK _) fun skPrf =>
      Lazy.qb_bind _ (openKeygenP_kindBound K pkSeed) fun root =>
        Lazy.qb_bind _ (runForger_kindBound A K hK qs hA _ skPrf) fun z =>
          Lazy.qb_bind _ (m := 0)
            (hashEmb_kindBound K (verifyInternalM_bound z.1.1 z.1.2 ⟨pkSeed, root⟩))
            fun v => isQueryBoundP_pure _ _ _).mono ?_
  unfold prfB
  omega

/-- **Queries of kind `K` of `bPrfWOpen wO A`**, for an open check of at most `c` hash queries. -/
theorem bPrfWOpen_kindBound (wO : OpenCheck vp prims) (c : ℕ)
    (hc : ∀ pk f log, IsQueryBoundP (wO pk f log) (fun _ => True) c)
    (A : Forger vp prims optRand pkSeedDist) (K : HKind)
    (hK : K ≠ .unif) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfWOpen wO A) (fun t => hkind t = K) (prfB vp K qs c) := by
  unfold bPrfWOpen bRestWOpen
  refine (Lazy.qb_bind _ (liftM_kindBound K hK pkSeedDist) fun pkSeed =>
    Lazy.qb_bind _ (liftM_kindBound K hK _) fun skPrf =>
      Lazy.qb_bind _ (openKeygenP_kindBound K pkSeed) fun root =>
        Lazy.qb_bind _ (runForgerSig_kindBound A K hK qs hA _ skPrf) fun z =>
          hashEmb_kindBound K (hc ⟨pkSeed, root⟩ z.1 z.2)).mono ?_
  unfold prfB
  omega

/-! ### Closed forms of the budget -/

theorem prfB_hash (qs c : ℕ) :
    prfB vp .hash qs c ≤ Lazy.keygenHashes vp + qs * Lazy.signHashes vp + c := by
  have h1 := Lazy.keygenB_hash (vp := vp)
  have h2 := Nat.mul_le_mul_left qs (Lazy.signB_hash (vp := vp))
  simp only [prfB, hind, ite_true, Nat.one_mul]
  simp only [show (HKind.hash = HKind.game) = False from by simp,
    show (HKind.hash = HKind.prfmsg) = False from by simp, ite_false, Nat.zero_add]
  omega

theorem prfB_prfmsg (qs c : ℕ) : prfB vp .prfmsg qs c = qs := by
  simp [prfB, hind, Lazy.keygenB_game, Lazy.signB_game]

theorem prfB_game (qs c : ℕ) :
    prfB vp .game qs c ≤ 2 ^ vp.params.hp * vp.params.len + qs * signReads vp := by
  have h1 := Lazy.keygenB_sec (vp := vp)
  have h2 := Nat.mul_le_mul_left qs (Lazy.signB_sec (vp := vp))
  simp only [prfB, hind, ite_true]
  simp only [show (HKind.game = HKind.hash) = False from by simp,
    show (HKind.game = HKind.prfmsg) = False from by simp, ite_false, Nat.zero_add,
    Nat.zero_mul, Nat.add_zero]
  omega

section Corollaries

variable (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
  (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)

include hA

/-- **R1, hash count of `bPrfOpen A`**: `Thash`+`H_msg` queries
`≤ keygenHashes + qs·signHashes + (1 + verifyHashes)`. -/
theorem bPrfOpen_hashes :
    IsQueryBoundP (bPrfOpen A) (fun t => hkind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp)) :=
  (bPrfOpen_kindBound A .hash (by decide) qs hA).mono (prfB_hash _ _)

/-- **R1, `PRF_msg` count of `bPrfOpen A`**: at most `qs`. -/
theorem bPrfOpen_prfmsg : IsQueryBoundP (bPrfOpen A) (fun t => hkind t = .prfmsg) qs :=
  (bPrfOpen_kindBound A .prfmsg (by decide) qs hA).mono (le_of_eq (prfB_prfmsg _ _))

/-- **R1, PRF-game count of `bPrfOpen A`**: as `bPrf_queryBound_exact`. -/
theorem bPrfOpen_game :
    IsQueryBoundP (bPrfOpen A) (fun t => hkind t = .game)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  (bPrfOpen_kindBound A .game (by decide) qs hA).mono (prfB_game _ _)

theorem bPrfCOpen_hashes :
    IsQueryBoundP (bPrfCOpen A) (fun t => hkind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp)) :=
  restrictO_kindBound _ _ (bPrfOpen_hashes A qs hA)

theorem bPrfCOpen_prfmsg : IsQueryBoundP (bPrfCOpen A) (fun t => hkind t = .prfmsg) qs :=
  restrictO_kindBound _ _ (bPrfOpen_prfmsg A qs hA)

theorem bPrfCOpen_game :
    IsQueryBoundP (bPrfCOpen A) (fun t => hkind t = .game)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  restrictO_kindBound _ _ (bPrfOpen_game A qs hA)

variable (wO : OpenCheck vp prims) (c : ℕ)
  (hc : ∀ pk f log, IsQueryBoundP (wO pk f log) (fun _ => True) c)

include hc

/-- **R1, hash count of `bPrfWOpen wO A`**: `≤ keygenHashes + qs·signHashes + c`. -/
theorem bPrfWOpen_hashes :
    IsQueryBoundP (bPrfWOpen wO A) (fun t => hkind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + c) :=
  (bPrfWOpen_kindBound wO c hc A .hash (by decide) qs hA).mono (prfB_hash _ _)

theorem bPrfWOpen_prfmsg : IsQueryBoundP (bPrfWOpen wO A) (fun t => hkind t = .prfmsg) qs :=
  (bPrfWOpen_kindBound wO c hc A .prfmsg (by decide) qs hA).mono (le_of_eq (prfB_prfmsg _ _))

theorem bPrfWOpen_game :
    IsQueryBoundP (bPrfWOpen wO A) (fun t => hkind t = .game)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  (bPrfWOpen_kindBound wO c hc A .game (by decide) qs hA).mono (prfB_game _ _)

theorem bPrfWCOpen_hashes :
    IsQueryBoundP (bPrfWCOpen wO A) (fun t => hkind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + c) :=
  restrictO_kindBound _ _ (bPrfWOpen_hashes A qs hA wO c hc)

theorem bPrfWCOpen_prfmsg : IsQueryBoundP (bPrfWCOpen wO A) (fun t => hkind t = .prfmsg) qs :=
  restrictO_kindBound _ _ (bPrfWOpen_prfmsg A qs hA wO c hc)

theorem bPrfWCOpen_game :
    IsQueryBoundP (bPrfWCOpen wO A) (fun t => hkind t = .game)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  restrictO_kindBound _ _ (bPrfWOpen_game A qs hA wO c hc)

end Corollaries

/-- **R1, hash count of the SUF distinguisher `bPrfWCOpen sufCheckOpen A`**: the same bound as
for EUF (`sufCheck` performs one verification; the log test does no hashing). -/
theorem bPrfWCOpen_suf_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfWCOpen sufCheckOpen A) (fun t => hkind t = .hash)
      (Lazy.keygenHashes vp + qs * Lazy.signHashes vp + (1 + Resources2.verifyHashes vp)) :=
  bPrfWCOpen_hashes A qs hA sufCheckOpen _ sufCheckOpen_bound

theorem bPrfWCOpen_suf_prfmsg (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfWCOpen sufCheckOpen A) (fun t => hkind t = .prfmsg) qs :=
  bPrfWCOpen_prfmsg A qs hA sufCheckOpen _ sufCheckOpen_bound

theorem bPrfWCOpen_suf_game (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfWCOpen sufCheckOpen A) (fun t => hkind t = .game)
      (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) :=
  bPrfWCOpen_game A qs hA sufCheckOpen _ sufCheckOpen_bound

end Open
end Reduction

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction
namespace Open

/-- Hash queries of `bPrfCOpen A` at SHA2-128s: `≤ 269824 + qs·2007385 + 3929`. -/
theorem bPrfCOpen_hashes_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfCOpen A) (fun t => hkind t = .hash) (269824 + qs * 2007385 + 3929) := by
  have h := bPrfCOpen_hashes A qs hA
  rwa [keygenHashes_128s, signHashes_128s, Resources2.verifyHashes_128s] at h

/-- Hash queries of `bPrfWCOpen sufCheckOpen A` at SHA2-128s: `≤ 269824 + qs·2007385 + 3929`. -/
theorem bPrfWCOpen_suf_hashes_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP (bPrfWCOpen sufCheckOpen A) (fun t => hkind t = .hash)
      (269824 + qs * 2007385 + 3929) := by
  have h := bPrfWCOpen_suf_hashes A qs hA
  rwa [keygenHashes_128s, signHashes_128s, Resources2.verifyHashes_128s] at h

#print axioms Reduction.Open.bPrfOpen_close
#print axioms Reduction.Open.bPrfWOpen_close
#print axioms Reduction.Open.bPrfCOpen_close
#print axioms Reduction.Open.bPrfWCOpen_close
#print axioms Reduction.Open.bPrfWCOpen_close_suf
#print axioms Reduction.Open.bPrfWOpen_close_euf
#print axioms Reduction.Open.bPrfOpen_kindBound
#print axioms Reduction.Open.bPrfWOpen_kindBound
#print axioms Reduction.Open.bPrfCOpen_hashes
#print axioms Reduction.Open.bPrfCOpen_prfmsg
#print axioms Reduction.Open.bPrfCOpen_game
#print axioms Reduction.Open.bPrfWCOpen_suf_hashes
#print axioms Reduction.Open.bPrfWCOpen_suf_prfmsg
#print axioms Reduction.Open.bPrfWCOpen_suf_game
#print axioms Reduction.Open.bPrfCOpen_hashes_128s
#print axioms Reduction.Open.bPrfWCOpen_suf_hashes_128s

end Open
end Reduction
