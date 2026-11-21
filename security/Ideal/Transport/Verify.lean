import Ideal.Transport.Core
import Reduction.TcrMemo

/-!
# Naturality of verification under `setPrf`

Verification never reads `PRF` / `PRF_msg`, so every verification-side program at
`setPrf prims prf pm`, applied to the field-wise transported key and signature (`trPk`, `trSig`),
equals the program at `prims`: callback-parametric recovery (`forsPkFromSigWith_setPrf`,
`pkFromSigWith_setPrf`, `verifyWith_setPrf`), `verifyCalls`, `Resources2.verifyFree`,
`verifyInternalM` (one monad, two agreeing query instances), `verifyInternal`, `classify`,
`g2Valid`, `g2ClassOf` (given naturality of `idealSign`), and phase 2 of `bTcrArM`
(given naturality of the forger's run).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Transport

open Reduction

section Callback

variable {p : Params} (core : CorePrimitives p) (prf : core.PkSeed → core.SkSeed → Adrs → core.Y)
  (pm : core.SkPrf → core.Y → List Byte → core.Y)

theorem wotsPkFromSigWith_setPrf {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (sig : WotsSig p core) (msg : core.Y) (adrs : Adrs) :
    wotsPkFromSigWith (setPrfC core prf pm) hash compress sig msg adrs =
      wotsPkFromSigWith core hash compress sig msg adrs := by krfl

theorem xmssPkFromSigWith_setPrf {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (idx : ℕ) (sig : XmssSigCore p core) (msg : core.Y) (adrs : Adrs) :
    xmssPkFromSigWith (setPrfC core prf pm) hash compress nodeHash idx (trXmss core prf pm sig)
        msg adrs =
      xmssPkFromSigWith core hash compress nodeHash idx sig msg adrs := by
  unfold xmssPkFromSigWith
  rw [wotsPkFromSigWith_setPrf]
  rfl

theorem forsPkFromSigWith_setPrf {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (sig : ForsSigCore p core) (md : List Byte) (adrs : Adrs) :
    forsPkFromSigWith (setPrfC core prf pm) hash nodeHash compress
        (sig.map (trFors core prf pm)) md adrs =
      forsPkFromSigWith core hash nodeHash compress sig md adrs := by
  unfold forsPkFromSigWith
  simp only [Vector.getElem_map, trFors_sk, trFors_auth]

end Callback

section Hypertree

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  (prf : core.PkSeed → core.SkSeed → Adrs → core.Y)
  (pm : core.SkPrf → core.Y → List Byte → core.Y)

theorem recoverFromPositionWith_setPrf {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (pk : core.PkSeed) :
    ∀ (layers : ℕ) (pos : LayerPosition vp) (h : pos.layer.val + layers = vp.params.d)
      (msg : core.Y) (sigs : Vector (XmssSigCore vp.params core) layers),
    GeneralHypertree.recoverFromPositionWith vp (setPrfC core prf pm) hash compress nodeHash pk pos
        layers h msg (sigs.map (trXmss core prf pm)) =
      GeneralHypertree.recoverFromPositionWith vp core hash compress nodeHash pk pos
        layers h msg sigs
  | 0, pos, h, msg, sigs => by
      simp only [GeneralHypertree.recoverFromPositionWith]
  | 1, pos, h, msg, sigs => by
      simp only [GeneralHypertree.recoverFromPositionWith]
      rw [← xmssPkFromSigWith_setPrf core prf pm]
      congr 1
      simp [Vector.head]
  | layers + 2, pos, h, msg, sigs => by
      simp only [GeneralHypertree.recoverFromPositionWith]
      have e : (sigs.map (trXmss core prf pm)).head = trXmss core prf pm sigs.head := by
        simp [Vector.head]
      have e2 : (sigs.map (trXmss core prf pm)).tail = sigs.tail.map (trXmss core prf pm) := by
        ext i hi; simp
      rw [e, e2, xmssPkFromSigWith_setPrf]
      exact bind_congr fun root => recoverFromPositionWith_setPrf hash compress nodeHash pk
        (layers + 1) _ _ root sigs.tail

theorem pkFromSigWith_setPrf {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (msg : core.Y)
    (sig : HtSigCore vp.params core) (pk : core.PkSeed) (parts : DigestParts vp.params) :
    GeneralHypertree.pkFromSigWith vp (setPrfC core prf pm) hash compress nodeHash msg
        (sig.map (trXmss core prf pm)) pk parts =
      GeneralHypertree.pkFromSigWith vp core hash compress nodeHash msg sig pk parts :=
  recoverFromPositionWith_setPrf core prf pm hash compress nodeHash pk _ _ _ msg sig

end Hypertree

section Reduction

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)

theorem digestParts_setPrf (pk : PublicKeyCore prims.core) (R : prims.Y) (msg : List Byte) :
    digestParts (prims := setPrf prims prf pm) (trPk _ prf pm pk) R msg =
      digestParts (prims := prims) pk R msg := rfl

theorem logTh_setPrf (pk : prims.PkSeed) :
    logTh (prims := setPrf prims prf pm) pk = logTh (prims := prims) pk := rfl

/-- FORS recovery followed by hypertree recovery, callback-parametric: the common shape of
`verifyCalls`, `Resources2.verifyFree` and (after the `H_msg` query) `verifyInternalM`. -/
theorem verifyWith_setPrf {m : Type → Type*} [Monad m]
    (hash : Adrs → prims.Y → m prims.Y) (nodeHash : Adrs → prims.Y → prims.Y → m prims.Y)
    (compress : Adrs → List prims.Y → m prims.Y)
    (sig : GeneralScheme.SignatureCore vp prims.core) (md : List Byte) (adrs : Adrs)
    (pkSeed : prims.PkSeed) (parts : DigestParts vp.params) :
    (forsPkFromSigWith (setPrfC prims.core prf pm) hash nodeHash compress
        (trSig _ prf pm sig).fors md adrs >>= fun forsPk =>
      GeneralHypertree.pkFromSigWith vp (setPrfC prims.core prf pm) hash compress nodeHash forsPk
        (trSig _ prf pm sig).hypertree pkSeed parts) =
    (forsPkFromSigWith prims.core hash nodeHash compress sig.fors md adrs >>= fun forsPk =>
      GeneralHypertree.pkFromSigWith vp prims.core hash compress nodeHash forsPk
        sig.hypertree pkSeed parts) := by
  rw [trSig_fors, trSig_hypertree, forsPkFromSigWith_setPrf]
  simp only [pkFromSigWith_setPrf]

/-- (V1) -/
theorem verifyCalls_setPrf (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    verifyCalls (prims := setPrf prims prf pm) (trPk _ prf pm pk) msg (trSig _ prf pm sig) =
      verifyCalls (prims := prims) pk msg sig :=
  congrArg (fun prog : StateM (List (prims.AdrsKey × List prims.Y)) prims.Y => (prog.run []).2)
    (verifyWith_setPrf prims prf pm
      (fun a x => logTh (prims := prims) pk.pkSeed (prims.adrsToKey a) [x])
      (fun a l r => logTh (prims := prims) pk.pkSeed (prims.adrsToKey a) [l, r])
      (fun a xs => logTh (prims := prims) pk.pkSeed (prims.adrsToKey a) xs)
      sig (digestParts pk sig.randomness msg).md.toList (digestParts pk sig.randomness msg).forsAdrs
      pk.pkSeed (digestParts pk sig.randomness msg))

/-- (V3) -/
theorem verifyFree_setPrf (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    Resources2.verifyFree (prims := setPrf prims prf pm) pkSeed parts (trSig _ prf pm sig) =
      Resources2.verifyFree (prims := prims) pkSeed parts sig :=
  verifyWith_setPrf prims prf pm
      (fun a x => Resources2.thQ prims (prims.adrsToKey a) [x])
      (fun a l r => Resources2.thQ prims (prims.adrsToKey a) [l, r])
      (fun a xs => Resources2.thQ prims (prims.adrsToKey a) xs)
      sig parts.md.toList parts.forsAdrs pkSeed parts

end Reduction

section Monadic

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  (prf : core.PkSeed → core.SkSeed → Adrs → core.Y)
  (pm : core.SkPrf → core.Y → List Byte → core.Y)
  {m : Type → Type*} [Monad m]
  (inst : HasQuery (publicHashSpec core) m)
  (inst' : HasQuery (publicHashSpec (setPrfC core prf pm)) m)

omit [Monad m] in
theorem f_setPrf
    (hth : ∀ pk ak xs, (inst'.query (.thash pk ak xs) : m core.Y) = inst.query (.thash pk ak xs))
    (pk : core.PkSeed) :
    @PublicHash.f _ (setPrfC core prf pm) m inst' pk = @PublicHash.f _ core m inst pk := by
  funext a x; exact hth _ _ _

omit [Monad m] in
theorem h_setPrf
    (hth : ∀ pk ak xs, (inst'.query (.thash pk ak xs) : m core.Y) = inst.query (.thash pk ak xs))
    (pk : core.PkSeed) :
    @PublicHash.h _ (setPrfC core prf pm) m inst' pk = @PublicHash.h _ core m inst pk := by
  funext a x y; exact hth _ _ _

omit [Monad m] in
theorem tl_setPrf
    (hth : ∀ pk ak xs, (inst'.query (.thash pk ak xs) : m core.Y) = inst.query (.thash pk ak xs))
    (pk : core.PkSeed) :
    @PublicHash.tl _ (setPrfC core prf pm) m inst' pk = @PublicHash.tl _ core m inst pk := by
  funext a x; exact hth _ _ _

omit [Monad m] in
theorem hmsg_setPrf
    (hhm : ∀ r pk root msg, (inst'.query (.hmsg r pk root msg) : m (Bytes vp.params.m)) =
      inst.query (.hmsg r pk root msg)) :
    @PublicHash.hmsg _ (setPrfC core prf pm) m inst' = @PublicHash.hmsg _ core m inst := by
  funext r pk root msg; exact hhm _ _ _ _

/-- (V2, monadic) -/
theorem verifyInternalM_setPrf [DecidableEq core.Y]
    (hth : ∀ pk ak xs, (inst'.query (.thash pk ak xs) : m core.Y) = inst.query (.thash pk ak xs))
    (hhm : ∀ r pk root msg, (inst'.query (.hmsg r pk root msg) : m (Bytes vp.params.m)) =
      inst.query (.hmsg r pk root msg))
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core) :
    @GeneralScheme.verifyInternalM vp (setPrfC core prf pm) m _ inst' _ msg (trSig core prf pm sig)
        (trPk core prf pm pk) =
      @GeneralScheme.verifyInternalM vp core m _ inst _ msg sig pk := by
  unfold GeneralScheme.verifyInternalM GeneralHypertree.verifyM GeneralHypertree.pkFromSigM
    GeneralHypertree.recoverFromPositionM forsPkFromSigM
  simp only [trSig_fors, trSig_hypertree, trSig_randomness, trPk_pkSeed, trPk_pkRoot,
    f_setPrf core prf pm inst inst' hth, h_setPrf core prf pm inst inst' hth,
    tl_setPrf core prf pm inst inst' hth, hmsg_setPrf core prf pm inst inst' hhm,
    forsPkFromSigWith_setPrf, recoverFromPositionWith_setPrf]
  rfl

end Monadic

section Pure

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)

/-- The deterministic interpretation of the public hash, as a query capability of `Id`. -/
@[reducible] def implQ {p : Params} (prims : Primitives p) : HasQuery (publicHashSpec prims.core) Id :=
  ⟨PublicHash.impl prims⟩

/-- `simulateQ (PublicHash.impl prims)` as a query-preserving morphism into `Id`. -/
def implHom {p : Params} (prims : Primitives p) :
    @HasQuery.QueryHom _ (publicHashSpec prims.core) (OracleComp (publicHashSpec prims.core)) _ _
      Id _ (implQ prims) :=
  letI := implQ prims
  { toMonadHom := simulateQ' (PublicHash.impl prims)
    map_query' := fun t => simulateQ_HasQuery_query (PublicHash.impl prims) t }

theorem verifyInternal_eq_Id [DecidableEq prims.Y] (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (pk : PublicKeyCore prims.core) :
    GeneralScheme.verifyInternal vp prims msg sig pk =
      @GeneralScheme.verifyInternalM vp prims.core Id _ (implQ prims) _ msg sig pk :=
  @GeneralScheme.verifyInternalM_natural vp prims.core _ _ _ _ _ _ _ (implQ prims) _
    (implHom prims) msg sig pk

theorem forsPkFromSig_eq_Id {p : Params} (prims : Primitives p) (sig : ForsSigCore p prims.core)
    (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkFromSig prims sig md pk adrs =
      @forsPkFromSigM _ prims.core Id _ (implQ prims) sig md pk adrs :=
  @forsPkFromSigM_natural _ prims.core _ _ _ _ _ _ _ (implQ prims) (implHom prims) sig md pk adrs

theorem xmssPkFromSig_eq_Id {p : Params} (prims : Primitives p) (idx : ℕ)
    (sig : XmssSigCore p prims.core) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    xmssPkFromSig prims idx sig msg pk adrs =
      @xmssPkFromSigM _ prims.core Id _ (implQ prims) idx sig msg pk adrs :=
  @xmssPkFromSigM_natural _ prims.core _ _ _ _ _ _ _ (implQ prims) (implHom prims) idx sig msg
    pk adrs

/-- (V2, pure) -/
theorem verifyInternal_setPrf [DecidableEq prims.Y] (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (pk : PublicKeyCore prims.core) :
    GeneralScheme.verifyInternal vp (setPrf prims prf pm) msg (trSig _ prf pm sig)
        (trPk _ prf pm pk) =
      GeneralScheme.verifyInternal vp prims msg sig pk := by
  rw [verifyInternal_eq_Id, verifyInternal_eq_Id]
  exact verifyInternalM_setPrf prims.core prf pm (implQ prims) (implQ (setPrf prims prf pm))
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) msg sig pk

theorem forsPkFromSig_setPrf (sig : ForsSigCore vp.params prims.core)
    (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkFromSig (setPrf prims prf pm) (sig.map (trFors _ prf pm)) md pk adrs =
      forsPkFromSig prims sig md pk adrs := by
  rw [forsPkFromSig_eq_Id, forsPkFromSig_eq_Id]
  exact forsPkFromSigWith_setPrf prims.core prf pm _ _ _ sig md adrs

theorem xmssPkFromSig_setPrf (idx : ℕ)
    (sig : XmssSigCore vp.params prims.core) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    xmssPkFromSig (setPrf prims prf pm) idx (trXmss _ prf pm sig) msg pk adrs =
      xmssPkFromSig prims idx sig msg pk adrs := by
  rw [xmssPkFromSig_eq_Id, xmssPkFromSig_eq_Id]
  exact xmssPkFromSigWith_setPrf prims.core prf pm _ _ _ idx sig msg adrs

end Pure

section Games

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)

theorem layerMsg_setPrf (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (j : ℕ) :
    layerMsg (prims := setPrf prims prf pm) pkSeed parts (s.map (trXmss _ prf pm)) m0 j =
      layerMsg (prims := prims) pkSeed parts s m0 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [layerMsg]
    split
    · rw [ih, Vector.getElem_map, xmssPkFromSig_setPrf]
    · exact ih

theorem layerTops_setPrf (pkSeed : prims.PkSeed) (parts : DigestParts vp.params)
    (s : HtSigCore vp.params prims.core) (m0 : prims.Y) (j : Fin vp.params.d) :
    layerTops (prims := setPrf prims prf pm) pkSeed parts (s.map (trXmss _ prf pm)) m0 j =
      layerTops (prims := prims) pkSeed parts s m0 j := by
  unfold layerTops
  rw [layerMsg_setPrf, Vector.getElem_map, trXmss_wots]
  krfl

variable [DecidableEq prims.Y]

theorem wotsLayer?_setPrf (pk : PublicKeyCore prims.core) (parts : DigestParts vp.params)
    (forged ref : GeneralScheme.SignatureCore vp prims.core) :
    wotsLayer? (prims := setPrf prims prf pm) (trPk _ prf pm pk) parts (trSig _ prf pm forged)
        (trSig _ prf pm ref) =
      wotsLayer? (prims := prims) pk parts forged ref := by
  unfold wotsLayer?
  refine congrArg (fun f => List.find? f (List.finRange vp.params.d)) (funext fun j => ?_)
  rw [decide_eq_decide]
  simp only [trSig_fors, trSig_hypertree, trPk_pkSeed]
  rw [forsPkFromSig_setPrf, forsPkFromSig_setPrf, layerMsg_setPrf, layerMsg_setPrf,
    layerTops_setPrf, layerTops_setPrf]

theorem openTree?_setPrf (pk : PublicKeyCore prims.core) (parts : DigestParts vp.params)
    (opened : List (Adrs × ℕ)) (forged ref : GeneralScheme.SignatureCore vp prims.core) :
    openTree? (prims := setPrf prims prf pm) (trPk _ prf pm pk) parts opened
        (trSig _ prf pm forged) (trSig _ prf pm ref) =
      openTree? (prims := prims) pk parts opened forged ref := by
  unfold openTree?
  refine congrArg (fun f => List.find? f (List.finRange vp.params.k)) (funext fun j => ?_)
  rw [decide_eq_decide]
  simp only [trSig_fors, trPk_pkSeed, Vector.getElem_map, trFors_sk]

theorem classify_setPrf (pk : PublicKeyCore prims.core) (signed : List (List Byte × prims.Y))
    (msg : List Byte) (forged ref : GeneralScheme.SignatureCore vp prims.core) :
    classify (prims := setPrf prims prf pm) (trPk _ prf pm pk) signed msg (trSig _ prf pm forged)
        (trSig _ prf pm ref) =
      classify (prims := prims) pk signed msg forged ref := by
  unfold classify
  simp only [trSig_randomness, digestParts_setPrf, wotsLayer?_setPrf, openTree?_setPrf]
  rfl

/-- (V4) -/
theorem g2Valid_setPrf (pk : PublicKeyCore prims.core) (log : G2Log prims) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    g2Valid (prims := setPrf prims prf pm) (trPk _ prf pm pk) log msg (trSig _ prf pm sig) =
      g2Valid (prims := prims) pk log msg sig := by
  unfold g2Valid
  rw [verifyInternal_setPrf]

/-- (V4) with the naturality of `idealSign` as a hypothesis. -/
theorem g2ClassOf_setPrf (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core)
    (log : G2Log prims) (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core)
    (hsign : idealSign vp (setPrf prims prf pm) tbl msg (trPk _ prf pm pk) sig.randomness =
      trSig _ prf pm (idealSign vp prims tbl msg pk sig.randomness)) :
    g2ClassOf (prims := setPrf prims prf pm) tbl (trPk _ prf pm pk) log msg (trSig _ prf pm sig) =
      g2ClassOf (prims := prims) tbl pk log msg sig := by
  unfold g2ClassOf
  rw [trSig_randomness, hsign, classify_setPrf]
  rfl

end Games

section Assembly

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {optRand' : PublicKeyCore (setPrf prims prf pm).core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

theorem idealRoot_setPrf (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    idealRoot vp (setPrf prims prf pm) tbl pkSeed = idealRoot vp prims tbl pkSeed := by krfl

theorem idealPk_setPrf (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed) :
    idealPk vp (setPrf prims prf pm) tbl pkSeed = trPk _ prf pm (idealPk vp prims tbl pkSeed) := by
  unfold idealPk
  rw [idealRoot_setPrf]
  rfl

theorem findCollisionM_setPrf (pk : prims.PkSeed)
    (targets calls : List (prims.AdrsKey × List prims.Y)) :
    findCollisionM (prims := setPrf prims prf pm) pk targets calls =
      findCollisionM (prims := prims) pk targets calls := by krfl

theorem classOut_setPrf (n : ℕ) (L : List (prims.AdrsKey × List prims.Y))
    (jm : ℕ × List prims.Y) :
    classOut (setPrf prims prf pm) n L jm = classOut prims n L jm := by krfl

/-- (V5) -/
theorem memoForge_setPrf (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (A' : Forger vp (setPrf prims prf pm) optRand' pkSeedDist)
    (hrun : ∀ tbl pk, g2Run A' tbl (trPk _ prf pm pk) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$> g2Run A tbl pk)
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    memoForge (prims := setPrf prims prf pm) n A' s pkSeed =
      memoForge (prims := prims) n A s pkSeed := by
  unfold memoForge
  rw [idealPk_setPrf]
  dsimp only
  rw [hrun, bind_map_left]
  refine bind_congr fun z => ?_
  rw [verifyCalls_setPrf, findCollisionM_setPrf, classOut_setPrf]

/-- (V5) -/
theorem bTcrArM_forge_setPrf (n : ℕ) (A : Forger vp prims optRand pkSeedDist)
    (A' : Forger vp (setPrf prims prf pm) optRand' pkSeedDist)
    (hrun : ∀ tbl pk, g2Run A' tbl (trPk _ prf pm pk) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$> g2Run A tbl pk)
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    (bTcrArM n A').forge s pkSeed = (bTcrArM n A).forge s pkSeed :=
  memoForge_setPrf prims prf pm n A A' hrun s pkSeed

end Assembly

end Ideal.Transport

section AxiomCheck
open Ideal.Transport
#print axioms forsPkFromSigWith_setPrf
#print axioms pkFromSigWith_setPrf
#print axioms verifyCalls_setPrf
#print axioms verifyFree_setPrf
#print axioms verifyInternalM_setPrf
#print axioms verifyInternal_setPrf
#print axioms classify_setPrf
#print axioms g2Valid_setPrf
#print axioms g2ClassOf_setPrf
#print axioms memoForge_setPrf
#print axioms bTcrArM_forge_setPrf
end AxiomCheck
