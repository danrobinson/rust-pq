import Ideal.Transport.Core

/-!
# Naturality of signing, of the wire codec and of the byte-level forger wrapper under `setPrf`
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Transport

set_option linter.unusedSectionVars false

/-! ## Generic helpers -/

/-- `Vector.ofFnM` commutes with a pointwise map. -/
theorem vector_ofFnM_map {m : Type → Type*} [Monad m] [LawfulMonad m] {α β : Type} (g : α → β) :
    ∀ {n : ℕ} (f : Fin n → m α),
      Vector.ofFnM (fun i => g <$> f i) = Vector.map g <$> Vector.ofFnM f
  | 0, f => by simp [Vector.ofFnM_zero]
  | n + 1, f => by
      rw [Vector.ofFnM_succ, Vector.ofFnM_succ, vector_ofFnM_map g fun i => f i.castSucc]
      simp [Vector.map_push]

/-- `Vector.map` commutes with `insertIdx`. -/
theorem vector_map_insertIdx {α β : Type} (g : α → β) {n : ℕ} (v : Vector α n) (i : ℕ) (a : α)
    (h : i ≤ n) : Vector.map g (v.insertIdx i a h) = (v.map g).insertIdx i (g a) h := by
  ext j hj
  simp only [Vector.getElem_map, Vector.getElem_insertIdx]
  split_ifs <;> rfl

variable {p : Params}

section Callback

variable (core : CorePrimitives p) (prf : core.PkSeed → core.SkSeed → Adrs → core.Y)
  (pm : core.SkPrf → core.Y → List Byte → core.Y)
variable {m : Type → Type*} [Monad m] [LawfulMonad m]

theorem forsSignWithSecret_tr (hash : Adrs → core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (secret : Adrs → m core.Y)
    (md : List Byte) (adrs : Adrs) :
    forsSignWithSecret (setPrfC core prf pm) hash nodeHash secret md adrs =
      Vector.map (trFors core prf pm) <$> forsSignWithSecret core hash nodeHash secret md adrs := by
  unfold forsSignWithSecret
  rw [← vector_ofFnM_map]
  refine congrArg Vector.ofFnM (funext fun i => ?_)
  have hleaf : forsLeafWithSecret (setPrfC core prf pm) hash secret adrs =
      forsLeafWithSecret core hash secret adrs := by krfl
  simp only [map_bind, map_pure, trFors_mk, hleaf]

theorem forsPkFromSigWith_tr (hash : Adrs → core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y) (compress : Adrs → List core.Y → m core.Y)
    (sig : ForsSigCore p core) (md : List Byte) (adrs : Adrs) :
    forsPkFromSigWith (setPrfC core prf pm) hash nodeHash compress
        (sig.map (trFors core prf pm)) md adrs =
      forsPkFromSigWith core hash nodeHash compress sig md adrs := by
  unfold forsPkFromSigWith
  simp only [Vector.getElem_map, trFors_sk, trFors_auth]

theorem xmssSignWithSecret_tr (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (msg : core.Y) (adrs : Adrs) (idx : ℕ) :
    xmssSignWithSecret (setPrfC core prf pm) hash compress nodeHash secret msg adrs idx =
      trXmss core prf pm <$> xmssSignWithSecret core hash compress nodeHash secret msg adrs idx := by
  unfold xmssSignWithSecret
  have hleaf : xmssLeafWithSecret (setPrfC core prf pm) hash compress secret adrs =
      xmssLeafWithSecret core hash compress secret adrs := by krfl
  have hw : wotsSignWithSecret (setPrfC core prf pm) hash secret msg (wotsLeafAdrs adrs idx) =
      wotsSignWithSecret core hash secret msg (wotsLeafAdrs adrs idx) := by krfl
  simp only [map_bind, map_pure, trXmss_mk, hleaf, hw]

theorem xmssPkFromSigWith_tr (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (idx : ℕ) (sig : XmssSigCore p core) (msg : core.Y) (adrs : Adrs) :
    xmssPkFromSigWith (setPrfC core prf pm) hash compress nodeHash idx (trXmss core prf pm sig)
        msg adrs =
      xmssPkFromSigWith core hash compress nodeHash idx sig msg adrs := by krfl

end Callback

/-! ## Hypertree signing -/

section Hypertree

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  (prf : core.PkSeed → core.SkSeed → Adrs → core.Y)
  (pm : core.SkPrf → core.Y → List Byte → core.Y)
variable {m : Type → Type*} [Monad m] [LawfulMonad m]

theorem signFromPositionWithSecret_tr (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) :
    ∀ (layers : ℕ) (recoverFinal : Bool) (pos : LayerPosition vp)
      (h : pos.layer.val + layers = vp.params.d) (msg : core.Y),
      GeneralHypertree.signFromPositionWithSecret (setPrfC core prf pm) hash compress nodeHash
          secret recoverFinal pos layers h msg =
        Vector.map (trXmss core prf pm) <$>
          GeneralHypertree.signFromPositionWithSecret core hash compress nodeHash secret
            recoverFinal pos layers h msg
  | 0, _, _, _, _ => by
      rw [GeneralHypertree.signFromPositionWithSecret, GeneralHypertree.signFromPositionWithSecret]
      simp
  | 1, rf, pos, _, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret, GeneralHypertree.signFromPositionWithSecret,
        xmssSignWithSecret_tr]
      cases rf <;>
        simp [xmssPkFromSigWith_tr]
  | layers + 2, _, pos, hremaining, msg => by
      rw [GeneralHypertree.signFromPositionWithSecret, GeneralHypertree.signFromPositionWithSecret,
        xmssSignWithSecret_tr]
      simp only [map_bind, bind_map_left, xmssPkFromSigWith_tr, map_pure,
        signFromPositionWithSecret_tr hash compress nodeHash secret (layers + 1), vector_map_insertIdx]

theorem signWithSecret_tr (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y) (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (secret : Adrs → m core.Y) (msg : core.Y) (parts : DigestParts vp.params) :
    GeneralHypertree.signWithSecret (setPrfC core prf pm) hash compress nodeHash secret msg parts =
      Vector.map (trXmss core prf pm) <$>
        GeneralHypertree.signWithSecret core hash compress nodeHash secret msg parts := by
  unfold GeneralHypertree.signWithSecret
  exact signFromPositionWithSecret_tr core prf pm hash compress nodeHash secret _ _ _ _ _

/-! ## Monadic signing naturality (S1m) -/

section Monadic

variable (inst : HasQuery (publicHashSpec core) m)
  (inst' : HasQuery (publicHashSpec (setPrfC core prf pm)) m)
  (hT : ∀ pk ak xs, inst'.query (.thash pk ak xs) = inst.query (.thash pk ak xs))
  (hM : ∀ r pk root msg, inst'.query (.hmsg r pk root msg) = inst.query (.hmsg r pk root msg))

include hT in
theorem publicHash_f_tr (pkSeed : core.PkSeed) :
    @PublicHash.f _ (setPrfC core prf pm) m inst' pkSeed = @PublicHash.f _ core m inst pkSeed :=
  funext fun _ => funext fun _ => hT _ _ _

include hT in
theorem publicHash_h_tr (pkSeed : core.PkSeed) :
    @PublicHash.h _ (setPrfC core prf pm) m inst' pkSeed = @PublicHash.h _ core m inst pkSeed :=
  funext fun _ => funext fun _ => funext fun _ => hT _ _ _

include hT in
theorem publicHash_tl_tr (pkSeed : core.PkSeed) :
    @PublicHash.tl _ (setPrfC core prf pm) m inst' pkSeed = @PublicHash.tl _ core m inst pkSeed :=
  funext fun _ => funext fun _ => hT _ _ _

include hM in
theorem publicHash_hmsg_tr (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y)
    (msg : List Byte) :
    @PublicHash.hmsg _ (setPrfC core prf pm) m inst' r pkSeed pkRoot msg =
      @PublicHash.hmsg _ core m inst r pkSeed pkRoot msg := hM _ _ _ _

include hT hM in
/-- **(S1m)** Monadic signing naturality. -/
theorem signInternalWithSecretRandomizerM_tr (sec : Adrs → m core.Y) (msg : List Byte)
    (pkSeed : core.PkSeed) (pkRoot R : core.Y) :
    @GeneralScheme.signInternalWithSecretRandomizerM vp (setPrfC core prf pm) m _ inst' sec msg
        pkSeed pkRoot R =
      trSig core prf pm <$>
        @GeneralScheme.signInternalWithSecretRandomizerM vp core m _ inst sec msg pkSeed pkRoot
          R := by
  unfold GeneralScheme.signInternalWithSecretRandomizerM forsSignWithSecretM forsPkFromSigM
    GeneralHypertree.signWithSecretM
  rw [publicHash_hmsg_tr core prf pm inst inst' hM]
  simp only [publicHash_f_tr core prf pm inst inst' hT, publicHash_h_tr core prf pm inst inst' hT,
    publicHash_tl_tr core prf pm inst inst' hT, forsSignWithSecret_tr, signWithSecret_tr,
    map_bind, bind_map_left, forsPkFromSigWith_tr, map_pure, trSig_mk]

end Monadic

end Hypertree

/-! ## Closed signing naturality (S1) -/

/-- Close the goal with the term `t`, the type being checked by the kernel only. -/
elab "kexact " t:term : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let e ← Lean.Elab.Tactic.elabTerm t none
  g.assign e
  Lean.Elab.Tactic.replaceMainGoal []

section Closed

open Reduction

variable (vp : ValidatedParams) (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)

/-- A `HasQuery` instance for the public-hash interface of `core`, read as one for the interface
of `setPrfC core prf pm` (the two specifications are definitionally equal). -/
@[reducible] def trInst {p : Params} (core : CorePrimitives p) (prf : core.PkSeed → core.SkSeed → Adrs → core.Y)
    (pm : core.SkPrf → core.Y → List Byte → core.Y) {m : Type → Type*}
    (inst : HasQuery (publicHashSpec core) m) :
    HasQuery (publicHashSpec (setPrfC core prf pm)) m := by
  kexact inst

/-- **(S1)** `idealSign` over `setPrf prims prf pm` is `idealSign` over `prims`. -/
theorem idealSign_tr (tbl : SecretTable vp prims) (msg : List Byte)
    (pk : PublicKeyCore prims.core) (R : prims.Y) :
    idealSign vp (setPrf prims prf pm) tbl msg (trPk _ prf pm pk) R =
      trSig _ prf pm (idealSign vp prims tbl msg pk R) := by
  have h1 : idealSign vp (setPrf prims prf pm) tbl msg (trPk _ prf pm pk) R =
      simulateQ (PublicHash.impl prims)
        (@GeneralScheme.signInternalWithSecretRandomizerM vp (setPrfC prims.core prf pm)
          (OracleComp (publicHashSpec prims.core)) _ (trInst prims.core prf pm inferInstance)
          (fun a => pure (secretOf vp prims tbl a)) msg pk.pkSeed pk.pkRoot R) := by
    krfl
  rw [h1, signInternalWithSecretRandomizerM_tr prims.core prf pm inferInstance
    (trInst prims.core prf pm inferInstance) (fun _ _ _ => by krfl) (fun _ _ _ _ => by krfl)]
  rw [simulateQ_map]
  rfl

end Closed

/-! ## Codec (S2) -/

section Codec

variable {p : Params} (core : CorePrimitives p) (prf : core.PkSeed → core.SkSeed → Adrs → core.Y)
  (pm : core.SkPrf → core.Y → List Byte → core.Y)

/-- The same atomic codecs, for the bundle with `PRF`, `PRF_msg` replaced. -/
def trCodec (codec : CoreWireCodec p core) : CoreWireCodec p (setPrfC core prf pm) where
  pkSeed := codec.pkSeed
  skSeed := codec.skSeed
  skPrf := codec.skPrf
  y := codec.y
  y_toBytes := codec.y_toBytes

theorem encodePublicKey_tr (codec : CoreWireCodec p core) (pk : PublicKeyCore core) :
    encodePublicKey (trCodec core prf pm codec) (trPk core prf pm pk) =
      encodePublicKey codec pk := by
  rw [encodePublicKey_eq, encodePublicKey_eq]
  rfl

end Codec

section CodecSig

variable (vp : ValidatedParams) (core : CorePrimitives vp.params)
  (prf : core.PkSeed → core.SkSeed → Adrs → core.Y)
  (pm : core.SkPrf → core.Y → List Byte → core.Y)

theorem encodeSignature_tr (codec : CoreWireCodec vp.params core)
    (s : SignatureCore vp.params core) :
    encodeSignature vp (trCodec core prf pm codec) (trSig core prf pm s) =
      encodeSignature vp codec s := by
  rw [encodeSignature_eq, encodeSignature_eq]
  simp only [trSig_randomness, trSig_fors, trSig_hypertree, Vector.getElem_map, trFors_sk,
    trFors_auth, trXmss_wots, trXmss_auth]
  rfl

theorem signatureCodec_equiv_tr (codec : CoreWireCodec vp.params core)
    (s : SignatureCore vp.params core) :
    (signatureCodec vp (trCodec core prf pm codec)).equiv (trSig core prf pm s) =
      (signatureCodec vp codec).equiv s :=
  Vector.toList_inj.mp (encodeSignature_tr vp core prf pm codec s)

theorem decodeSignature_tr (codec : CoreWireCodec vp.params core) (raw : List Byte) :
    decodeSignature vp (trCodec core prf pm codec) raw =
      trSig core prf pm <$> decodeSignature vp codec raw := by
  unfold decodeSignature WireCodec.decode
  cases decodeExact vp.params.signatureBytes raw with
  | error e => rfl
  | ok bytes =>
    refine congrArg Except.ok ?_
    rw [Equiv.symm_apply_eq, signatureCodec_equiv_tr, Equiv.apply_symm_apply]

end CodecSig

/-! ## The byte-level forger wrapper (S3) -/

section Forger

open Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [Inhabited prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)
  (pkSeedDist : ProbComp prims.PkSeed)

theorem constSig_tr (y : prims.Y) :
    constSig (vp := vp) (prims := setPrf prims prf pm) y =
      trSig _ prf pm (constSig (vp := vp) (prims := prims) y) := by
  simp [constSig, trSig, trFors, trXmss]

include hopt in
/-- The two simulation layers of the wrapped forger, fused: the same handler on both sides. -/
theorem fusedImpl_tr (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core) :
    ((QueryImpl.liftTarget (StateT (G2Log (setPrf prims prf pm)) ProbComp)
          (QueryImpl.ofLift unifSpec ProbComp) +
        g2SignOracle optRand' (trPk _ prf pm pk) fun m R =>
          idealSign vp (setPrf prims prf pm) tbl m (trPk _ prf pm pk) R) ∘ₛ
      Coded.signingImpl
        (bytesView vp (setPrf prims prf pm) (trCodec _ prf pm codec) optRand' pkSeedDist)) =
    ((QueryImpl.liftTarget (StateT (G2Log prims) ProbComp) (QueryImpl.ofLift unifSpec ProbComp) +
        g2SignOracle optRand pk fun m R => idealSign vp prims tbl m pk R) ∘ₛ
      Coded.signingImpl (bytesView vp prims codec optRand pkSeedDist)) := by
  funext t
  rcases t with n | msg
  · rfl
  · simp only [QueryImpl.apply_compose, Coded.signingImpl, simulateQ_map]
    simp only [simulateQ_HasQuery_query, QueryImpl.add_apply_inr]
    simp only [g2SignOracle, map_bind, map_pure, hopt, idealSign_tr, bytesView, encodeSignature_tr]
    krfl

theorem readForgery_tr (out : List Byte × List Byte) :
    Coded.readForgery
        (bytesView vp (setPrf prims prf pm) (trCodec _ prf pm codec) optRand' pkSeedDist)
        (constSig default) out =
      ((Coded.readForgery (bytesView vp prims codec optRand pkSeedDist) (constSig default) out).1,
        trSig _ prf pm
          (Coded.readForgery (bytesView vp prims codec optRand pkSeedDist) (constSig default)
            out).2) := by
  simp only [Coded.readForgery, bytesView, decodeSignature_tr]
  cases decodeSignature vp codec out.2 with
  | error e => exact congrArg (Prod.mk out.1) (constSig_tr prf pm default)
  | ok s => rfl

include hopt in
/-- **(S3)** The typed forger built from a byte-level forger main `S`, over `setPrf prims prf pm`,
runs in `G2` exactly as the one over `prims`, up to `trSig` on the forged signature. -/
theorem g2Run_bytesToTyped_tr
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))
    (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core) :
    g2Run (prims := setPrf prims prf pm)
        (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩) tbl (trPk _ prf pm pk) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        g2Run (bytesToTyped (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist) ⟨S⟩)
          tbl pk := by
  unfold g2Run g2RunWith bytesToTyped Coded.reduce
  dsimp only
  rw [simulateQ_map, simulateQ_map, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose,
    fusedImpl_tr prf pm codec optRand optRand' hopt pkSeedDist tbl pk,
    funext (readForgery_tr prf pm codec optRand optRand' pkSeedDist)]
  have hpk : (bytesView vp (setPrf prims prf pm) (trCodec _ prf pm codec) optRand'
      pkSeedDist).encPk (trPk _ prf pm pk) = (bytesView vp prims codec optRand pkSeedDist).encPk pk :=
    encodePublicKey_tr _ prf pm codec pk
  rw [hpk]
  simp only [StateT.run_map, Functor.map_map]

include hopt in
/-- **(S3, strong forger)** The same for `bytesToTypedS`. -/
theorem g2Run_bytesToTypedS_tr
    (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))
    (tbl : SecretTable vp prims) (pk : PublicKeyCore prims.core) :
    g2Run (prims := setPrf prims prf pm)
        (bytesToTypedS (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
          (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary tbl
        (trPk _ prf pm pk) =
      (fun z => ((z.1.1, trSig _ prf pm z.1.2), z.2)) <$>
        g2Run (bytesToTypedS (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist)
          ⟨S⟩).toUnforgeableAdversary tbl pk :=
  g2Run_bytesToTyped_tr prf pm codec optRand optRand' hopt pkSeedDist S tbl pk

end Forger

#print axioms vector_ofFnM_map
#print axioms signInternalWithSecretRandomizerM_tr
#print axioms idealSign_tr
#print axioms encodeSignature_tr
#print axioms decodeSignature_tr
#print axioms encodePublicKey_tr
#print axioms g2Run_bytesToTyped_tr
#print axioms g2Run_bytesToTypedS_tr
