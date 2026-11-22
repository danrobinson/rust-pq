import MLink.SignParts
import HashSig.SLHDSA.External

/-!
# Signing (FIPS 205 Algorithms 12, 19 and 22): `Spec` = VCVio, all six SHA-2 parameter sets
-/

namespace MLink

open SLHDSA SLHDSA.Concrete

variable (S : Sha2Set)

/-! ### Hypertree signing (Algorithm 12) -/

/-- One layer of the fold in `Spec.htSign`. -/
def htSignStep (sk pk : Spec.Bytes) (st : Spec.Bytes × Spec.Bytes × Nat × Nat) (j : Nat) :
    Spec.Bytes × Spec.Bytes × Nat × Nat :=
  let (sig, root, tree, leaf) := st
  let adrs := { Spec.Adrs.zero with layer := j, tree := tree }
  let s := Spec.xmssSign S.spec root sk leaf pk adrs
  (sig ++ s, Spec.xmssPkFromSig S.spec leaf s root pk adrs, tree >>> S.spec.hp,
    tree % 2 ^ S.spec.hp)

/-- The signing walk of `Spec.htSign` as a recursion on the number of remaining layers. -/
def htSignGo (sk pk : Spec.Bytes) : Nat → Nat → Spec.Bytes → Nat → Nat → Spec.Bytes
  | 0, _, _, _, _ => []
  | n + 1, j, root, tree, leaf =>
    let adrs := { Spec.Adrs.zero with layer := j, tree := tree }
    let s := Spec.xmssSign S.spec root sk leaf pk adrs
    s ++ htSignGo sk pk n (j + 1) (Spec.xmssPkFromSig S.spec leaf s root pk adrs)
      (tree >>> S.spec.hp) (tree % 2 ^ S.spec.hp)

theorem foldl_htSignStep (sk pk : Spec.Bytes) :
    ∀ (n j : Nat) (sig root : Spec.Bytes) (tree leaf : Nat),
      ((List.range' j n).foldl (htSignStep S sk pk) (sig, root, tree, leaf)).1 =
        sig ++ htSignGo S sk pk n j root tree leaf := by
  intro n
  induction n with
  | zero => intro j sig root tree leaf; simp [htSignGo]
  | succ n ih =>
    intro j sig root tree leaf
    simp only [List.range'_succ, List.foldl_cons, htSignGo]
    rw [htSignStep, ih, List.append_assoc]

theorem htSign_eq_go (msg sk pk : Spec.Bytes) (t l : Nat) :
    Spec.htSign S.spec msg sk pk t l = htSignGo S sk pk S.spec.d 0 msg t l := by
  have := foldl_htSignStep S sk pk S.spec.d 0 [] msg t l
  rw [← List.range_eq_range', List.nil_append] at this
  exact this

/-- VCVio's typed signing walk from any reachable position is the spec's walk
(`tree ↦ tree >>> h'`, `leaf ↦ tree mod 2^h'`), whatever the `recoverFinal` flag. -/
theorem signFrom_eq (sk pk : S.Node) :
    ∀ (layers : ℕ) (b : Bool) (pos : LayerPosition S.vp)
      (h : pos.layer.val + layers = S.vp.params.d) (msg : S.Node),
      (GeneralHypertree.signFromPosition S.vp S.prims sk pk b pos layers h msg).toList.flatMap
          (xmssBytes S) =
        htSignGo S (nd sk) (nd pk) layers pos.layer.val (nd msg) pos.tree.val pos.leaf.val := by
  have hx : ∀ (pos : LayerPosition S.vp) (s : XmssSig S.vp.params S.prims.core) (msg : S.Node),
      nd (SLHDSA.xmssPkFromSig S.prims pos.leaf.val s msg pk pos.toAdrs) =
        Spec.xmssPkFromSig S.spec pos.leaf.val (xmssBytes S s) (nd msg) (nd pk)
          { Spec.Adrs.zero with layer := pos.layer.val, tree := pos.tree.val } :=
    fun pos s msg => xmssPkFromSig_eq S pos.leaf.val pos.leaf.isLt s msg pk pos.toAdrs
      (layerPosition_baseDom S pos)
  have hs : ∀ (pos : LayerPosition S.vp) (msg : S.Node),
      xmssBytes S (SLHDSA.xmssSign S.prims msg sk pk pos.toAdrs pos.leaf.val) =
        Spec.xmssSign S.spec (nd msg) (nd sk) pos.leaf.val (nd pk)
          { Spec.Adrs.zero with layer := pos.layer.val, tree := pos.tree.val } :=
    fun pos msg => xmssSign_eq S msg sk pk pos.toAdrs (layerPosition_baseDom S pos) pos.leaf.val
      pos.leaf.isLt
  intro layers
  induction layers using Nat.strong_induction_on with
  | _ layers ih =>
    intro b pos h msg
    match layers, h with
    | 0, h => simp [GeneralHypertree.signFromPosition, htSignGo]
    | 1, h =>
      simp only [GeneralHypertree.signFromPosition, htSignGo]
      cases b <;>
      · simp only [Bool.false_eq_true, ite_false, ite_true, Vector.toList_mk, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        exact hs pos msg
    | layers + 2, h =>
      simp only [GeneralHypertree.signFromPosition]
      rw [htSignGo]
      have hins : ∀ (v : Vector (XmssSig S.vp.params S.prims.core) (layers + 1))
          (s : XmssSig S.vp.params S.prims.core),
          (v.insertIdx 0 s).toList = s :: v.toList := by
        intro v s
        rcases v with ⟨⟨l⟩, hl⟩
        simp [Vector.insertIdx]
      rw [hins, List.flatMap_cons]
      refine congrArg₂ (· ++ ·) (hs pos msg) ?_
      refine (ih (layers + 1) (by omega) _ _ _ _).trans ?_
      rw [hx, hs]
      simp [LayerPosition.next, Nat.shiftRight_eq_div_pow, S.hp_eq]

/-- Algorithm 12, `ht_sign`. -/
theorem htSign_eq (msg sk pk : S.Node) (parts : DigestParts S.vp.params) :
    htBytes S (GeneralHypertree.sign S.vp S.prims msg sk pk parts) =
      Spec.htSign S.spec (nd msg) (nd sk) (nd pk) parts.idxTree.val parts.idxLeaf.val := by
  rw [htSign_eq_go, htBytes, ← S.d_eq]
  refine (congrArg (fun v : HtSigCore S.vp.params S.prims.core => v.toList.flatMap (xmssBytes S))
    (GeneralHypertree.sign_eq_signFromPosition S.vp S.prims msg sk pk parts)).trans ?_
  exact signFrom_eq S sk pk S.vp.params.d _ (LayerPosition.initial S.vp parts) (by simp) msg

/-! ### Internal signing (Algorithm 19) -/

theorem signWithRandomizer_eq (msg : List Byte) (skSeed pkSeed pkRoot R : S.Node) :
    GeneralScheme.signInternalWithRandomizer S.vp S.prims msg skSeed pkSeed pkRoot R =
      (let parts := splitDigest S.vp.params (S.prims.Hmsg R pkSeed pkRoot msg)
       let forsSig := forsSign S.prims parts.md.toList skSeed pkSeed parts.forsAdrs
       ⟨R, forsSig,
        GeneralHypertree.sign S.vp S.prims
          (forsPkFromSig S.prims forsSig parts.md.toList pkSeed parts.forsAdrs)
          skSeed pkSeed parts⟩) := by
  unfold GeneralScheme.signInternalWithRandomizer GeneralScheme.signInternalWithRandomizerM
    GeneralHypertree.sign forsSign forsPkFromSig
  simp only [simulateQ_bind]
  rfl

/-- The secret key is four `n`-byte blocks. -/
theorem skBytes_block (sk : SecretKeyCore S.prims.core) :
    Spec.block S.spec (skBytes S sk) 0 = nd sk.skSeed ∧
    Spec.block S.spec (skBytes S sk) 1 = nd sk.skPrf ∧
    Spec.block S.spec (skBytes S sk) 2 = nd sk.pkSeed ∧
    Spec.block S.spec (skBytes S sk) 3 = nd sk.pkRoot := by
  have e : skBytes S sk =
      nds ([sk.skSeed, sk.skPrf, sk.pkSeed, sk.pkRoot] : List S.Node) := by
    show _ = nd _ ++ (nd _ ++ (nd _ ++ (nd _ ++ [])))
    simp [skBytes]
  rw [e]
  exact ⟨block_nds S _ 0 (by show 0 < 4; norm_num), block_nds S _ 1 (by show 1 < 4; norm_num), block_nds S _ 2 (by show 2 < 4; norm_num),
    block_nds S _ 3 (by show 3 < 4; norm_num)⟩

/-- FIPS 205 Algorithm 19, `slh_sign_internal`, with `opt_rand = addrnd`. -/
theorem sign_eq (msg : Spec.Bytes) (sk : SecretKeyCore S.prims.core) (addrnd : S.Node) :
    Spec.slhSignInternal S.spec msg (skBytes S sk) (nd addrnd) =
      sigBytes S (GeneralScheme.signInternal S.vp S.prims (cv msg) sk addrnd) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := skBytes_block S sk
  have hR : Spec.PRFmsg S.spec (nd sk.skPrf) (nd addrnd) msg =
      nd (S.prims.PRFmsg sk.skPrf addrnd (cv msg)) :=
    ((PRFmsg_eq S _ _ _).trans (congrArg (Spec.PRFmsg S.spec _ _) (sp_cv msg))).symm
  refine Eq.trans ?_ (congrArg (sigBytes S) (signWithRandomizer_eq S (cv msg) sk.skSeed sk.pkSeed
    sk.pkRoot (S.prims.PRFmsg sk.skPrf addrnd (cv msg))).symm)
  generalize hRR : S.prims.PRFmsg sk.skPrf addrnd (cv msg) = R at hR ⊢
  have hdg : sp (S.prims.Hmsg R sk.pkSeed sk.pkRoot (cv msg)).toList =
      Spec.Hmsg S.spec (nd R) (nd sk.pkSeed) (nd sk.pkRoot) msg :=
    (Hmsg_eq S _ _ _ _).trans (congrArg (Spec.Hmsg S.spec _ _ _) (sp_cv msg))
  generalize hdig : S.prims.Hmsg R sk.pkSeed sk.pkRoot (cv msg) = dg at hdg
  unfold Spec.slhSignInternal
  simp only [hb0, hb1, hb2, hb3, hR, ← hdg]
  have hmd := splitDigest_md S dg
  have ht := splitDigest_tree S dg
  have hl := splitDigest_leaf S dg
  generalize splitDigest S.vp.params dg = parts at hmd ht hl ⊢
  have hdom : ForsDom parts.forsAdrs := forsAdrs_dom S parts
  have hadr : adr parts.forsAdrs =
      specForsAdrs (Spec.digestTree S.spec (sp dg.toList))
        (Spec.digestLeaf S.spec (sp dg.toList)) := by
    rw [← ht, ← hl]; rfl
  have hfs := forsSign_eq S parts.md.toList Vector.length_toList sk.skSeed sk.pkSeed
    parts.forsAdrs hdom
  have hfp := forsPkFromSig_eq S
    (forsSign S.prims parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs) parts.md.toList
    Vector.length_toList sk.pkSeed parts.forsAdrs hdom
  have hht := htSign_eq S
    (forsPkFromSig S.prims (forsSign S.prims parts.md.toList sk.skSeed sk.pkSeed parts.forsAdrs)
      parts.md.toList sk.pkSeed parts.forsAdrs) sk.skSeed sk.pkSeed parts
  rw [hfp, hfs, hmd, hadr, ht, hl] at hht
  rw [hmd, hadr] at hfs
  show _ = nd R ++ forsBytes S _ ++ htBytes S _
  exact congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl hfs.symm) hht.symm

/-! ### External pure signing with a context string (Algorithm 22) -/

/-- `M' = 0x00 ‖ |ctx| ‖ ctx ‖ M` is VCVio's `encodePureMessage` (context of at most 255 bytes). -/
theorem cv_withContext (msg ctx : Spec.Bytes) (hc : ctx.length ≤ 255) :
    External.encodePureMessage (cv ctx) (cv msg) = .ok (cv (Spec.withContext msg ctx)) := by
  rw [External.encodePureMessage_eq_ok (cv ctx) (cv msg) (by rw [cv_length]; exact hc)]
  have h255 : ctx.length < 256 := by omega
  simp [Spec.withContext, Spec.toByte, cv, List.range_succ]
  rfl

/-- **External pure signing (FIPS 205 Algorithm 22, caller-supplied `addrnd`), typed secret key.**
`Spec.slhSign S.spec` is `none` exactly when VCVio's `External.signPureWithRandomizer` returns an
error (context longer than 255 bytes), and otherwise `some` of the flat FIPS encoding of the
signature VCVio returns. -/
theorem slhSign_eq (msg ctx : Spec.Bytes) (sk : SecretKeyCore S.prims.core) (addrnd : S.Node) :
    Spec.slhSign S.spec msg ctx (skBytes S sk) (nd addrnd) =
      (External.signPureWithRandomizer S.vp S.prims (cv msg) (cv ctx) sk addrnd).toOption.map
        (sigBytes S) := by
  unfold Spec.slhSign
  by_cases hc : ctx.length > 255
  · rw [ite_eq_left hc]
    have hreq : External.encodePureMessage (cv ctx) (cv msg) =
        .error (.contextTooLong (cv ctx).length) := by
      unfold External.encodePureMessage External.encodeMessage
      rw [External.requireContext_eq_error _ (by rw [cv_length]; exact hc)]; rfl
    simp only [External.signPureWithRandomizer, hreq]
    rfl
  · rw [ite_eq_right hc, sign_eq]
    simp only [External.signPureWithRandomizer, cv_withContext msg ctx (by omega)]
    rfl

/-! ### Byte-level forms (secret key and outputs as wire bytes) -/

/-- VCVio's FIPS wire encoder of a secret key at the set (`encodeApprovedSecretKey S.fips`). -/
abbrev encodeSk (k : SecretKeyCore S.prims.core) : List UInt8 :=
  encodeSecretKey (sha2WireCodec S.vp.params) k

/-- VCVio's strict FIPS decoder of a secret key at the set (`decodeApprovedSecretKey S.fips`). -/
abbrev decodeSk (raw : List UInt8) : Except CodecError (SecretKeyCore S.prims.core) :=
  decodeSecretKey (sha2WireCodec S.vp.params) raw

theorem encodeSk_eq_approved : HEq (encodeSk S) (encodeApprovedSecretKey S.fips) := by
  cases S <;> rfl

theorem decodeSk_eq_approved : HEq (decodeSk S) (decodeApprovedSecretKey S.fips) := by
  cases S <;> rfl

/-- The spec reading of VCVio's secret-key wire encoding is
`SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`. -/
theorem sp_encodeSecretKey (k : SecretKeyCore S.prims.core) :
    sp (encodeSk S k) = skBytes S k := by
  show sp (encodeSecretKey (sha2WireCodec S.vp.params) k) = _
  rw [encodeSecretKey_eq, sp_append, sp_append, sp_append]
  rfl

theorem cv_skBytes (k : SecretKeyCore S.prims.core) : cv (skBytes S k) = encodeSk S k := by
  rw [← sp_encodeSecretKey, cv_sp]

theorem cv_sigBytes (s : GeneralScheme.SignatureCore S.vp S.prims.core) :
    cv (sigBytes S s) = encodeSig S s := by
  rw [← sp_encodeSignature, cv_sp]

theorem cv_pkBytes (k : PublicKeyCore S.prims.core) : cv (pkBytes S k) = encodePk S k := by
  rw [← sp_encodePublicKey, cv_sp]

/-- Every `4n`-byte string is the encoding of a (unique) typed secret key. -/
theorem decodeSk_ok (sk : Spec.Bytes) (hs : sk.length = 4 * S.spec.n) :
    ∃ k, decodeSk S (cv sk) = .ok k ∧ sk = skBytes S k := by
  obtain ⟨k, h⟩ := decode_ok_of_length (secretKeyCodec (sha2WireCodec S.vp.params)) (cv sk)
    (((cv_length sk).trans hs).trans (by rw [Params.secretKeyBytes, S.n_eq]))
  refine ⟨k, h, ?_⟩
  have h2 : cv sk = encodeSk S k :=
    (decodeSecretKey_eq_ok_iff (sha2WireCodec S.vp.params) (cv sk) k).mp h
  rw [← sp_encodeSecretKey, ← h2, sp_cv]

theorem decodeSk_skBytes (k : SecretKeyCore S.prims.core) :
    decodeSk S (cv (skBytes S k)) = .ok k := by
  rw [cv_skBytes]; exact decodeSecretKey_encode _ k

/-- Key generation on wire bytes: the right-hand side is definitionally
`Reduction.byteKeygen S.vp S.prims (sha2WireCodec S.vp.params) skSeed skPrf pkSeed`
(`(pk bytes, sk bytes)`). -/
theorem keygen_eq_bytes (skSeed skPrf pkSeed : S.Node) :
    (cv (Spec.slhKeygenInternal S.spec (nd skSeed) (nd skPrf) (nd pkSeed)).2,
     cv (Spec.slhKeygenInternal S.spec (nd skSeed) (nd skPrf) (nd pkSeed)).1) =
      (encodePk S (GeneralScheme.keygenInternal S.vp S.prims skSeed skPrf pkSeed).1,
       encodeSk S (GeneralScheme.keygenInternal S.vp S.prims skSeed skPrf pkSeed).2) := by
  rw [keygen_eq, cv_pkBytes, cv_skBytes]

/-- Internal signing on wire bytes, typed secret key: the right-hand side is that of
`Reduction.byteSign_encode`, so
`cv (Spec.slhSignInternal S.spec msg (skBytes S k) (nd addrnd)) =
  Reduction.byteSign S.vp S.prims (sha2WireCodec S.vp.params) (cv msg) (cv (skBytes S k)) addrnd`
by `rw [cv_skBytes, Reduction.byteSign_encode]`. -/
theorem sign_eq_enc (msg : Spec.Bytes) (k : SecretKeyCore S.prims.core) (addrnd : S.Node) :
    cv (Spec.slhSignInternal S.spec msg (skBytes S k) (nd addrnd)) =
      encodeSig S (GeneralScheme.signInternal S.vp S.prims (cv msg) k addrnd) := by
  rw [sign_eq, cv_sigBytes]

/-- External pure signing on wire bytes, typed secret key: the right-hand side is that of
`Reduction.byteSignPure_encode`. -/
theorem slhSign_eq_enc (msg ctx : Spec.Bytes) (k : SecretKeyCore S.prims.core) (addrnd : S.Node) :
    (Spec.slhSign S.spec msg ctx (skBytes S k) (nd addrnd)).map cv =
      (External.signPureWithRandomizer S.vp S.prims (cv msg) (cv ctx) k addrnd).toOption.map
        (encodeSig S) := by
  rw [slhSign_eq, Option.map_map]
  exact congrArg (fun f => Option.map f _) (funext fun s => cv_sigBytes S s)

/-- Internal signing on wire bytes, for every `4n`-byte secret key `sk`: `cv sk` decodes to a
typed key `k` and the spec's signature bytes are VCVio's encoded signature under `k`
(so `cv (Spec.slhSignInternal …) = Reduction.byteSign S.vp S.prims (sha2WireCodec S.vp.params)
(cv msg) (cv sk) addrnd` by `simp only [Reduction.byteSign, hk]`). -/
theorem sign_eq_bytes (msg sk : Spec.Bytes) (hs : sk.length = 4 * S.spec.n) (addrnd : S.Node) :
    ∃ k, decodeSk S (cv sk) = .ok k ∧ sk = skBytes S k ∧
      cv (Spec.slhSignInternal S.spec msg sk (nd addrnd)) =
        encodeSig S (GeneralScheme.signInternal S.vp S.prims (cv msg) k addrnd) := by
  obtain ⟨k, hk, rfl⟩ := decodeSk_ok S sk hs
  exact ⟨k, hk, rfl, sign_eq_enc S msg k addrnd⟩

/-- **External pure signing (FIPS 205 Algorithm 22) on wire bytes**, for every message, context,
`4n`-byte secret key `sk` and `addrnd`: `cv sk` decodes to a typed key `k`, and
`Spec.slhSign S.spec` (read as VCVio bytes) is `none` iff the context is longer than 255 bytes
and otherwise `some` of VCVio's encoded signature — i.e. it equals
`Reduction.byteSignPure S.vp S.prims (sha2WireCodec S.vp.params) (cv msg) (cv ctx) (cv sk) addrnd`
(by `simp only [Reduction.byteSignPure, hk]`). -/
theorem slhSign_eq_bytes (msg ctx sk : Spec.Bytes) (hs : sk.length = 4 * S.spec.n)
    (addrnd : S.Node) :
    ∃ k, decodeSk S (cv sk) = .ok k ∧ sk = skBytes S k ∧
      (Spec.slhSign S.spec msg ctx sk (nd addrnd)).map cv =
        (External.signPureWithRandomizer S.vp S.prims (cv msg) (cv ctx) k addrnd).toOption.map
          (encodeSig S) := by
  obtain ⟨k, hk, rfl⟩ := decodeSk_ok S sk hs
  exact ⟨k, hk, rfl, slhSign_eq_enc S msg ctx k addrnd⟩

end MLink

#print axioms MLink.htSign_eq
#print axioms MLink.sign_eq
#print axioms MLink.slhSign_eq
#print axioms MLink.keygen_eq_bytes
#print axioms MLink.sign_eq_bytes
#print axioms MLink.slhSign_eq_bytes
