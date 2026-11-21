import MLink.Hypertree
import MLink.Fors
import HashSig.SLHDSA.External

/-!
# `Spec.slhVerifyInternal` = VCVio's `GeneralScheme.verifyInternal`, all six SHA-2 parameter sets
-/

namespace MLink

open SLHDSA SLHDSA.Concrete

variable (S : Sha2Set)

/-! ### Numeric facts used below -/

theorem Sha2Set.xmssSigBytes_eq (S : Sha2Set) :
    S.spec.xmssSigBytes = (S.vp.params.len + S.vp.params.hp) * S.vp.params.n := by
  rw [Spec.Params.xmssSigBytes, S.len_eq, S.hp_eq, S.n_eq]

theorem Sha2Set.forsSigBytes_eq (S : Sha2Set) :
    S.spec.forsSigBytes = S.vp.params.k * ((S.vp.params.a + 1) * S.vp.params.n) := by
  rw [Spec.Params.forsSigBytes, S.k_eq, S.a_eq, S.n_eq]; ring

/-- The digest is cut into the same three pieces on both sides
(`m = ⌈k·a/8⌉ + ⌈(h − h')/8⌉ + ⌈h'/8⌉`; in particular 8 tree-index bytes at 256f). -/
theorem Sha2Set.m_split (S : Sha2Set) :
    S.spec.m = S.spec.mdBytes + S.spec.treeBytes + S.spec.leafBytes := S.spec_valid.m_eq

/-! ### Wire codecs -/

theorem ofFn_vec {α β : Type} {n : ℕ} (v : Vector α n) (f : α → β) :
    List.ofFn (fun i : Fin n => f v[i.val]) = v.toList.map f := by
  apply List.ext_getElem <;> simp

theorem flatMap_length_const {α β : Type} (l : List α) (f : α → List β) (c : ℕ)
    (h : ∀ x, (f x).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, h, Nat.succ_mul, Nat.add_comm]

@[simp] theorem nds_length' {n : ℕ} (ys : List (Bytes n)) : (nds ys).length = ys.length * n :=
  flatMap_length_const ys nd n nd_length

theorem xmssBytes_length (s : XmssSig S.vp.params S.prims) :
    (xmssBytes S s).length = S.spec.xmssSigBytes :=
  calc (xmssBytes S s).length
      = (nds s.wots.toList).length + (nds s.auth.toList).length := List.length_append
    _ = S.vp.params.len * S.vp.params.n + S.vp.params.hp * S.vp.params.n := congrArg₂ (· + ·)
        ((nds_length' _).trans (congrArg (· * S.vp.params.n) Vector.length_toList))
        ((nds_length' _).trans (congrArg (· * S.vp.params.n) Vector.length_toList))
    _ = S.spec.xmssSigBytes := by rw [S.xmssSigBytes_eq]; ring

theorem htBytes_length (s : HtSigCore S.vp.params S.prims.core) :
    (htBytes S s).length = S.spec.d * S.spec.xmssSigBytes := by
  rw [htBytes, flatMap_length_const _ _ _ (xmssBytes_length S), Vector.length_toList, S.d_eq]

theorem forsBytes_length (s : ForsSigCore S.vp.params S.prims.core) :
    (forsBytes S s).length = S.spec.forsSigBytes := by
  rw [forsBytes, flatMap_length_const _ _ _ (forsTree_length S), Vector.length_toList,
    S.forsSigBytes_eq]

theorem cv_append (a b : Spec.Bytes) : cv (a ++ b) = cv a ++ cv b := by simp [cv]

theorem cv_nds {n : ℕ} (l : List (Bytes n)) : cv (nds l) = (l.map Vector.toList).flatten := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [nds, List.flatMap_cons, List.map_cons, List.flatten_cons] at ih ⊢
    rw [cv_append, ih, nd, cv_sp]

theorem enc_helper1 {n : ℕ} (y : Bytes n) (l : List (Bytes n)) :
    y.toList ++ (l.map Vector.toList).flatten = cv (nd y ++ nds l) := by
  rw [cv_append, cv_nds, nd, cv_sp]

theorem enc_helper2 {n : ℕ} (l1 l2 : List (Bytes n)) :
    (l1.map Vector.toList).flatten ++ (l2.map Vector.toList).flatten = cv (nds l1 ++ nds l2) := by
  rw [cv_append, cv_nds, cv_nds]

theorem sp_flatten_map_cv {α : Type} (l : List α) (g : α → Spec.Bytes) :
    sp ((l.map fun t => cv (g t)).flatten) = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons y ys ih => simp [ih]

/-- VCVio's FIPS wire encoder of a signature at the set (`encodeApprovedSignature S.fips`, see
`encodeSig_eq_approved`; stated at `S.prims` because `approvedPrimitives S.fips` reduces to
`S.prims` only once `S` is a constructor). -/
abbrev encodeSig (s : GeneralScheme.SignatureCore S.vp S.prims.core) : List UInt8 :=
  encodeSignature S.vp (sha2WireCodec S.vp.params) s

/-- VCVio's FIPS wire encoder of a public key at the set (`encodeApprovedPublicKey S.fips`). -/
abbrev encodePk (k : PublicKeyCore S.prims.core) : List UInt8 :=
  encodePublicKey (sha2WireCodec S.vp.params) k

theorem encodeSig_eq_approved : HEq (encodeSig S) (encodeApprovedSignature S.fips) := by
  cases S <;> rfl

theorem encodePk_eq_approved : HEq (encodePk S) (encodeApprovedPublicKey S.fips) := by
  cases S <;> rfl

/-- The spec reading of VCVio's signature wire encoding is `R ‖ SIG_FORS ‖ SIG_HT`. -/
theorem sp_encodeSignature (s : GeneralScheme.SignatureCore S.vp S.prims.core) :
    sp (encodeSig S s) = sigBytes S s := by
  show sp (encodeSignature S.vp (sha2WireCodec S.vp.params) s) = _
  rw [encodeSignature_eq]
  dsimp only [sha2WireCodec, WireCodec.encode, WireCodec.bytes, Equiv.refl, Equiv.coe_fn_mk, id]
  erw [ofFn_vec s.fors (fun t => t.sk.toList ++
      (List.ofFn fun node : Fin S.vp.params.a => t.auth[node.val].toList).flatten),
    ofFn_vec s.hypertree (fun x =>
      (List.ofFn fun chain : Fin S.vp.params.len => x.wots[chain.val].toList).flatten ++
      (List.ofFn fun node : Fin S.vp.params.hp => x.auth[node.val].toList).flatten)]
  have hF : ∀ t : ForsTreeSigCore S.vp.params S.prims.core,
      (Vector.toList (α := UInt8) (n := S.vp.params.n) t.sk ++
        (List.ofFn fun node : Fin S.vp.params.a =>
          Vector.toList (α := UInt8) (n := S.vp.params.n) t.auth[node.val]).flatten : List UInt8) =
        cv (nd t.sk ++ nds t.auth.toList) := fun t =>
    (congrArg (fun z => Vector.toList (α := UInt8) (n := S.vp.params.n) t.sk ++ List.flatten z)
      (ofFn_vec t.auth _)).trans
      (enc_helper1 _ _)
  have hH : ∀ x : XmssSig S.vp.params S.prims.core,
      ((List.ofFn fun chain : Fin S.vp.params.len =>
          Vector.toList (α := UInt8) (n := S.vp.params.n) x.wots[chain.val]).flatten ++
        (List.ofFn fun node : Fin S.vp.params.hp =>
          Vector.toList (α := UInt8) (n := S.vp.params.n) x.auth[node.val]).flatten : List UInt8) =
        cv (xmssBytes S x) := fun x =>
    (congrArg₂ (fun z w => List.flatten z ++ List.flatten w)
      (ofFn_vec x.wots _) (ofFn_vec x.auth _)).trans
      (enc_helper2 _ _)
  refine (congrArg sp (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·)
    (congrArg List.flatten (List.map_congr_left fun t _ => hF t))
    (congrArg List.flatten (List.map_congr_left fun x _ => hH x))))).trans ?_
  show _ = nd _ ++ forsBytes S _ ++ htBytes S _
  rw [List.append_assoc]
  exact (sp_append _ _).trans (congrArg₂ (· ++ ·) rfl ((sp_append _ _).trans
    (congrArg₂ (· ++ ·) (sp_flatten_map_cv _ _) (sp_flatten_map_cv _ _))))

/-- The spec reading of VCVio's public-key wire encoding is `PK.seed ‖ PK.root`. -/
theorem sp_encodePublicKey (k : PublicKeyCore S.prims.core) :
    sp (encodePk S k) = pkBytes S k := by
  show sp (encodePublicKey (sha2WireCodec S.vp.params) k) = _
  rw [encodePublicKey_eq, sp_append]
  rfl

theorem sigBytes_length (s : GeneralScheme.SignatureCore S.vp S.prims.core) :
    (sigBytes S s).length = S.spec.sigBytes := by
  rw [← sp_encodeSignature, sp_length, ← S.signatureBytes_eq]
  exact encodeSignature_length S.vp (sha2WireCodec S.vp.params) s

theorem pkBytes_length (k : PublicKeyCore S.prims.core) : (pkBytes S k).length = 2 * S.spec.n := by
  have h1 : (nd k.pkSeed).length = S.vp.params.n := nd_length _
  have h2 : (nd k.pkRoot).length = S.vp.params.n := nd_length _
  rw [pkBytes, List.length_append, h1, h2, S.n_eq]; ring

theorem decode_ok_of_length {α : Type} {width : ℕ} (codec : WireCodec α width)
    (raw : List Byte) (h : raw.length = width) : ∃ v, codec.decode raw = .ok v := by
  simp [WireCodec.decode, decodeExact, h, Except.map]

/-! ### The typed core -/

theorem nd_beq {n : ℕ} (x y : Bytes n) : (nd x == nd y) = decide (x = y) := by
  by_cases h : x = y
  · simp [h]
  · have : nd x ≠ nd y := fun h' => h (nd_injective h')
    simp [h, this]

/-- The spec-side FORS address of Algorithm 20. -/
def specForsAdrs (idxTree idxLeaf : Nat) : Spec.Adrs :=
  { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear Spec.FORS_TREE with keypair := idxLeaf }

/-! #### The digest split (Algorithm 19 lines 6–10) agrees -/

theorem splitDigest_md (dg : Bytes S.vp.params.m) :
    sp (splitDigest S.vp.params dg).md.toList = (sp dg.toList).take S.spec.mdBytes := by
  rw [splitDigest_md_toList, sp_take, S.digestBytes_eq]

theorem splitDigest_tree (dg : Bytes S.vp.params.m) :
    (splitDigest S.vp.params dg).idxTree.val = Spec.digestTree S.spec (sp dg.toList) := by
  rw [splitDigest_idxTree_val, toInt_eq, sp_take, sp_drop, Spec.digestTree, S.digestBytes_eq,
    S.treeIdxBytes_eq, S.h_eq, S.hp_eq, S.h_div_d]

theorem splitDigest_leaf (dg : Bytes S.vp.params.m) :
    (splitDigest S.vp.params dg).idxLeaf.val = Spec.digestLeaf S.spec (sp dg.toList) := by
  rw [splitDigest_idxLeaf_val, toInt_eq, sp_take, sp_drop, Spec.digestLeaf, S.digestBytes_eq,
    S.treeIdxBytes_eq, S.leafIdxBytes_eq, S.hp_eq, S.h_div_d]

/-- The FORS address derived from any digest is in the SHA-2 domain. -/
theorem forsAdrs_dom (parts : DigestParts S.vp.params) : ForsDom parts.forsAdrs := by
  have htlt : parts.idxTree.val < 2 ^ 64 :=
    lt_of_lt_of_le parts.idxTree.isLt (Nat.pow_le_pow_right (by norm_num) S.tree_bits_le)
  have hllt : parts.idxLeaf.val < 2 ^ 32 :=
    lt_of_lt_of_le parts.idxLeaf.isLt
      (Nat.pow_le_pow_right (by norm_num) (le_trans S.hp_le (by norm_num)))
  exact ⟨rfl, by show (0 : ℕ) < 256; omega, htlt, hllt⟩

/-- The recomputed hypertree root agrees (everything in Algorithm 20 except the final test). -/
theorem root_eq (dg : Bytes S.vp.params.m) (s : GeneralScheme.SignatureCore S.vp S.prims.core)
    (pk : S.Node) :
    nd (GeneralHypertree.pkFromSig S.vp S.prims
        (forsPkFromSig S.prims s.fors (splitDigest S.vp.params dg).md.toList pk
          (splitDigest S.vp.params dg).forsAdrs)
        s.hypertree pk (splitDigest S.vp.params dg)) =
      specHtRoot S
        (Spec.forsPkFromSig S.spec (forsBytes S s.fors) ((sp dg.toList).take S.spec.mdBytes) (nd pk)
          (specForsAdrs (Spec.digestTree S.spec (sp dg.toList))
            (Spec.digestLeaf S.spec (sp dg.toList))))
        (htBytes S s.hypertree) (nd pk)
        (Spec.digestTree S.spec (sp dg.toList)) (Spec.digestLeaf S.spec (sp dg.toList)) := by
  have hmd := splitDigest_md S dg
  have ht := splitDigest_tree S dg
  have hl := splitDigest_leaf S dg
  generalize splitDigest S.vp.params dg = parts at hmd ht hl ⊢
  have hfors := forsPkFromSig_eq S s.fors parts.md.toList (Vector.length_toList) pk parts.forsAdrs
    (forsAdrs_dom S parts)
  refine (congrArg nd
    (GeneralHypertree.pkFromSig_eq_recoverFromPosition S.vp S.prims _ _ _ _)).trans ?_
  have hrec := recover_eq S pk S.vp.params.d (LayerPosition.initial S.vp parts) (by simp)
    (forsPkFromSig S.prims s.fors parts.md.toList pk parts.forsAdrs) s.hypertree
  refine hrec.trans ?_
  rw [hfors, hmd]
  have hchunks : htBytes S s.hypertree = (s.hypertree.toList.map (xmssBytes S)).flatten := by
    rw [htBytes, List.flatMap_def]
  rw [hchunks, specHtRoot_eq_htGo S _ _ _ _ _ (by simp [S.d_eq])
    (by intro c hc; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hc; exact xmssBytes_length S x)]
  rw [← ht, ← hl]
  rfl

/-- **Verification agrees on typed inputs.** For every message, typed signature and typed public
key, the spec's verifier on the flat FIPS encodings equals VCVio's executable verifier. -/
theorem verify_eq_typed (msg : Spec.Bytes) (s : GeneralScheme.SignatureCore S.vp S.prims.core)
    (k : PublicKeyCore S.prims.core) :
    Spec.slhVerifyInternal S.spec msg (sigBytes S s) (pkBytes S k) =
      GeneralScheme.verifyInternal S.vp S.prims (cv msg) s k := by
  have hlen := sigBytes_length S s
  have hn : S.spec.n = S.vp.params.n := S.n_eq.symm
  have hR : (sigBytes S s).take S.spec.n = nd s.randomness := by
    simp only [sigBytes, List.append_assoc, hn]; exact List.take_left' (nd_length _)
  have hF : ((sigBytes S s).drop S.spec.n).take S.spec.forsSigBytes = forsBytes S s.fors := by
    simp only [sigBytes, List.append_assoc, hn]
    exact (congrArg (List.take _) (List.drop_left' (nd_length _))).trans
      (List.take_left' (forsBytes_length S _))
  have hH : (sigBytes S s).drop (S.spec.n + S.spec.forsSigBytes) = htBytes S s.hypertree := by
    rw [sigBytes]
    exact List.drop_left' (List.length_append.trans
      (congrArg₂ (· + ·) ((nd_length _).trans hn.symm) (forsBytes_length S _)))
  have hk0 : Spec.block S.spec (pkBytes S k) 0 = nd k.pkSeed := by
    simp only [Spec.block, pkBytes, Nat.zero_mul, List.drop_zero, hn]
    exact List.take_left' (nd_length _)
  have hk1 : Spec.block S.spec (pkBytes S k) 1 = nd k.pkRoot := by
    simp only [Spec.block, pkBytes, Nat.one_mul, hn]
    exact (congrArg (List.take _) (List.drop_left' (nd_length _))).trans
      (List.take_of_length_le (Nat.le_of_eq (nd_length _)))
  have hdg : sp (S.prims.Hmsg s.randomness k.pkSeed k.pkRoot (cv msg)).toList =
      Spec.Hmsg S.spec (nd s.randomness) (nd k.pkSeed) (nd k.pkRoot) msg := by
    exact (Hmsg_eq S _ _ _ _).trans (congrArg (Spec.Hmsg S.spec _ _ _) (sp_cv msg))
  rw [GeneralScheme.verifyInternal_eq_decide]
  unfold Spec.slhVerifyInternal
  rw [ite_eq_right (not_not.mpr hlen)]
  simp only [hR, hF, hH, hk0, hk1, htVerify_eq]
  have hroot := root_eq S (S.prims.Hmsg s.randomness k.pkSeed k.pkRoot (cv msg)) s k.pkSeed
  rw [hdg] at hroot
  exact (congrArg (· == nd k.pkRoot) hroot.symm).trans (nd_beq _ _)

/-! ### The byte-level statements -/

/-- VCVio's strict FIPS decoder of a signature at the set: `decodeApprovedSignature S.fips`
(`decodeSig_eq_approved`; definitionally so at each of the six sets). -/
abbrev decodeSig (raw : List UInt8) :
    Except CodecError (GeneralScheme.SignatureCore S.vp S.prims.core) :=
  SLHDSA.decodeSignature S.vp (sha2WireCodec S.vp.params) raw

/-- VCVio's strict FIPS decoder of a public key at the set: `decodeApprovedPublicKey S.fips`
(`decodePk_eq_approved`). -/
abbrev decodePk (raw : List UInt8) : Except CodecError (PublicKeyCore S.prims.core) :=
  decodePublicKey (sha2WireCodec S.vp.params) raw

theorem decodeSig_eq_approved : HEq (decodeSig S) (decodeApprovedSignature S.fips) := by
  cases S <;> rfl

theorem decodePk_eq_approved : HEq (decodePk S) (decodeApprovedPublicKey S.fips) := by
  cases S <;> rfl

example : decodeSig .s128s = decodeApprovedSignature .SLHDSA_SHA2_128s := rfl
example : decodeSig .s128f = decodeApprovedSignature .SLHDSA_SHA2_128f := rfl
example : decodeSig .s192s = decodeApprovedSignature .SLHDSA_SHA2_192s := rfl
example : decodeSig .s192f = decodeApprovedSignature .SLHDSA_SHA2_192f := rfl
example : decodeSig .s256s = decodeApprovedSignature .SLHDSA_SHA2_256s := rfl
example : decodeSig .s256f = decodeApprovedSignature .SLHDSA_SHA2_256f := rfl
example : decodePk .s128s = decodeApprovedPublicKey .SLHDSA_SHA2_128s := rfl
example : decodePk .s128f = decodeApprovedPublicKey .SLHDSA_SHA2_128f := rfl
example : decodePk .s192s = decodeApprovedPublicKey .SLHDSA_SHA2_192s := rfl
example : decodePk .s192f = decodeApprovedPublicKey .SLHDSA_SHA2_192f := rfl
example : decodePk .s256s = decodeApprovedPublicKey .SLHDSA_SHA2_256s := rfl
example : decodePk .s256f = decodeApprovedPublicKey .SLHDSA_SHA2_256f := rfl

theorem decodeSig_ok (sig : Spec.Bytes) (hs : sig.length = S.spec.sigBytes) :
    ∃ s, decodeSig S (cv sig) = .ok s ∧ sig = sigBytes S s := by
  obtain ⟨s, h⟩ := decode_ok_of_length (signatureCodec S.vp (sha2WireCodec S.vp.params)) (cv sig)
    (((cv_length sig).trans hs).trans S.signatureBytes_eq.symm)
  refine ⟨s, h, ?_⟩
  have h2 : cv sig = encodeSig S s :=
    (decodeSignature_eq_ok_iff S.vp (sha2WireCodec S.vp.params) (cv sig) s).mp h
  rw [← sp_encodeSignature, ← h2, sp_cv]

theorem decodeSig_error (sig : Spec.Bytes) (hs : sig.length ≠ S.spec.sigBytes) :
    ∃ e, decodeSig S (cv sig) = .error e :=
  ⟨_, WireCodec.decode_eq_error_of_length_ne (signatureCodec S.vp (sha2WireCodec S.vp.params))
    (cv sig) (by rw [cv_length, S.signatureBytes_eq]; exact hs)⟩

theorem decodePk_ok (pk : Spec.Bytes) (hp : pk.length = 2 * S.spec.n) :
    ∃ k, decodePk S (cv pk) = .ok k ∧ pk = pkBytes S k := by
  obtain ⟨k, h⟩ := decode_ok_of_length (publicKeyCodec (sha2WireCodec S.vp.params)) (cv pk)
    (((cv_length pk).trans hp).trans (by rw [Params.publicKeyBytes, S.n_eq]))
  refine ⟨k, h, ?_⟩
  have h2 : cv pk = encodePk S k :=
    (decodePublicKey_eq_ok_iff (sha2WireCodec S.vp.params) (cv pk) k).mp h
  rw [← sp_encodePublicKey, ← h2, sp_cv]

/-- **Main theorem (internal verification, FIPS 205 Algorithm 20), all six SHA-2 sets.**  For
every message, every byte string offered as a signature and every `2n`-byte public key, our
specification's `Spec.slhVerifyInternal S.spec` returns exactly what VCVio's executable
`GeneralScheme.verifyInternal` at the set (`S.vp = S.fips.validatedParams`,
`S.prims = approvedPrimitives S.fips`, `decodeSig S = decodeApprovedSignature S.fips`,
`decodePk S = decodeApprovedPublicKey S.fips`) returns on the values VCVio's own strict
decoders produce; a signature of the wrong length (the only way the signature decoder can
fail) is rejected by both sides. -/
theorem verify_eq (msg sig pk : Spec.Bytes) (hp : pk.length = 2 * S.spec.n) :
    Spec.slhVerifyInternal S.spec msg sig pk =
      match decodeSig S (cv sig), decodePk S (cv pk) with
      | .ok s, .ok k =>
        GeneralScheme.verifyInternal S.vp S.prims (cv msg) s k
      | _, _ => false := by
  obtain ⟨k, hk, rfl⟩ := decodePk_ok S pk hp
  by_cases hs : sig.length = S.spec.sigBytes
  · obtain ⟨s, hsd, rfl⟩ := decodeSig_ok S sig hs
    rw [hsd, hk]
    exact verify_eq_typed S msg s k
  · obtain ⟨e, he⟩ := decodeSig_error S sig hs
    have h1 : decodeSig S (cv sig) = .error e := he
    rw [h1]
    unfold Spec.slhVerifyInternal
    exact ite_eq_left hs

/-- The same statement with both lengths assumed: the decoders succeed and the verdicts agree. -/
theorem verify_eq' (msg sig pk : Spec.Bytes) (hs : sig.length = S.spec.sigBytes)
    (hp : pk.length = 2 * S.spec.n) :
    ∃ s k, decodeSig S (cv sig) = .ok s ∧
      decodePk S (cv pk) = .ok k ∧
      Spec.slhVerifyInternal S.spec msg sig pk =
        GeneralScheme.verifyInternal S.vp S.prims (cv msg) s k := by
  obtain ⟨k, hk, rfl⟩ := decodePk_ok S pk hp
  obtain ⟨s, hsd, rfl⟩ := decodeSig_ok S sig hs
  exact ⟨s, k, hsd, hk, verify_eq_typed S msg s k⟩

/-- **External verification (FIPS 205 Algorithm 24, pure mode), all six SHA-2 sets.**
`Spec.slhVerify S.spec` equals VCVio's `External.verifyPure` on the decoded values, for every
context (an over-long context is rejected by both). -/
theorem slhVerify_eq (msg sig ctx pk : Spec.Bytes) (hp : pk.length = 2 * S.spec.n) :
    Spec.slhVerify S.spec msg sig ctx pk =
      match decodeSig S (cv sig), decodePk S (cv pk) with
      | .ok s, .ok k =>
        External.verifyPure S.vp S.prims (cv msg) s (cv ctx) k
      | _, _ => false := by
  unfold Spec.slhVerify
  by_cases hc : ctx.length > 255
  · rw [ite_eq_left hc]
    have hreq : External.encodePureMessage (cv ctx) (cv msg) =
        .error (.contextTooLong (cv ctx).length) := by
      unfold External.encodePureMessage External.encodeMessage
      rw [External.requireContext_eq_error _ (by rw [cv_length]; exact hc)]; rfl
    split <;> simp [External.verifyPure, hreq]
  · rw [ite_eq_right hc, verify_eq S _ _ _ hp]
    have hreq := External.encodePureMessage_eq_ok (cv ctx) (cv msg)
      (by rw [cv_length]; omega)
    have hm : cv (Spec.withContext msg ctx) =
        [0, UInt8.ofNat (cv ctx).length] ++ cv ctx ++ cv msg := by
      have h255 : ctx.length < 256 := by omega
      simp [Spec.withContext, Spec.toByte, cv, List.range_succ]
      rfl
    split <;> simp [External.verifyPure, hreq, hm]

end MLink

#print axioms MLink.verify_eq_typed
#print axioms MLink.verify_eq
#print axioms MLink.verify_eq'
#print axioms MLink.slhVerify_eq
