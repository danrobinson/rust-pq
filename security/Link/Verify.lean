import Link.Hypertree
import Link.Fors
import HashSig.SLHDSA.External

/-!
# `Spec.slhVerifyInternal` = VCVio's `GeneralScheme.verifyInternal` at SLH-DSA-SHA2-128s
-/

namespace Link

open SLHDSA SLHDSA.Concrete

/-! ### Wire codecs -/

theorem ofFn_vec {α β : Type} {n : ℕ} (v : Vector α n) (f : α → β) :
    List.ofFn (fun i : Fin n => f v[i.val]) = v.toList.map f := by
  apply List.ext_getElem <;> simp

theorem flatMap_length_const {α β : Type} (l : List α) (f : α → List β) (c : ℕ)
    (h : ∀ x, (f x).length = c) : (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, h, Nat.succ_mul, Nat.add_comm]

@[simp] theorem nds_length' (ys : List Node) : (nds ys).length = ys.length * 16 :=
  flatMap_length_const ys nd 16 nd_length

theorem xmssBytes_length (s : XmssSig vp.params prims) :
    (xmssBytes s).length = Spec.xmssSigBytes :=
  calc (xmssBytes s).length
      = (nds s.wots.toList).length + (nds s.auth.toList).length := List.length_append
    _ = 35 * 16 + 9 * 16 := congrArg₂ (· + ·)
        ((nds_length' _).trans (congrArg (· * 16) Vector.length_toList))
        ((nds_length' _).trans (congrArg (· * 16) Vector.length_toList))

theorem htBytes_length (s : HtSigCore vp.params prims.core) : (htBytes s).length = 7 * 704 := by
  rw [htBytes, flatMap_length_const _ _ _ xmssBytes_length]; simp; rfl

theorem forsBytes_length (s : ForsSigCore vp.params prims.core) :
    (forsBytes s).length = Spec.forsSigBytes := by
  rw [forsBytes, flatMap_length_const _ _ (13 * 16)]
  · simp; rfl
  · intro t
    calc (nd t.sk ++ nds t.auth.toList).length
        = (nd t.sk).length + (nds t.auth.toList).length := List.length_append
      _ = 16 + 12 * 16 := congrArg₂ (· + ·) (nd_length _)
          ((nds_length' _).trans (congrArg (· * 16) Vector.length_toList))

theorem cv_append (a b : Spec.Bytes) : cv (a ++ b) = cv a ++ cv b := by simp [cv]

theorem cv_nds (l : List Node) : cv (nds l) = (l.map Vector.toList).flatten := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [nds, List.flatMap_cons, List.map_cons, List.flatten_cons] at ih ⊢
    rw [cv_append, ih, nd, cv_sp]

theorem enc_helper1 (y : Node) (l : List Node) :
    y.toList ++ (l.map Vector.toList).flatten = cv (nd y ++ nds l) := by
  rw [cv_append, cv_nds, nd, cv_sp]

theorem enc_helper2 (l1 l2 : List Node) :
    (l1.map Vector.toList).flatten ++ (l2.map Vector.toList).flatten = cv (nds l1 ++ nds l2) := by
  rw [cv_append, cv_nds, cv_nds]

theorem sp_flatten_map_cv {α : Type} (l : List α) (g : α → Spec.Bytes) :
    sp ((l.map fun t => cv (g t)).flatten) = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons y ys ih => simp [ih]

/-- The spec reading of VCVio's signature wire encoding is `R ‖ SIG_FORS ‖ SIG_HT`. -/
theorem sp_encodeSignature (s : GeneralScheme.SignatureCore vp prims.core) :
    sp (encodeApprovedSignature S128 s) = sigBytes s := by
  show sp (encodeSignature vp (sha2WireCodec vp.params) s) = _
  rw [encodeSignature_eq]
  dsimp only [sha2WireCodec, WireCodec.encode, WireCodec.bytes, Equiv.refl, Equiv.coe_fn_mk, id]
  erw [ofFn_vec s.fors (fun t => t.sk.toList ++
      (List.ofFn fun node : Fin vp.params.a => t.auth[node.val].toList).flatten),
    ofFn_vec s.hypertree (fun x =>
      (List.ofFn fun chain : Fin vp.params.len => x.wots[chain.val].toList).flatten ++
      (List.ofFn fun node : Fin vp.params.hp => x.auth[node.val].toList).flatten)]
  have hF : ∀ t : ForsTreeSigCore vp.params prims.core,
      (Vector.toList (α := UInt8) (n := 16) t.sk ++ (List.ofFn fun node : Fin vp.params.a =>
        Vector.toList (α := UInt8) (n := 16) t.auth[node.val]).flatten : List UInt8) =
        cv (nd t.sk ++ nds t.auth.toList) := fun t =>
    (congrArg (fun z => Vector.toList (α := UInt8) (n := 16) t.sk ++ List.flatten z)
      (ofFn_vec t.auth _)).trans
      (enc_helper1 _ _)
  have hH : ∀ x : XmssSig vp.params prims.core,
      ((List.ofFn fun chain : Fin vp.params.len =>
          Vector.toList (α := UInt8) (n := 16) x.wots[chain.val]).flatten ++
        (List.ofFn fun node : Fin vp.params.hp =>
          Vector.toList (α := UInt8) (n := 16) x.auth[node.val]).flatten : List UInt8) =
        cv (xmssBytes x) := fun x =>
    (congrArg₂ (fun z w => List.flatten z ++ List.flatten w)
      (ofFn_vec x.wots _) (ofFn_vec x.auth _)).trans
      (enc_helper2 _ _)
  refine (congrArg sp (congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·)
    (congrArg List.flatten (List.map_congr_left fun t _ => hF t))
    (congrArg List.flatten (List.map_congr_left fun x _ => hH x))))).trans ?_
  show _ = nd _ ++ forsBytes _ ++ htBytes _
  rw [List.append_assoc]
  exact (sp_append _ _).trans (congrArg₂ (· ++ ·) rfl ((sp_append _ _).trans
    (congrArg₂ (· ++ ·) (sp_flatten_map_cv _ _) (sp_flatten_map_cv _ _))))

/-- The spec reading of VCVio's public-key wire encoding is `PK.seed ‖ PK.root`. -/
theorem sp_encodePublicKey (k : PublicKeyCore prims.core) :
    sp (encodeApprovedPublicKey S128 k) = pkBytes k := by
  show sp (encodePublicKey (sha2WireCodec vp.params) k) = _
  rw [encodePublicKey_eq, sp_append]
  rfl

theorem sigBytes_length (s : GeneralScheme.SignatureCore vp prims.core) :
    (sigBytes s).length = 7856 := by
  rw [← sp_encodeSignature, sp_length]
  exact encodeApprovedSignature_length S128 s

theorem decode_ok_of_length {α : Type} {width : ℕ} (codec : WireCodec α width)
    (raw : List Byte) (h : raw.length = width) : ∃ v, codec.decode raw = .ok v := by
  simp [WireCodec.decode, decodeExact, h, Except.map]

/-! ### The typed core -/

theorem nd_beq (x y : Node) : (nd x == nd y) = decide (x = y) := by
  by_cases h : x = y
  · simp [h]
  · have : nd x ≠ nd y := fun h' => h (nd_injective h')
    simp [h, this]

/-- The spec-side FORS address of Algorithm 20. -/
def specForsAdrs (idxTree idxLeaf : Nat) : Spec.Adrs :=
  { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear Spec.FORS_TREE with keypair := idxLeaf }

/-- The recomputed hypertree root agrees (everything in Algorithm 20 except the final test). -/
theorem root_eq (dg : Bytes vp.params.m) (s : GeneralScheme.SignatureCore vp prims.core) (pk : Node) :
    nd (GeneralHypertree.pkFromSig vp prims
        (forsPkFromSig prims s.fors (splitDigest vp.params dg).md.toList pk
          (splitDigest vp.params dg).forsAdrs)
        s.hypertree pk (splitDigest vp.params dg)) =
      specHtRoot
        (Spec.forsPkFromSig (forsBytes s.fors) ((sp dg.toList).take Spec.mdBytes) (nd pk)
          (specForsAdrs (Spec.digestTree (sp dg.toList)) (Spec.digestLeaf (sp dg.toList))))
        (htBytes s.hypertree) (nd pk)
        (Spec.digestTree (sp dg.toList)) (Spec.digestLeaf (sp dg.toList)) := by
  generalize hparts : splitDigest vp.params dg = parts
  have hmd : sp parts.md.toList = (sp dg.toList).take Spec.mdBytes := by
    rw [← hparts, splitDigest_md_toList, sp_take]; rfl
  have ht : parts.idxTree.val = Spec.digestTree (sp dg.toList) := by
    rw [← hparts, splitDigest_idxTree_val, toInt_eq, sp_take, sp_drop]; rfl
  have hl : parts.idxLeaf.val = Spec.digestLeaf (sp dg.toList) := by
    rw [← hparts, splitDigest_idxLeaf_val, toInt_eq, sp_take, sp_drop]; rfl
  have htlt : parts.idxTree.val < 2 ^ 54 := parts.idxTree.isLt
  have hllt : parts.idxLeaf.val < 2 ^ 9 := parts.idxLeaf.isLt
  have hfors := forsPkFromSig_eq s.fors parts.md.toList (Vector.length_toList) pk parts.forsAdrs
    ⟨rfl, by show (0 : ℕ) < 256; omega,
     by show parts.idxTree.val < 2 ^ 64; omega, by show parts.idxLeaf.val < 2 ^ 32; omega⟩
  refine (congrArg nd (GeneralHypertree.pkFromSig_eq_recoverFromPosition vp prims _ _ _ _)).trans ?_
  have hrec := recover_eq pk vp.params.d (LayerPosition.initial vp parts) (by simp)
    (forsPkFromSig prims s.fors parts.md.toList pk parts.forsAdrs) s.hypertree
  refine hrec.trans ?_
  rw [hfors, hmd]
  have hchunks : htBytes s.hypertree = (s.hypertree.toList.map xmssBytes).flatten := by
    rw [htBytes, List.flatMap_def]
  rw [hchunks, specHtRoot_eq_htGo _ _ _ _ _ (by simp; rfl)
    (by intro c hc; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hc; exact xmssBytes_length x)]
  rw [← ht, ← hl]
  rfl

/-- **Verification agrees on typed inputs.** For every message, typed signature and typed public
key, the spec's verifier on the flat FIPS encodings equals VCVio's executable verifier. -/
theorem verify_eq_typed (msg : Spec.Bytes) (s : GeneralScheme.SignatureCore vp prims.core)
    (k : PublicKeyCore prims.core) :
    Spec.slhVerifyInternal msg (sigBytes s) (pkBytes k) =
      GeneralScheme.verifyInternal vp prims (cv msg) s k := by
  have hlen := sigBytes_length s
  have hR : (sigBytes s).take Spec.n = nd s.randomness := by
    simp only [sigBytes, List.append_assoc]; exact List.take_left' (nd_length _)
  have hF : ((sigBytes s).drop Spec.n).take Spec.forsSigBytes = forsBytes s.fors := by
    simp only [sigBytes, List.append_assoc]
    exact (congrArg (List.take _) (List.drop_left' (nd_length _))).trans
      (List.take_left' (forsBytes_length _))
  have hH : (sigBytes s).drop (Spec.n + Spec.forsSigBytes) = htBytes s.hypertree := by
    rw [sigBytes]
    exact List.drop_left' (List.length_append.trans
      (congrArg₂ (· + ·) (nd_length _) (forsBytes_length _)))
  have hk0 : Spec.block (pkBytes k) 0 = nd k.pkSeed := by
    simp only [Spec.block, pkBytes, Nat.zero_mul, List.drop_zero]
    exact List.take_left' (nd_length _)
  have hk1 : Spec.block (pkBytes k) 1 = nd k.pkRoot := by
    simp only [Spec.block, pkBytes, Nat.one_mul]
    exact (congrArg (List.take _) (List.drop_left' (nd_length _))).trans
      (List.take_of_length_le (Nat.le_of_eq (nd_length _)))
  have hdg : sp (prims.Hmsg s.randomness k.pkSeed k.pkRoot (cv msg)).toList =
      Spec.Hmsg (nd s.randomness) (nd k.pkSeed) (nd k.pkRoot) msg := by
    exact (Hmsg_eq _ _ _ _).trans (congrArg (Spec.Hmsg _ _ _) (sp_cv msg))
  rw [GeneralScheme.verifyInternal_eq_decide]
  unfold Spec.slhVerifyInternal
  rw [ite_eq_right (by rw [hlen]; decide)]
  simp only [hR, hF, hH, hk0, hk1, htVerify_eq]
  have hroot := root_eq (prims.Hmsg s.randomness k.pkSeed k.pkRoot (cv msg)) s k.pkSeed
  rw [hdg] at hroot
  exact (congrArg (· == nd k.pkRoot) hroot.symm).trans (nd_beq _ _)

/-! ### The byte-level statements -/

/-- VCVio's strict FIPS decoder of a signature for SLH-DSA-SHA2-128s. -/
abbrev decodeSig (raw : List UInt8) :
    Except CodecError (GeneralScheme.SignatureCore vp prims.core) :=
  decodeApprovedSignature S128 raw

/-- VCVio's strict FIPS decoder of a public key for SLH-DSA-SHA2-128s. -/
abbrev decodePk (raw : List UInt8) : Except CodecError (PublicKeyCore prims.core) :=
  decodeApprovedPublicKey S128 raw

theorem decodeSig_ok (sig : Spec.Bytes) (hs : sig.length = 7856) :
    ∃ s, decodeSig (cv sig) = .ok s ∧ sig = sigBytes s := by
  obtain ⟨s, h⟩ := decode_ok_of_length (signatureCodec vp (sha2WireCodec vp.params)) (cv sig)
    ((cv_length sig).trans hs)
  refine ⟨s, h, ?_⟩
  have h2 : cv sig = encodeApprovedSignature S128 s :=
    (decodeSignature_eq_ok_iff vp (sha2WireCodec vp.params) (cv sig) s).mp h
  rw [← sp_encodeSignature, ← h2, sp_cv]

theorem decodeSig_error (sig : Spec.Bytes) (hs : sig.length ≠ 7856) :
    ∃ e, decodeSig (cv sig) = .error e :=
  ⟨_, WireCodec.decode_eq_error_of_length_ne (signatureCodec vp (sha2WireCodec vp.params))
    (cv sig) (by rw [cv_length]; exact hs)⟩

theorem decodePk_ok (pk : Spec.Bytes) (hp : pk.length = 32) :
    ∃ k, decodePk (cv pk) = .ok k ∧ pk = pkBytes k := by
  obtain ⟨k, h⟩ := decode_ok_of_length (publicKeyCodec (sha2WireCodec vp.params)) (cv pk)
    ((cv_length pk).trans hp)
  refine ⟨k, h, ?_⟩
  have h2 : cv pk = encodeApprovedPublicKey S128 k :=
    (decodePublicKey_eq_ok_iff (sha2WireCodec vp.params) (cv pk) k).mp h
  rw [← sp_encodePublicKey, ← h2, sp_cv]

/-- **Main theorem (internal verification, FIPS 205 Algorithm 20).**  For every message, every
byte string offered as a signature and every 32-byte public key, our specification's
`Spec.slhVerifyInternal` returns exactly what VCVio's executable
`GeneralScheme.verifyInternal` at SLH-DSA-SHA2-128s (`vp = S128.validatedParams`,
`prims = approvedPrimitives S128`, `decodeSig = decodeApprovedSignature S128`,
`decodePk = decodeApprovedPublicKey S128`, all by `rfl`) returns on the values VCVio's own strict
decoders produce; a signature of the wrong length (the only way the signature decoder can
fail) is rejected by both sides. -/
theorem verify_eq (msg sig pk : Spec.Bytes) (hp : pk.length = 32) :
    Spec.slhVerifyInternal msg sig pk =
      match decodeSig (cv sig), decodePk (cv pk) with
      | .ok s, .ok k =>
        GeneralScheme.verifyInternal vp prims (cv msg) s k
      | _, _ => false := by
  obtain ⟨k, hk, rfl⟩ := decodePk_ok pk hp
  by_cases hs : sig.length = 7856
  · obtain ⟨s, hsd, rfl⟩ := decodeSig_ok sig hs
    rw [hsd, hk]
    exact verify_eq_typed msg s k
  · obtain ⟨e, he⟩ := decodeSig_error sig hs
    have h1 : decodeSig (cv sig) = .error e := he
    rw [h1]
    unfold Spec.slhVerifyInternal
    exact ite_eq_left (by simpa [Spec.sigBytes, Spec.k, Spec.a, Spec.h, Spec.d, Spec.len, Spec.n] using hs)

/-- The same statement with both lengths assumed: the decoders succeed and the verdicts agree. -/
theorem verify_eq' (msg sig pk : Spec.Bytes) (hs : sig.length = 7856) (hp : pk.length = 32) :
    ∃ s k, decodeSig (cv sig) = .ok s ∧
      decodePk (cv pk) = .ok k ∧
      Spec.slhVerifyInternal msg sig pk =
        GeneralScheme.verifyInternal vp prims (cv msg) s k := by
  obtain ⟨k, hk, rfl⟩ := decodePk_ok pk hp
  obtain ⟨s, hsd, rfl⟩ := decodeSig_ok sig hs
  exact ⟨s, k, hsd, hk, verify_eq_typed msg s k⟩

/-- **External verification (FIPS 205 Algorithm 24, pure mode).**  `Spec.slhVerify` equals VCVio's
`External.verifyPure` on the decoded values, for every context (an over-long context is rejected
by both). -/
theorem slhVerify_eq (msg sig ctx pk : Spec.Bytes) (hp : pk.length = 32) :
    Spec.slhVerify msg sig ctx pk =
      match decodeSig (cv sig), decodePk (cv pk) with
      | .ok s, .ok k =>
        External.verifyPure vp prims (cv msg) s (cv ctx) k
      | _, _ => false := by
  unfold Spec.slhVerify
  by_cases hc : ctx.length > 255
  · rw [ite_eq_left hc]
    have hreq : External.encodePureMessage (cv ctx) (cv msg) =
        .error (.contextTooLong (cv ctx).length) := by
      unfold External.encodePureMessage External.encodeMessage
      rw [External.requireContext_eq_error _ (by rw [cv_length]; exact hc)]; rfl
    split <;> simp [External.verifyPure, hreq]
  · rw [ite_eq_right hc, verify_eq _ _ _ hp]
    have hreq := External.encodePureMessage_eq_ok (cv ctx) (cv msg)
      (by rw [cv_length]; omega)
    have hm : cv (Spec.withContext msg ctx) = [0, UInt8.ofNat (cv ctx).length] ++ cv ctx ++ cv msg := by
      have h255 : ctx.length < 256 := by omega
      simp [Spec.withContext, Spec.toByte, cv, List.range_succ]
      rfl
    split <;> simp [External.verifyPure, hreq, hm]

end Link

#print axioms Link.verify_eq_typed
#print axioms Link.verify_eq
#print axioms Link.verify_eq'
#print axioms Link.slhVerify_eq
