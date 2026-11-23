import PeerEquality.CallGraph
import Spec.Correctness

namespace slhdsa.PeerCall
open Spec

structure Key.Shape (k : Key) (p : Params) : Prop where
  seed : k.seed.length = p.n
  prf : k.prf.length = p.n
  publicSeed : k.publicSeed.length = p.n
  root : k.root.length = p.n

structure PublicKey.Shape (k : PublicKey) (p : Params) : Prop where
  seed : k.seed.length = p.n
  root : k.root.length = p.n

structure Signature.Shape (s : Signature) (p : Params) : Prop where
  r : s.r.length = p.n
  fors : s.fors.length = p.forsSigBytes
  size : s.bytes.length = p.sigBytes

/-- The remaining interfaces are named separately so a caller theorem does
not assume equality of peer and FIPS signing or verification. -/
structure ChildLaws (c : Children) (p : Params) : Prop where
  node : c.xmss.node = xmssNode p
  sign : c.xmss.sign = xmssSign p
  recover : c.xmss.recover = xmssPkFromSig p
  prfMsg : ∀ key rand msg, key.length = p.n → c.prfMsg key rand msg = PRFmsg p key rand msg.flatten.flatten
  hMsg : c.hMsg = (specChildren p).hMsg
  split : c.split = (specChildren p).split
  forsSign : c.forsSign = Spec.forsSign p
  forsRecover : c.forsRecover = forsPkFromSig p
  htVerify : c.htVerify = Spec.htVerify p

private theorem xmss_is_spec {c : Children} {p : Params} (laws : ChildLaws c p) :
    c.xmss = xmssSpec p := by
  obtain ⟨⟨sign,recover,node⟩,other⟩ := c
  cases laws with
  | mk hn hs hr _ _ _ _ _ _ => simp only at hn hs hr; subst_vars; rfl

/-- For D > 0 and H' < 32 the checked narrowing and bit mask agree with
the FIPS natural-number leaf operation for every 64-bit tree index. -/
theorem leaf_bits (tree height : Nat) (small : height < 32) :
    tree &&& (2^height-1) = tree % 2^height ∧ tree % 2^height < 2^32 := by
  exact ⟨Nat.and_two_pow_sub_one_eq_mod _ _, lt_trans (Nat.mod_lt tree (Nat.two_pow_pos height))
    (Nat.pow_lt_pow_right (by decide) small)⟩

theorem keygen_fips (c : Children) (p : Params) (node : c.xmss.node = xmssNode p) (sk prf pk : Bytes) :
    let k := keygen c p sk prf pk
    (k.bytes,k.public.bytes) = slhKeygenInternal p sk prf pk := by
  simp only [keygen,Key.bytes,Key.public,PublicKey.bytes,slhKeygenInternal,node,layer]; rfl

private theorem key_blocks (p : Params) (k : Key) (h : k.Shape p) :
    block p k.bytes 0 = k.seed ∧ block p k.bytes 1 = k.prf ∧
    block p k.bytes 2 = k.publicSeed ∧ block p k.bytes 3 = k.root := by
  have a : 2*p.n=p.n+p.n := by omega
  have b : 3*p.n=p.n+p.n+p.n := by omega
  have first : k.seed.drop (p.n+p.n+p.n) = [] := List.drop_eq_nil_of_le (by rw [h.seed]; omega)
  have second : k.prf.drop (p.n+p.n) = [] := List.drop_eq_nil_of_le (by rw [h.prf]; omega)
  simp [block,Key.bytes,first,second,List.append_assoc,List.drop_append,List.take_append,
    h.seed,h.prf,h.publicSeed,h.root,a,b,List.take_of_length_le h.seed.le,
    List.take_of_length_le h.prf.le,List.take_of_length_le h.publicSeed.le,
    List.take_of_length_le h.root.le]

theorem key_public_block (p : Params) (k : Key) (h : k.Shape p) : block p k.bytes 2 = k.publicSeed :=
  (key_blocks p k h).2.2.1

private theorem public_blocks (p : Params) (k : PublicKey) (h : k.Shape p) :
    block p k.bytes 0 = k.seed ∧ block p k.bytes 1 = k.root := by
  simp [block,PublicKey.bytes,List.take_append,List.drop_append,h.seed,
    List.take_of_length_le h.seed.le,List.take_of_length_le h.root.le]

theorem sign_fips (c : Children) (p : Params) (laws : ChildLaws c p) (positive : 0 < p.d)
    (k : Key) (shape : k.Shape p) (msg : Parts) (rand : Option Bytes) :
    (rawSign c p k msg rand).bytes =
      slhSignInternal p msg.flatten.flatten k.bytes (rand.getD k.publicSeed) := by
  obtain ⟨a,b,d,e⟩ := key_blocks p k shape
  simp only [rawSign,Signature.bytes,slhSignInternal,a,b,d,e,laws.prfMsg _ _ _ shape.prf,
    laws.hMsg,laws.split,laws.forsSign,laws.forsRecover,xmss_is_spec laws, specChildren,
    ht_fips _ positive]
  rfl

theorem verify_fips (c : Children) (p : Params) (laws : ChildLaws c p)
    (k : PublicKey) (shape : k.Shape p) (msg : Parts) (s : Signature) (sig : s.Shape p) :
    rawVerify c k msg s = slhVerifyInternal p msg.flatten.flatten s.bytes k.bytes := by
  obtain ⟨a,b⟩ := public_blocks p k shape
  unfold slhVerifyInternal
  rw [if_neg (by intro bad; exact bad sig.size),a,b]
  have r : s.bytes.take p.n = s.r := by
    simp [Signature.bytes,List.append_assoc,List.take_append,sig.r,List.take_of_length_le sig.r.le]
  have f : (s.bytes.drop p.n).take p.forsSigBytes = s.fors := by
    simp [Signature.bytes,List.append_assoc,List.drop_append,List.take_append,sig.r,sig.fors,
      List.take_of_length_le sig.fors.le]
  have t : s.bytes.drop (p.n+p.forsSigBytes) = s.tree := by
    simp [Signature.bytes,List.append_assoc,List.drop_append,sig.r,sig.fors]
  rw [r,f,t]
  simp only [rawVerify,laws.hMsg,laws.split,laws.forsRecover,laws.htVerify,specChildren]
  rfl

private theorem context_bytes (ctx : Bytes) (msg : List Bytes) :
    (contextParts ctx msg).flatten.flatten = withContext msg.flatten ctx := by
  simp [contextParts,withContext,toByte,List.range_succ,List.append_assoc]

theorem sign_context (c : Children) (p : Params) (laws : ChildLaws c p) (positive : 0 < p.d)
    (k : Key) (shape : k.Shape p) (msg : List Bytes) (ctx : Bytes) (rand : Option Bytes) :
    (signCtx c p k msg ctx rand).map Signature.bytes =
      slhSign p msg.flatten ctx k.bytes (rand.getD k.publicSeed) := by
  by_cases ok : ctx.length ≤ 255
  · simp [signCtx,slhSign,ok,Nat.not_lt.mpr ok,sign_fips c p laws positive k shape,context_bytes]
  · simp [signCtx,slhSign,ok,Nat.lt_of_not_ge ok]

theorem verify_context (c : Children) (p : Params) (laws : ChildLaws c p) (k : PublicKey)
    (shape : k.Shape p) (msg : List Bytes) (ctx : Bytes) (s : Signature) (sig : s.Shape p) :
    verifyCtx c k msg ctx s = slhVerify p msg.flatten s.bytes ctx k.bytes := by
  by_cases ok : ctx.length ≤ 255
  · simp [verifyCtx,slhVerify,ok,Nat.not_lt.mpr ok,verify_fips c p laws k shape _ s sig,context_bytes]
  · simp [verifyCtx,slhVerify,ok,Nat.lt_of_not_ge ok]

end slhdsa.PeerCall
