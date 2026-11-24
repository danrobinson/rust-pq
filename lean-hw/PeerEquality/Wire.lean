import PeerEquality.Library
import Facade.Parse

open Aeneas Aeneas.Std Result
namespace slhdsa.PeerCall
open Spec slh_dsa

def wireKey (p : Params) (b : Bytes) : Key :=
  let prf := b.drop p.n
  let pub := prf.drop p.n
  ⟨b.take p.n,prf.take p.n,pub.take p.n,pub.drop p.n⟩

def wirePublic (p : Params) (b : Bytes) : PublicKey := ⟨b.take p.n,b.drop p.n⟩

def wireSignature (p : Params) (b : Bytes) : Signature :=
  let tail := b.drop p.n
  ⟨b.take p.n,tail.take p.forsSigBytes,tail.drop p.forsSigBytes⟩

theorem wireKey_bytes (p : Params) (b : Bytes) : (wireKey p b).bytes = b := by
  simp [wireKey,Key.bytes,List.append_assoc]
theorem wirePublic_bytes (p : Params) (b : Bytes) : (wirePublic p b).bytes = b := by
  simp [wirePublic,PublicKey.bytes]
theorem wireSignature_bytes (p : Params) (b : Bytes) : (wireSignature p b).bytes = b := by
  simp [wireSignature,Signature.bytes,List.append_assoc]

theorem wireKey_shape (p : Params) (b : Bytes) (h : b.length=4*p.n) : (wireKey p b).Shape p := by
  constructor <;> simp [wireKey] <;> omega
theorem wirePublic_shape (p : Params) (b : Bytes) (h : b.length=2*p.n) : (wirePublic p b).Shape p := by
  constructor <;> simp [wirePublic] <;> omega
theorem wireSignature_shape (p : Params) (b : Bytes) (h : b.length=p.sigBytes)
    (fits : p.n+p.forsSigBytes ≤ p.sigBytes) : (wireSignature p b).Shape p := by
  constructor
  · simp [wireSignature]; omega
  · simp [wireSignature]; omega
  · simpa only [wireSignature_bytes] using h

section
variable {P : Type} {sk vk sig : Usize} (C : @Core P sk vk sig) (p : Params) (slack : Nat)

/-- All raw key/signature parsers and the public signing and verification
operations, on the complete set of fixed-size byte arrays. -/
structure WireFacade (c : Children) : Prop where
  parse : ParsersCorrect C p
  sign : ∀ (k : signing_key.SigningKey P (Array U8 sk) (Array U8 vk) (Array U8 sig))
    (m ctx : Slice U8) (rnd : Option (Slice U8)), (∀ r ∈ rnd, r.length=p.n) → Room m.length slack →
    signing_key.SigningKey.try_sign_with_context C k m ctx rnd ⦃ ret =>
      signatureBytes ret = (signCtx c p (wireKey p (bytes k.bytes.val)) [bytes m.val] (bytes ctx.val)
        (rnd.map fun x => bytes x.val)).map Signature.bytes ⦄
  verify : ∀ (k : verifying_key.VerifyingKey P (Array U8 sk) (Array U8 vk) (Array U8 sig))
    (m ctx : Slice U8) (s : signature_encoding.Signature P (Array U8 sk) (Array U8 vk) (Array U8 sig)),
    Room m.length slack → verifying_key.VerifyingKey.try_verify_with_context C k m ctx s ⦃ ret =>
      ret = if verifyCtx c p (wirePublic p (bytes k.bytes.val)) [bytes m.val] (bytes ctx.val)
        (wireSignature p (bytes s.bytes.val)) then .Ok () else .Err () ⦄

theorem wireFacade {c : Children} (api : SameFacade C p slack c) (parse : ParsersCorrect C p)
    (ks : sk.val=4*p.n) (vs : vk.val=2*p.n) (ss : sig.val=p.sigBytes)
    (fits : p.n+p.forsSigBytes ≤ p.sigBytes) : WireFacade C p slack c := by
  refine ⟨parse,?_,?_⟩
  · intro k m ctx rnd hr room
    exact api.sign _ (wireKey_shape _ _ (by rw [bytes_length,Array.length_eq,ks])) k
      (wireKey_bytes _ _).symm m ctx rnd hr room
  · intro k m ctx s room
    exact api.verify _ (wirePublic_shape _ _ (by rw [bytes_length,Array.length_eq,vs])) k
      (wirePublic_bytes _ _).symm m ctx _ (wireSignature_shape _ _ (by rw [bytes_length,Array.length_eq,ss]) fits)
      s (wireSignature_bytes _ _).symm room
end

theorem sha2_128s_wire (route : RcSlhSha2.Routing) : WireFacade params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.sha2_128s 409
    (Providers.sha2 .s128 RcSlhSha2.nativeAlgorithms) :=
  wireFacade _ _ _ (sha2_128s_peer route).2 sha2_128s_parsers (by decide) (by decide) (by decide) (by decide)

theorem sha2_128f_wire (route : RcSlhSha2.Routing) : WireFacade params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.sha2_128f 409
    (Providers.sha2 .f128 RcSlhSha2.nativeAlgorithms) :=
  wireFacade _ _ _ (sha2_128f_peer route).2 sha2_128f_parsers (by decide) (by decide) (by decide) (by decide)

theorem sha2_192s_wire (route : RcSlhSha2.Routing) : WireFacade params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.sha2_192s 561
    (Providers.sha2 .s192 RcSlhSha2.nativeAlgorithms) :=
  wireFacade _ _ _ (sha2_192s_peer route).2 sha2_192s_parsers (by decide) (by decide) (by decide) (by decide)

theorem sha2_192f_wire (route : RcSlhSha2.Routing) : WireFacade params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.sha2_192f 561
    (Providers.sha2 .f192 RcSlhSha2.nativeAlgorithms) :=
  wireFacade _ _ _ (sha2_192f_peer route).2 sha2_192f_parsers (by decide) (by decide) (by decide) (by decide)

theorem sha2_256s_wire (route : RcSlhSha2.Routing) : WireFacade params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.sha2_256s 561
    (Providers.sha2 .s256 RcSlhSha2.nativeAlgorithms) :=
  wireFacade _ _ _ (sha2_256s_peer route).2 sha2_256s_parsers (by decide) (by decide) (by decide) (by decide)

theorem sha2_256f_wire (route : RcSlhSha2.Routing) : WireFacade params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.sha2_256f 561
    (Providers.sha2 .f256 RcSlhSha2.nativeAlgorithms) :=
  wireFacade _ _ _ (sha2_256f_peer route).2 sha2_256f_parsers (by decide) (by decide) (by decide) (by decide)

theorem shake_128s_wire : WireFacade params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856 Spec.shake_128s 409
    (Providers.shake Spec.shake_128s) :=
  wireFacade _ _ _ shake_128s_peer shake_128s_parsers (by decide) (by decide) (by decide) (by decide)

theorem shake_128f_wire : WireFacade params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088 Spec.shake_128f 409
    (Providers.shake Spec.shake_128f) :=
  wireFacade _ _ _ shake_128f_peer shake_128f_parsers (by decide) (by decide) (by decide) (by decide)

theorem shake_192s_wire : WireFacade params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224 Spec.shake_192s 561
    (Providers.shake Spec.shake_192s) :=
  wireFacade _ _ _ shake_192s_peer shake_192s_parsers (by decide) (by decide) (by decide) (by decide)

theorem shake_192f_wire : WireFacade params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664 Spec.shake_192f 561
    (Providers.shake Spec.shake_192f) :=
  wireFacade _ _ _ shake_192f_peer shake_192f_parsers (by decide) (by decide) (by decide) (by decide)

theorem shake_256s_wire : WireFacade params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792 Spec.shake_256s 561
    (Providers.shake Spec.shake_256s) :=
  wireFacade _ _ _ shake_256s_peer shake_256s_parsers (by decide) (by decide) (by decide) (by decide)

theorem shake_256f_wire : WireFacade params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856 Spec.shake_256f 561
    (Providers.shake Spec.shake_256f) :=
  wireFacade _ _ _ shake_256f_peer shake_256f_parsers (by decide) (by decide) (by decide) (by decide)

end slhdsa.PeerCall
