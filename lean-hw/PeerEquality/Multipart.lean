import PeerEquality.CallerFacade
import Facade.MultipartApi

open Aeneas Aeneas.Std Result
namespace slhdsa.PeerCall
open Spec slh_dsa

def byteParts (parts : Slice (Slice U8)) : List Bytes :=
  parts.val.map (fun s => bytes s.val)

private theorem joined_bytes (parts : Slice (Slice U8)) (m : Slice U8)
    (same : parts.val.flatMap (·.val) = m.val) : (byteParts parts).flatten = bytes m.val := by
  rw [← same]
  simp [byteParts,bytes,List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def]

variable {P : Type} {sk vk sig : Usize} {C : @Core P sk vk sig} {p : Params} {slack : Nat}

/-- Compare actual multipart callers for arbitrary partitions, context and matched randomizer. -/
theorem multipart_sign_peer (facades : Facades C p slack) (c : Children) (laws : ChildLaws c p)
    (positive : 0 < p.d) (k : Key) (shape : k.Shape p)
    (ours : signing_key.SigningKey P (Array U8 sk) (Array U8 vk) (Array U8 sig))
    (sameKey : bytes ours.bytes.val = k.bytes) (parts : Slice (Slice U8)) (m ctx : Slice U8)
    (same : parts.val.flatMap (·.val) = m.val) (rnd : Option (Slice U8))
    (valid : ∀ r ∈ rnd, r.length=p.n) (space : Room m.length slack) :
    signing_key.SigningKey.raw_try_sign_with_context C ours parts ctx rnd ⦃ ret =>
      signatureBytes ret = (signCtx c p k (byteParts parts) (bytes ctx.val)
        (rnd.map fun x => bytes x.val)).map Signature.bytes ⦄ := by
  have eq : signing_key.SigningKey.raw_try_sign_with_context C ours parts ctx rnd =
      signing_key.SigningKey.try_sign_with_context C ours m ctx rnd := by
    simp only [signing_key.SigningKey.try_sign_with_context, signing_key.SigningKey.raw_try_sign_with_context,
      lift,bind_ok,multipart.join_single parts m same]
  rw [eq]
  apply WP.spec_mono (facades.sign c laws k shape ours sameKey m ctx rnd valid space)
  intro ret result
  simpa only [sign_context c p laws positive k shape,joined_bytes parts m same,
    List.flatten_cons,List.flatten_nil,List.append_nil] using result

theorem multipart_verify_peer (facades : Facades C p slack) (c : Children) (laws : ChildLaws c p)
    (positive : 0 < p.d) (k : PublicKey) (shape : k.Shape p)
    (ours : verifying_key.VerifyingKey P (Array U8 sk) (Array U8 vk) (Array U8 sig))
    (sameKey : bytes ours.bytes.val = k.bytes) (parts : Slice (Slice U8)) (m ctx : Slice U8)
    (same : parts.val.flatMap (·.val) = m.val) (s : Signature) (signatureShape : s.Shape p)
    (parsed : signature_encoding.Signature P (Array U8 sk) (Array U8 vk) (Array U8 sig))
    (sameSig : bytes parsed.bytes.val = s.bytes) (space : Room m.length slack) :
    verifying_key.VerifyingKey.raw_try_verify_with_context C ours parts ctx parsed ⦃ ret =>
      ret = if verifyCtx c p k (byteParts parts) (bytes ctx.val) s then .Ok () else .Err () ⦄ := by
  have eq : verifying_key.VerifyingKey.raw_try_verify_with_context C ours parts ctx parsed =
      verifying_key.VerifyingKey.try_verify_with_context C ours m ctx parsed := by
    simp only [verifying_key.VerifyingKey.try_verify_with_context,
      verifying_key.VerifyingKey.raw_try_verify_with_context,lift,bind_ok,multipart.join_single parts m same]
  rw [eq]
  apply WP.spec_mono (facades.verify c laws k shape ours sameKey m ctx s signatureShape parsed sameSig space)
  intro ret result
  simpa only [verify_context c p laws positive k shape _ _ s signatureShape,joined_bytes parts m same,
    List.flatten_cons,List.flatten_nil,List.append_nil] using result

end slhdsa.PeerCall
