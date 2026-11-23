import Facade.Randomized
import Facade.Verify
open Aeneas Aeneas.Std Result
namespace slh_dsa

theorem multipart.join_single (parts : Slice (Slice U8)) (m : Slice U8)
    (h : parts.val.flatMap (·.val) = m.val) :
    multipart.join parts = multipart.join (Array.make 1#usize [m]).to_slice := by
  obtain ⟨a, ha, ea⟩ := _root_.slhdsa.spec_imp_exists
    (multipart.join_spec parts (by rw [h]; exact m.property))
  obtain ⟨b, hb, eb⟩ := _root_.slhdsa.spec_imp_exists
    (multipart.join_spec (Array.make 1#usize [m]).to_slice (by simp [Array.make]))
  rw [ha, hb]
  have eqv : a.val = b.val := by simpa [Array.make, ea, h] using eb.symm
  exact congrArg Result.ok (alloc.vec.Vec.ext a b eqv)

/-- All part boundaries, including empty slices, give the same signature as the
single-message trait implementation on their concatenation. -/
theorem multipart_sign_eq {P Sk Vk Sig : Type} (C : params.Core P Sk Vk Sig)
    (sk : signing_key.SigningKey P Sk Vk Sig) (parts : Slice (Slice U8)) (m : Slice U8)
    (h : parts.val.flatMap (·.val) = m.val) :
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign C sk parts =
    signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign C sk m := by
  simp only [signing_key.SigningKey.Insts.SignatureSignerSignerSignature.try_sign,
    signing_key.SigningKey.Insts.SignatureSignerMultipartSignerSignature.try_multipart_sign,
    lift, bind_ok, signing_key.SigningKey.raw_try_sign_with_context, multipart.join_single parts m h]

theorem multipart_verify_eq {P Sk Vk Sig : Type} (C : params.Core P Sk Vk Sig)
    (vk : verifying_key.VerifyingKey P Sk Vk Sig) (parts : Slice (Slice U8)) (m : Slice U8)
    (sig : signature_encoding.Signature P Sk Vk Sig) (h : parts.val.flatMap (·.val) = m.val) :
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify C vk parts sig =
    verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify C vk m sig := by
  simp only [verifying_key.VerifyingKey.Insts.SignatureVerifierVerifierSignature.verify,
    verifying_key.VerifyingKey.Insts.SignatureVerifierMultipartVerifierSignature.multipart_verify,
    lift, bind_ok, verifying_key.VerifyingKey.raw_try_verify_with_context, multipart.join_single parts m h]

/-- Equality includes errors and the RNG state returned by the translated method. -/
theorem multipart_randomized_eq {P Sk Vk Sig R E : Type} (C : params.Core P Sk Vk Sig)
    (rng : rand_core.TryCryptoRng R E) (sk : signing_key.SigningKey P Sk Vk Sig)
    (r : R) (parts : Slice (Slice U8)) (m : Slice U8) (h : parts.val.flatMap (·.val) = m.val) :
    signing_key.SigningKey.Insts.SignatureSignerRandomizedMultipartSignerSignature.try_multipart_sign_with_rng C rng sk r parts =
    signing_key.SigningKey.Insts.SignatureSignerRandomizedSignerSignature.try_sign_with_rng C rng sk r m := by
  simp only [signing_key.SigningKey.Insts.SignatureSignerRandomizedSignerSignature.try_sign_with_rng,
    signing_key.SigningKey.Insts.SignatureSignerRandomizedMultipartSignerSignature.try_multipart_sign_with_rng,
    signing_key.SigningKey.raw_try_sign_with_rng, signing_key.SigningKey.sign_with_rng_buffer,
    signing_key.SigningKey.raw_try_sign_with_context, lift, bind_ok, multipart.join_single parts m h]

#print axioms multipart_sign_eq
#print axioms multipart_verify_eq
#print axioms multipart_randomized_eq
end slh_dsa
