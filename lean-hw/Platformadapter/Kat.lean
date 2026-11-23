import Platformadapter.KatProgram
import Facade.Keygen
import Facade.Verify
open Aeneas Aeneas.Std Result
open slhdsa (Room msgSlack bytes paramsS PN)
open slh_dsa

namespace slh_dsa.Kat

def Algorithms {P Sk Vk Sig} (C : params.Core P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig)) (S : Spec.Params) : Prop :=
  (∀ (a b c : Slice U8), a.length=S.n → b.length=S.n → c.length=S.n →
    signing_key.SigningKey.slh_keygen_internal C a b c ⦃ out => keyBytes out = Spec.slhKeygenInternal S (bytes a.val) (bytes b.val) (bytes c.val) ⦄) ∧
  (∀ (key : slh_dsa.signing_key.SigningKey P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig))
    (parts : Slice (Slice U8)) (rnd : Option (Slice U8)), (∀ r ∈ rnd, r.length=S.n) →
    Room (parts.val.flatMap (·.val)).length (msgSlack S.n) →
    signing_key.SigningKey.slh_sign_internal C key parts rnd ⦃ out =>
      bytes out.bytes.val=Spec.slhSignInternal S (bytes (parts.val.flatMap (·.val))) (bytes key.bytes.val)
        ((rnd.map (fun r => bytes r.val)).getD (Spec.block S (bytes key.bytes.val) 2)) ⦄) ∧
  (∀ (key : slh_dsa.verifying_key.VerifyingKey P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig))
    (parts : Slice (Slice U8)) (sig : signature_encoding.Signature P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig)),
    Room (parts.val.flatMap (·.val)).length (msgSlack S.n) →
    verifying_key.VerifyingKey.slh_verify_internal C key parts sig ⦃ out =>
      out=if Spec.slhVerifyInternal S (bytes (parts.val.flatMap (·.val))) (bytes sig.bytes.val) (bytes key.bytes.val) then .Ok () else .Err () ⦄)

theorem kat_algorithms {P N Sk Vk Sig}
    (C : params.Core P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig))
    (p : _root_.slhdsa.params.Params) (hp : PN p N)
    (sklen : Sk.val=4*N.val) (vklen : Vk.val=2*N.val) (siglen : Sig.val=(paramsS p).sigBytes)
    (skBuf : C.SigningKeyStorageInst.BufferInst=ArrayU8N.Insts.Slh_dsaParamsBuffer Sk)
    (vkBuf : C.VerifyingKeyStorageInst.BufferInst=ArrayU8N.Insts.Slh_dsaParamsBuffer Vk)
    (sigBuf : C.SignatureStorageInst.BufferInst=ArrayU8N.Insts.Slh_dsaParamsBuffer Sig)
    (kg : C.keygen_seeds=_root_.slhdsa.adapter.keygen_seeds N p)
    (sg : ∀ m sk r dest, C.sign_internal m sk r dest=
      _root_.slhdsa.adapter.sign_internal_into N p m sk r.isSome (r.getD (Std.Array.empty U8).to_slice) dest)
    (vf : C.verify_internal=_root_.slhdsa.slh.slh_verify_internal N p) :
    Algorithms C (paramsS p) := by
  refine ⟨?_,?_,?_⟩
  · intro a b c ha hb hc
    exact slh_dsa.seeded_spec .sha2 C p hp sklen vklen skBuf vkBuf kg a b c (hp.n ▸ ha) (hp.n ▸ hb) (hp.n ▸ hc)
  · intro sk parts rnd valid room
    unfold signing_key.SigningKey.slh_sign_internal
    rw [skBuf,sigBuf]
    have fits := room.1
    obtain ⟨m,join,mval⟩ := _root_.slhdsa.spec_imp_exists (multipart.join_spec parts (by omega))
    rw [join]
    simp only [ArrayU8N.Insts.Slh_dsaParamsBuffer.zeroed,ArrayU8N.Insts.Slh_dsaParamsBuffer.as_slice,
      ArrayU8N.Insts.Slh_dsaParamsBuffer.as_mut_slice,Array.to_slice_mut,bind_ok,uncurry,sg]
    let rndBytes := rnd.getD (Std.Array.empty U8).to_slice
    have validRnd : rnd.isSome = true → rndBytes.length=N.val := by
      cases rnd with
      | none => simp
      | some r => intro _; exact (valid r (by simp)).trans hp.n
    obtain ⟨out,eq,data⟩ := _root_.slhdsa.spec_imp_exists (_root_.slhdsa.adapter_sign_internal_into_spec p hp m.deref
      sk.bytes.to_slice rnd.isSome rndBytes (Array.repeat Sig 0#u8).to_slice
      (by simpa [Slice.length] using sklen) (by simpa [Slice.length] using siglen) validRnd
      (by simpa only [Slice.length,_root_.slhdsa.vec_deref_val,mval,hp.n] using room))
    rw [eq]
    simp only [_root_.slhdsa.vec_deref_val,Array.val_to_slice,mval] at data
    have sized := congrArg List.length data
    rw [_root_.slhdsa.bytes_length,Spec.slhSignInternal_length _ hp.valid,←siglen] at sized
    simp only [bind_ok,WP.spec_ok,Array.from_slice_val _ _ sized,data]
    cases rnd <;> simp [rndBytes,_root_.slhdsa.randS]
  · intro pk parts sig room
    unfold verifying_key.VerifyingKey.slh_verify_internal
    have fits := room.1
    obtain ⟨m,join,mval⟩ := _root_.slhdsa.spec_imp_exists (multipart.join_spec parts (by omega))
    rw [join,vkBuf,sigBuf]
    simp only [ArrayU8N.Insts.Slh_dsaParamsBuffer.as_slice,bind_ok,vf]
    obtain ⟨b,eq,correct⟩ := _root_.slhdsa.spec_imp_exists (_root_.slhdsa.slh_verify_internal_spec p hp m.deref
      sig.bytes.to_slice pk.bytes.to_slice (by simpa [Slice.length] using vklen)
      (by simpa only [Slice.length,_root_.slhdsa.vec_deref_val,mval,hp.n] using room))
    simp only [_root_.slhdsa.vec_deref_val,Array.val_to_slice,mval] at correct
    rw [eq,←correct]
    cases b <;> simp [core.bool.Bool.then_some, signature.error.Error.new,Std.core.option.Option.ok_or]
end slh_dsa.Kat
