import Facade.Funs
open Aeneas Aeneas.Std Result
open slh_dsa
namespace slh_dsa.Kat

/-- [slh_dsa::signing_key::{slh_dsa::signing_key::SigningKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::slh_keygen_internal]:
    Source: 'src/signing_key.rs', lines 153:4-161:5
    Visibility: public -/
def signing_key.SigningKey.slh_keygen_internal
  {P : Type _} {Clause0_Clause0_Sk : Type _} {Clause0_Clause1_Vk : Type _}
  {Clause0_Clause2_Sig : Type _} (paramsCoreInst : params.Core P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig)
  (sk_seed : Slice Std.U8) (sk_prf : Slice Std.U8) (pk_seed : Slice Std.U8) :
  Result (signing_key.SigningKey P Clause0_Clause0_Sk Clause0_Clause1_Vk
    Clause0_Clause2_Sig)
  := do
  let t ← paramsCoreInst.SigningKeyStorageInst.BufferInst.zeroed
  let pk ← paramsCoreInst.VerifyingKeyStorageInst.BufferInst.zeroed
  let (s, as_mut_slice_back) ←
    paramsCoreInst.SigningKeyStorageInst.BufferInst.as_mut_slice t
  let (s1, as_mut_slice_back1) ←
    paramsCoreInst.VerifyingKeyStorageInst.BufferInst.as_mut_slice pk
  let (s2, s3) ← paramsCoreInst.keygen_seeds sk_seed sk_prf pk_seed s s1
  let bytes := as_mut_slice_back s2
  let pk1 := as_mut_slice_back1 s3
  ok { bytes, verifying_key := { bytes := pk1 } }

/-- [slh_dsa::signing_key::{slh_dsa::signing_key::SigningKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::slh_sign_internal]:
    Source: 'src/signing_key.rs', lines 168:4-173:5
    Visibility: public -/
def signing_key.SigningKey.slh_sign_internal
  {P : Type _} {Clause0_Clause0_Sk : Type _} {Clause0_Clause1_Vk : Type _}
  {Clause0_Clause2_Sig : Type _} (paramsCoreInst : params.Core P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig)
  (self : signing_key.SigningKey P Clause0_Clause0_Sk Clause0_Clause1_Vk
  Clause0_Clause2_Sig) (msg : Slice (Slice Std.U8))
  (opt_rand : Option (Slice Std.U8)) :
  Result (signature_encoding.Signature P Clause0_Clause0_Sk Clause0_Clause1_Vk
    Clause0_Clause2_Sig)
  := do
  let m ← multipart.join msg
  let sig ← paramsCoreInst.SignatureStorageInst.BufferInst.zeroed
  let s := alloc.vec.Vec.deref m
  let s1 ←
    paramsCoreInst.SigningKeyStorageInst.BufferInst.as_slice self.bytes
  let (s2, as_mut_slice_back) ←
    paramsCoreInst.SignatureStorageInst.BufferInst.as_mut_slice sig
  let s3 ← paramsCoreInst.sign_internal s s1 opt_rand s2
  let sig1 := as_mut_slice_back s3
  ok { bytes := sig1 }

/-- [slh_dsa::verifying_key::{slh_dsa::verifying_key::VerifyingKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::slh_verify_internal]:
    Source: 'src/verifying_key.rs', lines 51:4-60:5
    Visibility: public -/
def verifying_key.VerifyingKey.slh_verify_internal
  {P : Type _} {Clause0_Clause0_Sk : Type _} {Clause0_Clause1_Vk : Type _}
  {Clause0_Clause2_Sig : Type _} (paramsCoreInst : params.Core P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig)
  (self : verifying_key.VerifyingKey P Clause0_Clause0_Sk Clause0_Clause1_Vk
  Clause0_Clause2_Sig) (msg : Slice (Slice Std.U8))
  (sig : signature_encoding.Signature P Clause0_Clause0_Sk Clause0_Clause1_Vk
  Clause0_Clause2_Sig) :
  Result (core.result.Result Unit signature.error.Error)
  := do
  let m ← multipart.join msg
  let s := alloc.vec.Vec.deref m
  let s1 ← paramsCoreInst.SignatureStorageInst.BufferInst.as_slice sig.bytes
  let s2 ←
    paramsCoreInst.VerifyingKeyStorageInst.BufferInst.as_slice self.bytes
  let b ← paramsCoreInst.verify_internal s s1 s2
  let o ← core.bool.Bool.then_some b ()
  let e ← signature.error.Error.new
  core.option.Option.ok_or o e

end slh_dsa.Kat
