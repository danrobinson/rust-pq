import Platformadapter.Writers
open Aeneas Aeneas.Std Result
open slh_dsa
namespace slh_dsa.PlatformExports

/-- Forward a DER document or its converted error, preserving the external
constructor's effect on the supplied bytes. -/
def documentResult {D E Err} (construct : Slice U8 → Result (core.result.Result D E))
    (report : E → Result Err) (data : Slice U8) : Result (core.result.Result D Err) := do
  let r ← construct data
  match r with
  | .Ok value => ok (.Ok value)
  | .Err error => do
    let converted ← report error
    ok (.Err converted)

def ExportsCorrect [doc : Documents] {P Sk Vk Sig HK HV}
    (C : params.Core P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig))
    (sh : Std.Array U8 HK) (ph : Std.Array U8 HV) (slen plen : Usize)
    (hs : slen.val=HK.val+Sk.val) (hp : plen.val=HV.val+Vk.val) : Prop :=
  (∀ key : signing_key.SigningKey P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig),
    signing_key.SigningKey.Insts.Pkcs8TraitsEncodePrivateKey.to_pkcs8_der C key =
    documentResult doc.secret doc.pkcsError
      (Slice.from (sh.val++key.bytes.val) (by simp; rw [←hs]; scalar_tac))) ∧
  (∀ key : verifying_key.VerifyingKey P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig),
    verifying_key.VerifyingKey.Insts.SpkiTraitsEncodePublicKey.to_public_key_der C key =
    documentResult doc.publicDoc doc.spkiError
      (Slice.from (ph.val++key.bytes.val) (by simp; rw [←hp]; scalar_tac)))

theorem exports_correct [doc : Documents] {P Sk Vk Sig HK HV}
    (C : params.Core P (Std.Array U8 Sk) (Std.Array U8 Vk) (Std.Array U8 Sig))
    (sh : Std.Array U8 HK) (ph : Std.Array U8 HV) (slen plen : Usize)
    (hs : slen.val=HK.val+Sk.val) (hp : plen.val=HV.val+Vk.val)
    (writers : WritersCorrect C sh ph slen plen hs hp)
    (skSlice : C.SigningKeyStorageInst.BufferInst.as_slice = fun a => ok a.to_slice)
    (pkSlice : C.VerifyingKeyStorageInst.BufferInst.as_slice = fun a => ok a.to_slice) :
    ExportsCorrect C sh ph slen plen hs hp := by
  constructor
  · intro key
    unfold signing_key.SigningKey.Insts.Pkcs8TraitsEncodePrivateKey.to_pkcs8_der
    rw [skSlice]
    simp only [bind_ok]
    rw [writers.1 _ _ _ _ _ (by simp [Slice.length])]
    unfold documentResult
    simp only [signing_key.EncodePrivateKeySigningKey.to_pkcs8_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultSecretDocumentError,
      signing_key.EncodePrivateKeySigningKey.to_pkcs8_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultSecretDocumentError.call_once,
      Array.val_to_slice,der.document.SecretDocument.Insts.CoreConvertTryFromShared0SliceU8Error.try_from]
    congr 1
    funext r
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      pkcs8.error.Error.Insts.CoreConvertFromError,pkcs8.error.Error.Insts.CoreConvertFromError.from, bind_tc_eq,bind_ok] <;> rfl
  · intro key
    unfold verifying_key.VerifyingKey.Insts.SpkiTraitsEncodePublicKey.to_public_key_der
    rw [pkSlice]
    simp only [bind_ok]
    rw [writers.2 _ _ _ _ _ (by simp [Slice.length])]
    unfold documentResult
    simp only [verifying_key.EncodePublicKeyVerifyingKey.to_public_key_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultDocumentError,
      verifying_key.EncodePublicKeyVerifyingKey.to_public_key_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultDocumentError.call_once,
      Array.val_to_slice,der.document.Document.Insts.CoreConvertTryFromShared0SliceU8Error.try_from]
    congr 1
    funext r
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      spki.error.Error.Insts.CoreConvertFromError,spki.error.Error.Insts.CoreConvertFromError.from, bind_tc_eq,bind_ok] <;> rfl

local macro "set_exports " lemmaId:ident writer:ident coreId:ident secret:ident pub:ident plen:term:max vlen:term:max : command =>
  `(theorem $lemmaId [Documents] : ExportsCorrect $coreId $secret $pub $plen $vlen (by decide) (by decide) :=
      exports_correct _ _ _ _ _ _ _ $writer rfl rfl)

set_exports sha2_128s_exports sha2_128s_writers params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856
  _root_.slhdsa.sets.sha2_128s.PKCS8_PREFIX _root_.slhdsa.sets.sha2_128s.SPKI_PREFIX 84#usize 50#usize
set_exports sha2_128f_exports sha2_128f_writers params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088
  _root_.slhdsa.sets.sha2_128f.PKCS8_PREFIX _root_.slhdsa.sets.sha2_128f.SPKI_PREFIX 84#usize 50#usize
set_exports sha2_192s_exports sha2_192s_writers params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224
  _root_.slhdsa.sets.sha2_192s.PKCS8_PREFIX _root_.slhdsa.sets.sha2_192s.SPKI_PREFIX 116#usize 66#usize
set_exports sha2_192f_exports sha2_192f_writers params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664
  _root_.slhdsa.sets.sha2_192f.PKCS8_PREFIX _root_.slhdsa.sets.sha2_192f.SPKI_PREFIX 116#usize 66#usize
set_exports sha2_256s_exports sha2_256s_writers params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792
  _root_.slhdsa.sets.sha2_256s.PKCS8_PREFIX _root_.slhdsa.sets.sha2_256s.SPKI_PREFIX 150#usize 82#usize
set_exports sha2_256f_exports sha2_256f_writers params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856
  _root_.slhdsa.sets.sha2_256f.PKCS8_PREFIX _root_.slhdsa.sets.sha2_256f.SPKI_PREFIX 150#usize 82#usize
set_exports shake_128s_exports shake_128s_writers params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856
  _root_.slhdsa.sets.shake_128s.PKCS8_PREFIX _root_.slhdsa.sets.shake_128s.SPKI_PREFIX 84#usize 50#usize
set_exports shake_128f_exports shake_128f_writers params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088
  _root_.slhdsa.sets.shake_128f.PKCS8_PREFIX _root_.slhdsa.sets.shake_128f.SPKI_PREFIX 84#usize 50#usize
set_exports shake_192s_exports shake_192s_writers params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224
  _root_.slhdsa.sets.shake_192s.PKCS8_PREFIX _root_.slhdsa.sets.shake_192s.SPKI_PREFIX 116#usize 66#usize
set_exports shake_192f_exports shake_192f_writers params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664
  _root_.slhdsa.sets.shake_192f.PKCS8_PREFIX _root_.slhdsa.sets.shake_192f.SPKI_PREFIX 116#usize 66#usize
set_exports shake_256s_exports shake_256s_writers params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792
  _root_.slhdsa.sets.shake_256s.PKCS8_PREFIX _root_.slhdsa.sets.shake_256s.SPKI_PREFIX 150#usize 82#usize
set_exports shake_256f_exports shake_256f_writers params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856
  _root_.slhdsa.sets.shake_256f.PKCS8_PREFIX _root_.slhdsa.sets.shake_256f.SPKI_PREFIX 150#usize 82#usize

end slh_dsa.PlatformExports
