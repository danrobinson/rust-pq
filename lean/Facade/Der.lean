import Facade.Parse

open Aeneas Aeneas.Std Result
open slhdsa (bytes)
namespace slh_dsa

abbrev PrivateInfo := pkcs8.private_key_info.PrivateKeyInfo der.asn1.any.AnyRef
  der.asn1.octet_string.OctetStringRef der.asn1.bit_string.BitStringRef
abbrev PublicInfo := spki.spki.SubjectPublicKeyInfo der.asn1.any.AnyRef der.asn1.bit_string.BitStringRef

private def resultBytes {K B E : Type} (readKey : K → B) : Std.core.result.Result K E → Except E B
  | .Ok k => .ok (readKey k)
  | .Err e => .error e

/-- The external parser supplies the decoded fields. A bit string with unused bits has no byte view. -/
def DerCorrect {P : Type} {Sk Vk Sig : Usize}
    (C : params.Core P (Array U8 Sk) (Array U8 Vk) (Array U8 Sig))
    (D : params.DerAlgorithm P) (p : Spec.Params) (oid : Slice U8) : Prop :=
  (∀ k : PrivateInfo,
    signing_key.SigningKey.Insts.CoreConvertTryFromPrivateKeyInfoAnyRefShared0OctetStringRefBitStringRefError.try_from C D k ⦃ r =>
      resultBytes keyBytes r =
        if k.algorithm.oid.val ≠ oid.val then .error (.PublicKey (.OidUnknown k.algorithm.oid))
        else if k.private_key.length = 4*p.n then .ok (bytes k.private_key.val, Spec.skPk p (bytes k.private_key.val))
        else .error (.KeyMalformed .Invalid) ⦄) ∧
  (∀ k : PublicInfo,
    verifying_key.VerifyingKey.Insts.CoreConvertTryFromSubjectPublicKeyInfoAnyRefBitStringRefError.try_from C D k ⦃ r =>
      resultBytes (fun key => bytes key.bytes.val) r =
        if k.algorithm.oid.val ≠ oid.val then .error (.OidUnknown k.algorithm.oid)
        else match k.subject_public_key with
          | none => .error (.Asn1 ())
          | some data => if data.length = 2*p.n then .ok (bytes data.val) else .error .KeyMalformed ⦄)

local macro "der_errors" : tactic => `(tactic| simp [signing_key.TryFromSigningKeyPrivateKeyInfoAnyRefShared0OctetStringRefBitStringRefError.try_from.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    signing_key.TryFromSigningKeyPrivateKeyInfoAnyRefShared0OctetStringRefBitStringRefError.try_from.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    verifying_key.TryFromVerifyingKeySubjectPublicKeyInfoAnyRefBitStringRefError.try_from.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    verifying_key.TryFromVerifyingKeySubjectPublicKeyInfoAnyRefBitStringRefError.try_from.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError,
    verifying_key.TryFromVerifyingKeySubjectPublicKeyInfoAnyRefBitStringRefError.try_from.closure.Insts.CoreOpsFunctionFnOnceTupleError.call_once,
    verifying_key.TryFromVerifyingKeySubjectPublicKeyInfoAnyRefBitStringRefError.try_from.closure.Insts.CoreOpsFunctionFnOnceTupleError,
    Std.core.result.Result.map_err, Std.core.convert.IntoFrom.into,
    pkcs8.error.Error.Insts.CoreConvertFromKeyError.from, pkcs8.error.Error.Insts.CoreConvertFromError.from,
    spki.error.Error.Insts.CoreConvertFromError.from, der.error.ErrorKind.to_error, der.tag.Tag.value_error,
    core.option.Option.ok_or_else, Std.core.result.Result.Insts.CoreOpsTry.branch,
    Std.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, resultBytes])

private theorem der_spec {P : Type} {Sk Vk Sig : Usize}
    (C : params.Core P (Array U8 Sk) (Array U8 Vk) (Array U8 Sig)) (D : params.DerAlgorithm P)
    (p : Spec.Params) (oid : Slice U8) (hoid : D.DER_OID = ok oid) (raw : ParsersCorrect C p) :
    DerCorrect C D p oid := by
  constructor
  · intro k
    unfold signing_key.SigningKey.Insts.CoreConvertTryFromPrivateKeyInfoAnyRefShared0OctetStringRefBitStringRefError.try_from
    simp only [const_oid.ObjectIdentifier.as_bytes, hoid, bind_ok, same]
    let* ⟨equal, he⟩ ← _root_.slhdsa.adapter_bytes_equal_spec
    by_cases matchOid : k.algorithm.oid.val = oid.val
    · simp only [he, matchOid, decide_true, ↓reduceIte, der.asn1.octet_string.OctetStringRef.as_bytes, bind_ok]
      obtain ⟨r, hr, hbytes⟩ := _root_.slhdsa.spec_imp_exists (raw k.private_key).1
      rw [hr]
      cases r <;> by_cases valid : k.private_key.length = 4*p.n <;>
        simp [valid, observed] at hbytes <;> simp [valid, resultBytes, hbytes] <;> der_errors
    · simp [he, matchOid, resultBytes]; der_errors
  · intro k
    unfold verifying_key.VerifyingKey.Insts.CoreConvertTryFromSubjectPublicKeyInfoAnyRefBitStringRefError.try_from
    simp only [const_oid.ObjectIdentifier.as_bytes, hoid, bind_ok, same]
    let* ⟨equal, he⟩ ← _root_.slhdsa.adapter_bytes_equal_spec
    by_cases matchOid : k.algorithm.oid.val = oid.val
    · simp only [he, matchOid, decide_true, ↓reduceIte, der.asn1.bit_string.BitStringRef.as_bytes, bind_ok]
      cases hkey : k.subject_public_key with
      | none => der_errors
      | some data =>
        simp only [core.option.Option.ok_or_else, bind_ok, Std.core.result.Result.Insts.CoreOpsTry.branch]
        obtain ⟨r, hr, hbytes⟩ := _root_.slhdsa.spec_imp_exists (raw data).2.1
        rw [hr]
        cases r <;> by_cases valid : data.length = 2*p.n <;>
          simp [valid, observed] at hbytes <;> simp [valid, resultBytes, hbytes] <;> der_errors
    · simp [he, matchOid, resultBytes]

theorem sha2_128s_der : DerCorrect
    params.Sha2_128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856
    params.Sha2_128s.Insts.Slh_dsaParamsDerAlgorithm Spec.sha2_128s (slhOid 20#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) sha2_128s_parsers
#print axioms sha2_128s_der

theorem sha2_128f_der : DerCorrect
    params.Sha2_128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088
    params.Sha2_128f.Insts.Slh_dsaParamsDerAlgorithm Spec.sha2_128f (slhOid 21#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) sha2_128f_parsers
#print axioms sha2_128f_der

theorem sha2_192s_der : DerCorrect
    params.Sha2_192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224
    params.Sha2_192s.Insts.Slh_dsaParamsDerAlgorithm Spec.sha2_192s (slhOid 22#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) sha2_192s_parsers
#print axioms sha2_192s_der

theorem sha2_192f_der : DerCorrect
    params.Sha2_192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664
    params.Sha2_192f.Insts.Slh_dsaParamsDerAlgorithm Spec.sha2_192f (slhOid 23#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) sha2_192f_parsers
#print axioms sha2_192f_der

theorem sha2_256s_der : DerCorrect
    params.Sha2_256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792
    params.Sha2_256s.Insts.Slh_dsaParamsDerAlgorithm Spec.sha2_256s (slhOid 24#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) sha2_256s_parsers
#print axioms sha2_256s_der

theorem sha2_256f_der : DerCorrect
    params.Sha2_256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856
    params.Sha2_256f.Insts.Slh_dsaParamsDerAlgorithm Spec.sha2_256f (slhOid 25#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) sha2_256f_parsers
#print axioms sha2_256f_der

theorem shake_128s_der : DerCorrect
    params.Shake128s.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU87856
    params.Shake128s.Insts.Slh_dsaParamsDerAlgorithm Spec.shake_128s (slhOid 26#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) shake_128s_parsers
#print axioms shake_128s_der

theorem shake_128f_der : DerCorrect
    params.Shake128f.Insts.Slh_dsaParamsCoreArrayU864ArrayU832ArrayU817088
    params.Shake128f.Insts.Slh_dsaParamsDerAlgorithm Spec.shake_128f (slhOid 27#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) shake_128f_parsers
#print axioms shake_128f_der

theorem shake_192s_der : DerCorrect
    params.Shake192s.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU816224
    params.Shake192s.Insts.Slh_dsaParamsDerAlgorithm Spec.shake_192s (slhOid 28#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) shake_192s_parsers
#print axioms shake_192s_der

theorem shake_192f_der : DerCorrect
    params.Shake192f.Insts.Slh_dsaParamsCoreArrayU896ArrayU848ArrayU835664
    params.Shake192f.Insts.Slh_dsaParamsDerAlgorithm Spec.shake_192f (slhOid 29#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) shake_192f_parsers
#print axioms shake_192f_der

theorem shake_256s_der : DerCorrect
    params.Shake256s.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU829792
    params.Shake256s.Insts.Slh_dsaParamsDerAlgorithm Spec.shake_256s (slhOid 30#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) shake_256s_parsers
#print axioms shake_256s_der

theorem shake_256f_der : DerCorrect
    params.Shake256f.Insts.Slh_dsaParamsCoreArrayU8128ArrayU864ArrayU849856
    params.Shake256f.Insts.Slh_dsaParamsDerAlgorithm Spec.shake_256f (slhOid 31#u8) :=
  der_spec _ _ _ _ (by with_unfolding_all rfl) shake_256f_parsers
#print axioms shake_256f_der

end slh_dsa
