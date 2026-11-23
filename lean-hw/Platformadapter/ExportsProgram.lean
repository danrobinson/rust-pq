import Facade.Funs
open Aeneas Aeneas.Std Result
open slh_dsa
namespace slh_dsa.PlatformExports

/-- Interface to the external DER document constructors. Their argument, return
value and error conversion remain observable for every possible implementation. -/
class Documents where
  Public : Type
  Secret : Type
  DecodeError : Type
  PkcsError : Type
  SpkiError : Type
  secret : Slice U8 → Result (core.result.Result Secret DecodeError)
  publicDoc : Slice U8 → Result (core.result.Result Public DecodeError)
  pkcsError : DecodeError → Result PkcsError
  spkiError : DecodeError → Result SpkiError

variable [doc : Documents]
abbrev der.document.Document := doc.Public
abbrev der.document.SecretDocument := doc.Secret
abbrev der.error.Error := doc.DecodeError
abbrev pkcs8.error.Error := doc.PkcsError
abbrev spki.error.Error := doc.SpkiError
abbrev der.document.Document.Insts.CoreConvertTryFromShared0SliceU8Error.try_from := doc.publicDoc
abbrev der.document.SecretDocument.Insts.CoreConvertTryFromShared0SliceU8Error.try_from := doc.secret
abbrev pkcs8.error.Error.Insts.CoreConvertFromError.from := doc.pkcsError
abbrev spki.error.Error.Insts.CoreConvertFromError.from := doc.spkiError

/-- [slh_dsa::signing_key::{impl pkcs8::traits::EncodePrivateKey for slh_dsa::signing_key::SigningKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_pkcs8_der::{closure}]
    Source: 'src/signing_key.rs', lines 338:45-338:100 -/
@[reducible]
def signing_key.EncodePrivateKeySigningKey.to_pkcs8_der.closure (P : Type _)
  (Clause0_Clause0_Sk : Type _) (Clause0_Clause1_Vk : Type _)
  (Clause0_Clause2_Sig : Type _) :=
Unit

/-- [slh_dsa::verifying_key::{impl spki::traits::EncodePublicKey for slh_dsa::verifying_key::VerifyingKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_public_key_der::{closure}]
    Source: 'src/verifying_key.rs', lines 152:44-152:93 -/
@[reducible]
def verifying_key.EncodePublicKeyVerifyingKey.to_public_key_der.closure (P :
  Type _) (Clause0_Clause0_Sk : Type _) (Clause0_Clause1_Vk : Type _)
  (Clause0_Clause2_Sig : Type _) :=
Unit


/-- Trait implementation: [pkcs8::error::{impl core::convert::From<der::error::Error> for pkcs8::error::Error}]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/pkcs8-0.11.0/src/error.rs', lines 69:0-69:31
    Name pattern: [core::convert::From<pkcs8::error::Error, der::error::Error>] -/
@[reducible, rust_trait_impl
  "core::convert::From<pkcs8::error::Error, der::error::Error>"]
def pkcs8.error.Error.Insts.CoreConvertFromError : core.convert.From
  pkcs8.error.Error der.error.Error := {
  «from» := pkcs8.error.Error.Insts.CoreConvertFromError.from
}

/-- Trait implementation: [spki::error::{impl core::convert::From<der::error::Error> for spki::error::Error}]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/spki-0.8.1/src/error.rs', lines 59:0-59:31
    Name pattern: [core::convert::From<spki::error::Error, der::error::Error>] -/
@[reducible, rust_trait_impl
  "core::convert::From<spki::error::Error, der::error::Error>"]
def spki.error.Error.Insts.CoreConvertFromError : core.convert.From
  spki.error.Error der.error.Error := {
  «from» := spki.error.Error.Insts.CoreConvertFromError.from
}

/-- [slh_dsa::signing_key::{impl pkcs8::traits::EncodePrivateKey for slh_dsa::signing_key::SigningKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_pkcs8_der::{impl core::ops::function::FnOnce<(&'_0 [u8],), core::result::Result<der::document::SecretDocument, pkcs8::error::Error>> for slh_dsa::signing_key::{impl pkcs8::traits::EncodePrivateKey for slh_dsa::signing_key::SigningKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_pkcs8_der::{closure}<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::call_once]:
    Source: 'src/signing_key.rs', lines 338:45-338:100 -/
def
  signing_key.EncodePrivateKeySigningKey.to_pkcs8_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultSecretDocumentError.call_once
  {P : Type _} {Clause0_Clause0_Sk : Type _} {Clause0_Clause1_Vk : Type _}
  {Clause0_Clause2_Sig : Type _} (paramsCoreInst : params.Core P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig)
  (c : signing_key.EncodePrivateKeySigningKey.to_pkcs8_der.closure P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig)
  (tupled_args : Slice Std.U8) :
  Result (core.result.Result der.document.SecretDocument pkcs8.error.Error)
  := do
  let r ←
    der.document.SecretDocument.Insts.CoreConvertTryFromShared0SliceU8Error.try_from
      tupled_args
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      der.document.SecretDocument pkcs8.error.Error.Insts.CoreConvertFromError
      residual

/-- Trait implementation: [slh_dsa::signing_key::{impl pkcs8::traits::EncodePrivateKey for slh_dsa::signing_key::SigningKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_pkcs8_der::{impl core::ops::function::FnOnce<(&'_0 [u8],), core::result::Result<der::document::SecretDocument, pkcs8::error::Error>> for slh_dsa::signing_key::{impl pkcs8::traits::EncodePrivateKey for slh_dsa::signing_key::SigningKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_pkcs8_der::{closure}<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}]
    Source: 'src/signing_key.rs', lines 338:45-338:100 -/
@[reducible]
def
  signing_key.EncodePrivateKeySigningKey.to_pkcs8_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultSecretDocumentError
  {P : Type _} {Clause0_Clause0_Sk : Type _} {Clause0_Clause1_Vk : Type _}
  {Clause0_Clause2_Sig : Type _} (paramsCoreInst : params.Core P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig) :
  core.ops.function.FnOnce
  (signing_key.EncodePrivateKeySigningKey.to_pkcs8_der.closure P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig) (Slice Std.U8)
  (core.result.Result der.document.SecretDocument pkcs8.error.Error) := {
  call_once :=
    signing_key.EncodePrivateKeySigningKey.to_pkcs8_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultSecretDocumentError.call_once
    paramsCoreInst
}

/-- [slh_dsa::signing_key::{impl pkcs8::traits::EncodePrivateKey for slh_dsa::signing_key::SigningKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_pkcs8_der]:
    Source: 'src/signing_key.rs', lines 335:4-339:5
    Visibility: public -/
def signing_key.SigningKey.Insts.Pkcs8TraitsEncodePrivateKey.to_pkcs8_der
  {P : Type _} {Clause0_Clause0_Sk : Type _} {Clause0_Clause1_Vk : Type _}
  {Clause0_Clause2_Sig : Type _} (paramsCoreInst : params.Core P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig)
  (self : signing_key.SigningKey P Clause0_Clause0_Sk Clause0_Clause1_Vk
  Clause0_Clause2_Sig) :
  Result (core.result.Result der.document.SecretDocument pkcs8.error.Error)
  := do
  let s ← paramsCoreInst.SigningKeyStorageInst.BufferInst.as_slice self.bytes
  paramsCoreInst.with_pkcs8
    (signing_key.EncodePrivateKeySigningKey.to_pkcs8_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultSecretDocumentError
    paramsCoreInst) s ()

/-- [slh_dsa::verifying_key::{impl spki::traits::EncodePublicKey for slh_dsa::verifying_key::VerifyingKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_public_key_der::{impl core::ops::function::FnOnce<(&'_0 [u8],), core::result::Result<der::document::Document, spki::error::Error>> for slh_dsa::verifying_key::{impl spki::traits::EncodePublicKey for slh_dsa::verifying_key::VerifyingKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_public_key_der::{closure}<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::call_once]:
    Source: 'src/verifying_key.rs', lines 152:44-152:93 -/
def
  verifying_key.EncodePublicKeyVerifyingKey.to_public_key_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultDocumentError.call_once
  {P : Type _} {Clause0_Clause0_Sk : Type _} {Clause0_Clause1_Vk : Type _}
  {Clause0_Clause2_Sig : Type _} (paramsCoreInst : params.Core P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig)
  (c : verifying_key.EncodePublicKeyVerifyingKey.to_public_key_der.closure P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig)
  (tupled_args : Slice Std.U8) :
  Result (core.result.Result der.document.Document spki.error.Error)
  := do
  let r ←
    der.document.Document.Insts.CoreConvertTryFromShared0SliceU8Error.try_from
      tupled_args
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      der.document.Document spki.error.Error.Insts.CoreConvertFromError
      residual

/-- Trait implementation: [slh_dsa::verifying_key::{impl spki::traits::EncodePublicKey for slh_dsa::verifying_key::VerifyingKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_public_key_der::{impl core::ops::function::FnOnce<(&'_0 [u8],), core::result::Result<der::document::Document, spki::error::Error>> for slh_dsa::verifying_key::{impl spki::traits::EncodePublicKey for slh_dsa::verifying_key::VerifyingKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_public_key_der::{closure}<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}]
    Source: 'src/verifying_key.rs', lines 152:44-152:93 -/
@[reducible]
def
  verifying_key.EncodePublicKeyVerifyingKey.to_public_key_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultDocumentError
  {P : Type _} {Clause0_Clause0_Sk : Type _} {Clause0_Clause1_Vk : Type _}
  {Clause0_Clause2_Sig : Type _} (paramsCoreInst : params.Core P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig) :
  core.ops.function.FnOnce
  (verifying_key.EncodePublicKeyVerifyingKey.to_public_key_der.closure P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig) (Slice Std.U8)
  (core.result.Result der.document.Document spki.error.Error) := {
  call_once :=
    verifying_key.EncodePublicKeyVerifyingKey.to_public_key_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultDocumentError.call_once
    paramsCoreInst
}

/-- [slh_dsa::verifying_key::{impl spki::traits::EncodePublicKey for slh_dsa::verifying_key::VerifyingKey<P, Clause0_Clause0_Sk, Clause0_Clause1_Vk, Clause0_Clause2_Sig>}::to_public_key_der]:
    Source: 'src/verifying_key.rs', lines 149:4-153:5
    Visibility: public -/
def
  verifying_key.VerifyingKey.Insts.SpkiTraitsEncodePublicKey.to_public_key_der
  {P : Type _} {Clause0_Clause0_Sk : Type _} {Clause0_Clause1_Vk : Type _}
  {Clause0_Clause2_Sig : Type _} (paramsCoreInst : params.Core P
  Clause0_Clause0_Sk Clause0_Clause1_Vk Clause0_Clause2_Sig)
  (self : verifying_key.VerifyingKey P Clause0_Clause0_Sk Clause0_Clause1_Vk
  Clause0_Clause2_Sig) :
  Result (core.result.Result der.document.Document spki.error.Error)
  := do
  let s ←
    paramsCoreInst.VerifyingKeyStorageInst.BufferInst.as_slice self.bytes
  paramsCoreInst.with_spki
    (verifying_key.EncodePublicKeyVerifyingKey.to_public_key_der.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8ResultDocumentError
    paramsCoreInst) s ()

end slh_dsa.PlatformExports
