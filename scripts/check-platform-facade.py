#!/usr/bin/env python3
"""Check the feature-selected RustCrypto facade and the core signing adapter on accelerated builds."""
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-arm-api-proof.py")))
ROOT, LEAN, run = common["ROOT"], common["LEAN"], common["run"]
TARGETS = ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu")
FACADE_ROOTS = (
    '{impl crate::params::DerAlgorithm for _}',
    '{impl crate::params::Core for _}',
    '{impl signature::Signer for crate::signing_key::SigningKey}::try_sign',
    '{impl signature::Verifier for crate::verifying_key::VerifyingKey}::verify',
    'crate::signing_key::SigningKey::try_sign_with_context',
    'crate::verifying_key::VerifyingKey::try_verify_with_context',
    'crate::signing_key::SigningKey::new',
    '{impl signature::RandomizedSigner for crate::signing_key::SigningKey}::try_sign_with_rng',
    '{impl core::convert::TryFrom for crate::signature_encoding::Signature}::try_from',
    '{impl core::convert::TryFrom for crate::verifying_key::VerifyingKey}::try_from',
    '{impl core::convert::TryFrom for crate::signing_key::SigningKey}::try_from',
)

def extract(crate, target, package, scratch, roots, cuts, includes=()):
    dest = scratch / package
    llbc = scratch / (package.lower() + ".llbc")
    run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
         *(arg for item in roots for arg in ("--start-from", item)),
         *(arg for item in cuts for arg in ("--opaque", item)),
         *(arg for item in includes for arg in ("--include", item)),
         "--dest-file", llbc, "--", "--locked", "--features", "platform-sha2", "--target", target], ROOT / crate)
    run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error", "-no-progress-bar",
         "-split-files", "-dest", dest, llbc], ROOT)
    return dest


def check_exports(target, scratch):
    roots = ("{impl pkcs8::traits::EncodePrivateKey for crate::signing_key::SigningKey}::to_pkcs8_der",
             "{impl spki::traits::EncodePublicKey for crate::verifying_key::VerifyingKey}::to_public_key_der")
    package = extract("compat", target, "Export", scratch, roots, ())
    program = (LEAN / "Platformadapter/ExportsProgram.lean").read_text()
    fresh_types = set(common["declarations"](common["body"](package / "Types.lean", "slh_dsa")))
    shared = set(common["declarations"](common["body"](LEAN / "Facade/Types.lean", "slh_dsa")))
    for declaration in fresh_types - shared:
        if declaration not in program:
            raise ValueError(f"unmatched exporter nominal type on {target}: {declaration}")
    for declaration in common["declarations"](common["body"](package / "Funs.lean", "slh_dsa")):
        if declaration not in program:
            raise ValueError(f"unmatched exporter function on {target}: {declaration}")
    source = ["import Platformadapter.ExportsProgram", "open Aeneas Aeneas.Std Result",
              "open slh_dsa.PlatformExports", "variable [doc : Documents]"]
    names = set()
    template = (package / "FunsExternal_Template.lean").read_text()
    for item in common["declarations"](template[template.index("/-- "):]):
        match = re.fullmatch(r"(?:@\[.*?\]\s*)?axiom\s+([^\s:]+)\s*:(.*)", item, re.DOTALL)
        if not match:
            raise ValueError(f"unrecognized DER exporter external signature: {item}")
        name, signature = match.groups()
        source.append(f"example : {signature} := {name}")
        names.add(name)
    if names != {"der.document.Document.Insts.CoreConvertTryFromShared0SliceU8Error.try_from",
                 "der.document.SecretDocument.Insts.CoreConvertTryFromShared0SliceU8Error.try_from",
                 "pkcs8.error.Error.Insts.CoreConvertFromError.from", "spki.error.Error.Insts.CoreConvertFromError.from"}:
        raise ValueError(f"unexpected DER export dependency: {names}")
    run(["lake", "env", "lean", "--stdin"], LEAN, input="\n".join(source), text=True)


def check(target, scratch):
    facade = extract("compat", target, "Facade", scratch, FACADE_ROOTS, ("slhdsa::params::Params",))
    for file in ("Types.lean", "Funs.lean"):
        if (facade / file).read_bytes() != (LEAN / "Facade" / file).read_bytes():
            raise ValueError(f"facade {file} differs on {target}")
    roots = tuple("crate::adapter::" + name for name in ("append", "sign_into", "sign_internal_into",
                  "keygen_seeds", "signing_key_from", "signature_from", "bytes_equal"))
    cuts = tuple("crate::slh::" + name for name in ("slh_sign", "slh_sign_internal", "slh_keygen_internal", "with_context"))
    adapter = extract("rust", target, "Adapter", scratch, roots, cuts)
    shared = set(common["declarations"](common["body"](LEAN / "Slhdsa/Funs.lean")))
    program = (LEAN / "Platformadapter/Program.lean").read_text()
    for declaration in common["declarations"](common["body"](adapter / "Funs.lean")):
        if declaration not in shared and declaration not in program:
            raise ValueError(f"unmatched signing adapter function on {target}: {declaration}")
    shared_types = set(common["declarations"](common["body"](LEAN / "Slhdsa/Types.lean")))
    if set(common["declarations"](common["body"](adapter / "Types.lean"))) - shared_types:
        raise ValueError(f"unmatched signing adapter type on {target}")
    external = set(common["declarations"]((adapter / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]))
    reference = set(common["declarations"]((LEAN / "Platformadapter/Bindings.lean.txt").read_text()))
    if external != reference:
        raise ValueError(f"unexpected signing adapter inputs on {target}")
    kat = extract("compat", target, "Kat", scratch,
                  ("crate::signing_key::SigningKey::slh_keygen_internal", "crate::signing_key::SigningKey::slh_sign_internal",
                   "crate::verifying_key::VerifyingKey::slh_verify_internal"), ("crate::multipart::join", "slhdsa::params::Params"))
    shared_kat_types = set(common["declarations"](common["body"](LEAN / "Facade/Types.lean", "slh_dsa")))
    if set(common["declarations"](common["body"](kat / "Types.lean", "slh_dsa"))) - shared_kat_types:
        raise ValueError(f"unmatched KAT nominal types on {target}")
    kat_source = (LEAN / "Platformadapter/KatProgram.lean").read_text()
    for declaration in common["declarations"](common["body"](kat / "Funs.lean", "slh_dsa")):
        if declaration not in kat_source:
            raise ValueError(f"unmatched KAT wrapper implementation on {target}: {declaration}")
    kat_inputs = set(common["declarations"]((kat / "FunsExternal_Template.lean").read_text().split("open slh_dsa", 1)[1]))
    if kat_inputs != {
        '@[rust_fun "core::bool::{bool}::then_some"]\naxiom core.bool.Bool.then_some {T : Type _} : Bool → T → Result (Option T)',
        '@[rust_fun "signature::error::{signature::error::Error}::new"]\naxiom signature.error.Error.new : Result signature.error.Error',
        'axiom multipart.join : Slice (Slice Std.U8) → Result (alloc.vec.Vec Std.U8)',
    }:
        raise ValueError(f"unexpected KAT wrapper dependencies on {target}: {kat_inputs}")
    check_exports(target, scratch)
    print(f"{target}: matched facade, signing adapter, and DER exporters", flush=True)


def audit_theorems(module, theorems):
    source = f"import {module}\n" + "".join(f"#print axioms {name}\n" for name in theorems)
    result = run(["lake", "env", "lean", "--stdin"], LEAN, input=source, text=True, stdout=subprocess.PIPE)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name in theorems:
        reports = re.findall(
            rf"^'{re.escape(name)}' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])$",
            result.stdout, re.MULTILINE,
        )
        if len(reports) != 1 or {x.strip() for x in reports[0].split(",") if x.strip()} - allowed:
            raise ValueError(f"unexpected facade axiom audit for {name}\n{result.stdout}")


def audit(model, module):
    names = [f"sha2_{bits}{speed}_{op}" for bits in (128, 192, 256) for speed in ("s", "f")
             for op in ("sign", "sign_with_context", "verify", "verify_with_context", "randomized_sign", "new", "parsers", "der")]
    names.extend(f"Kat.sha2_{bits}{speed}_{op}" for bits in (128, 192, 256) for speed in ("s", "f")
                 for op in ("algorithms", "errors"))
    names.extend(("multipart_sign_eq", "multipart_verify_eq", "multipart_randomized_eq"))
    theorems = [f"{model}.FacadeContext.FacadeAdapter.slh_dsa.{name}" for name in names]
    audit_theorems(module, theorems)
    print(f"{model}: checked {len(theorems)} facade theorems", flush=True)


if __name__ == "__main__":
    run(["lake", "build", "Platformadapter.Linux", "Platformadapter.X86", "Platformadapter.Exports"], LEAN)
    for target in TARGETS:
        with tempfile.TemporaryDirectory() as temp:
            check(target, Path(temp))
    exports = [f"slh_dsa.PlatformExports.{family}_{bits}{speed}_exports" for family in ("sha2", "shake")
               for bits in (128, 192, 256) for speed in ("s", "f")]
    audit_theorems("Platformadapter.Exports", exports)
    for model, module in (("AppleFacade", "Platformadapter.Apple"),
                          ("LinuxFacade.AppleFacade", "Platformadapter.Linux"),
                          ("X86Facade", "Platformadapter.X86")):
        audit(model, module)
