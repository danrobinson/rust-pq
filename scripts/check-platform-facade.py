#!/usr/bin/env python3
"""Check the feature-selected RustCrypto facade and the core signing adapter on accelerated builds."""
from pathlib import Path
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

def extract(crate, target, package, scratch, roots, cuts):
    dest = scratch / package
    llbc = scratch / (package.lower() + ".llbc")
    run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
         *(arg for item in roots for arg in ("--start-from", item)),
         *(arg for item in cuts for arg in ("--opaque", item)),
         "--dest-file", llbc, "--", "--locked", "--features", "platform-sha2", "--target", target], ROOT / crate)
    run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error", "-no-progress-bar",
         "-split-files", "-dest", dest, llbc], ROOT)
    return dest


def check(target, scratch):
    facade = extract("compat", target, "Facade", scratch, FACADE_ROOTS, ("slhdsa::params::Params",))
    for file in ("Types.lean", "Funs.lean"):
        if (facade / file).read_bytes() != (LEAN / "Facade" / file).read_bytes():
            raise ValueError(f"facade {file} differs on {target}")
    cuts = ("crate::adapter::randomizer", "crate::slh::slh_sign", "crate::slh::with_context",
            "crate::slh::slh_sign_internal")
    adapter = extract("rust", target, "Adapter", scratch, ("crate::adapter::sign_into",), cuts)
    text = common["body"](adapter / "Funs.lean").strip()
    if text not in (LEAN / "Platformadapter/Program.lean").read_text():
        raise ValueError(f"signing adapter differs on {target}")
    external = set(common["declarations"]((adapter / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]))
    reference = set(common["declarations"]((LEAN / "Platformadapter/Bindings.lean.txt").read_text()))
    if external != reference:
        raise ValueError(f"unexpected signing adapter inputs on {target}")
    print(f"{target}: matched facade and signing adapter translations", flush=True)


def audit(model, module):
    names = [f"sha2_{bits}{speed}_{op}" for bits in (128, 192, 256) for speed in ("s", "f")
             for op in ("sign", "sign_with_context", "verify", "verify_with_context", "randomized_sign", "new", "parsers", "der")]
    names.extend(("multipart_sign_eq", "multipart_verify_eq", "multipart_randomized_eq"))
    theorems = [f"{model}.FacadeContext.FacadeAdapter.slh_dsa.{name}" for name in names]
    source = f"import {module}\n" + "".join(f"#print axioms {name}\n" for name in theorems)
    result = run(["lake", "env", "lean", "--stdin"], LEAN, input=source, text=True, stdout=subprocess.PIPE)
    audits = " ".join(result.stdout.split())
    for name in theorems:
        expected = f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        if expected not in audits:
            raise ValueError(f"unexpected facade axiom audit for {name}\n{result.stdout}")
    print(f"{model}: checked {len(theorems)} facade theorems", flush=True)


if __name__ == "__main__":
    for target in TARGETS:
        with tempfile.TemporaryDirectory() as temp:
            check(target, Path(temp))
    run(["lake", "build", "Platformadapter.Linux", "Platformadapter.X86"], LEAN)
    for model, module in (("AppleFacade", "Platformadapter.Apple"),
                          ("LinuxFacade.AppleFacade", "Platformadapter.Linux"),
                          ("X86Facade", "Platformadapter.X86")):
        audit(model, module)
