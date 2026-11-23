#!/usr/bin/env python3
"""Re-extract the named public SHA-2 operations and check their FIPS theorems on both Arm targets."""
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean-hw"
SETS = tuple(f"sha2_{bits}{speed}" for bits in (128, 192, 256) for speed in ("s", "f"))
KEY_OPERATIONS = ("keygen", "public_key", "slh_keygen_internal")
INTERNAL = ("slh_sign_internal", "slh_verify_internal")
OPERATIONS = KEY_OPERATIONS + INTERNAL
TARGETS = {"aarch64-apple-darwin": "ArmApple", "aarch64-unknown-linux-gnu": "ArmLinuxTarget"}
os.environ["PATH"] = os.pathsep.join(str(Path.home() / tool / "bin") for tool in (".elan", ".cargo")) + os.pathsep + os.environ["PATH"]


def run(args, cwd, **kwargs):
    return subprocess.run(args, cwd=cwd, check=True, **kwargs)


def body(path, namespace="slhdsa"):
    text = path.read_text()
    before, separator, after = text.partition(f"\nnamespace {namespace}\n")
    if not separator or not after.rstrip().endswith(f"end {namespace}"):
        raise ValueError(f"unexpected Aeneas namespace in {path}")
    return after.rstrip().removesuffix(f"end {namespace}")


def declarations(text):
    """Aeneas prefixes each declaration with its Rust source doc comment."""
    for item in re.split(r"/--.*?-/", text, flags=re.DOTALL):
        if item.strip():
            yield item.strip()


def checked_external_bindings(package):
    # Keep the exact Aeneas binder signatures. Every external resolves to an
    # existing model explicitly, and the fresh translation calls these bindings.
    aliases = []
    models = "\n".join((LEAN / "Slhdsa" / f).read_text() for f in ("FunsExternal.lean", "TypesExternal.lean"))
    for path in sorted(package.glob("*External_Template.lean"), reverse=True):
        text = path.read_text()
        text = text[text.index("/-- "):]
        for declaration in declarations(text):
            m = re.fullmatch(r"(?:@\[.*?\]\s*)?axiom\s+([^\s:]+)\s*(.*)", declaration, re.DOTALL)
            if not m:
                raise ValueError(f"unexpected external declaration in {path}: {declaration}")
            name, signature = m.groups()
            if re.search(rf"^def {re.escape(name)}\b", models, re.MULTILINE):
                owner = "_root_" if path.name.startswith("Types") else "slhdsa"
            elif name in ("core.slice.raw.from_ref", "core.slice.Slice.as_chunks",
                          "sha2.sha256.compress256", "sha2.sha512.compress512"):
                owner = "ArmStreamRust"
            elif name in ("sha512.parents.parents", "sha512.parents.path_parents"):
                owner = "ParentarmRust"
            else:
                raise ValueError(f"no verified binding for {name}")
            # The only polymorphic reference in this extraction is slice::from_ref.
            binders = signature.split(":", 1)[0]
            args = " T N" if name == "core.slice.Slice.as_chunks" else (
                " T" if "{T" in binders else " N" if "{N" in binders else "")
            aliases.append(f"abbrev {name} {signature} := @{owner}.{name}{args}")
    return "\n".join(aliases)


def check_target(target, namespace, scratch):
    package = scratch / "Slhdsa"
    package.mkdir()
    roots = [f"crate::sets::{s}::{f}" for s in SETS for f in OPERATIONS]
    roots.append("crate::slh::message::digest")
    charon = ROOT / ".tools/aeneas/charon/bin/charon"
    run([charon, "cargo", "--preset=aeneas", *(a for r in roots for a in ("--start-from", r)),
         "--opaque", "crate::sha256::hw::arm", "--opaque", "crate::sha512::hw::arm",
         "--opaque", "sha2::sha512::compress512", "--opaque", "sha2::sha256::compress256",
         "--opaque", "crate::sha512::parents::parents", "--opaque", "crate::sha512::parents::path_parents",
         "--dest-file", scratch / "slhdsa.llbc",
         "--", "--locked", "--features", "platform-sha2", "--target", target], ROOT / "rust")
    run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error", "-no-progress-bar",
         "-split-files", "-dest", package, scratch / "slhdsa.llbc"], ROOT)
    check_extraction(package, namespace, scratch)


def check_extraction(package, namespace, scratch):
    # Lean structures from different modules have nominal identity. Share only
    # declarations whose complete definitions match the checked hardware build.
    types = set(declarations(body(LEAN / "Slhdsa/Types.lean")))
    message_types = {item: "SegmentedRust" for item in declarations(body(LEAN / "Segmented/Types.lean", "SegmentedRust"))}
    for item in declarations(body(LEAN / "Segmentedapi/Types.lean", "SegmentedApiRust")):
        if re.match(r"@\[reducible\]\s*def slh\.message\.Sha(?:256|512) :=", item):
            message_types[item] = "SegmentedApiRust"
    aliases = []
    for item in declarations(body(package / "Types.lean")):
        if item in types:
            continue
        if item not in message_types:
            raise ValueError(f"unmatched type declaration: {item}")
        name = re.search(r"(?:structure|def) (slh\.message\.\w+)", item).group(1)
        aliases.append(f"abbrev {name} := {message_types[item]}.{name}")
    source = f"""import Armplatform.Keygen
import Armplatform.LinuxMessageDigest
open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa
set_option maxRecDepth 65536
set_option maxHeartbeats 0
noncomputable section
namespace {namespace}
{chr(10).join(aliases)}
{checked_external_bindings(package)}
{body(package / 'Funs.lean')}
end {namespace}
"""
    root = "LinuxMessage.AppleMessage." if namespace == "ArmLinuxTarget" else "AppleMessage."
    bindings = [(root + "slhdsa.Segmented.digest_spec", root + "SegmentedApiRust.slh.message.digest",
                 namespace + ".slh.message.digest")]
    for s in SETS:
        for op in OPERATIONS:
            fips_proof = f"slhdsa.{s}.{op}_spec"
            entry = f"slhdsa.sets.{s}.{op}"
            if op in INTERNAL:
                owner = "LinuxInternal.AppleInternal." if namespace == "ArmLinuxTarget" else "AppleInternal."
                fips_proof = owner + fips_proof
                entry = owner + entry
            elif namespace == "ArmLinuxTarget":
                fips_proof = "ArmLinux." + fips_proof
                if op != "public_key":
                    entry = "ArmLinux." + entry
            fresh = f"{namespace}.sets.{s}.{op}"
            bindings.append((fips_proof, entry, fresh))
    for fips_proof, entry, fresh in bindings:
        source += (f"run_cmd Lean.Elab.Command.liftCoreM <| PlatformProof.bindEntry "
                   f"`{fips_proof} `{entry} `{fresh} `{fresh}_fips\n#print axioms {fresh}_fips\n")
    proof = scratch / "PublicAPI.lean"
    proof.write_text(source)
    result = subprocess.run(["lake", "env", "lean", proof], cwd=LEAN, stdout=subprocess.PIPE, text=True)
    if result.returncode:
        raise RuntimeError(result.stdout)
    output = result.stdout
    for _, _, fresh in bindings:
        expected = f"'{fresh}_fips' depends on axioms: [propext, Classical.choice, Quot.sound]"
        if expected not in output.splitlines():
            raise ValueError(f"unexpected axiom audit for {fresh}\n{output}")
    print(f"{namespace}: checked {len(SETS) * len(OPERATIONS)} public-entry theorems and segmented H_msg", flush=True)


if __name__ == "__main__":
    run(["lake", "build", "Armplatform.Keygen", "Armplatform.LinuxMessageDigest"], LEAN)
    for arch, namespace in TARGETS.items():
        with tempfile.TemporaryDirectory() as temp:
            check_target(arch, namespace, Path(temp))
