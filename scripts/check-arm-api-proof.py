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
CONTEXT = ("sign", "sign_deterministic", "verify", "slh_sign", "slh_verify")
OPERATIONS = KEY_OPERATIONS + INTERNAL + CONTEXT
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


def arm_agreement(set_name, operation, fresh, arch):
    """Compare the fresh public entry to the other target's source-bound theorem."""
    peer = "linux" if arch == "ArmApple" else "apple"
    entry, theorem = arm_entry(set_name, operation, peer)
    return agreement(set_name, operation, fresh + "_arm_agreement", fresh, fresh + "_fips", entry, theorem)


def arm_entry(set_name, operation, target):
    linux = target == "linux"
    if operation in KEY_OPERATIONS:
        owner = "ArmLinux." if linux else ""
    elif operation in CONTEXT:
        owner = ("LinuxContext." if linux else "") + "AppleContext.SegmentedSdk."
    else:
        owner = ("LinuxInternal." if linux else "") + "AppleInternal."
    entry = ("" if operation == "public_key" else owner) + f"slhdsa.sets.{set_name}.{operation}"
    return entry, owner + f"slhdsa.{set_name}.{operation}_spec"


def agreement(set_name, operation, name, lhs, lhs_proof, rhs, rhs_proof):
    family, shape = set_name.split("_")
    n = int(shape[:-1]) // 8
    context = operation in CONTEXT
    key = operation in KEY_OPERATIONS
    types = {"m":"Slice U8","sig":"Slice U8","ctx":"Slice U8"}
    for arg, size in (("pk",2*n),("sk",4*n),("seeds",3*n),
                      ("addrnd",n),("sk_seed",n),("sk_prf",n),("pk_seed",n)):
        types[arg] = f"Array U8 {size}#usize"
    if operation == "keygen":
        args = "seeds sk pk"
    elif operation == "slh_keygen_internal":
        args = "sk_seed sk_prf pk_seed"
    elif operation == "public_key":
        args = "sk"
    elif "verify" in operation:
        args = "m sig ctx pk" if context else "m sig pk"
    else:
        args = ("m ctx sk" if context else "m sk") + ("" if "deterministic" in operation else " addrnd")
    binders = " ".join(f"({a} : {types[a]})" for a in args.split())
    proof_args = args
    if family == "shake" and context:
        binders += " (hm : Shake.ContextFits m ctx)"
        proof_args += " hm"
    elif family == "sha2" and not key:
        slack = (409 if n == 16 else 561) if context else (152 if n == 16 else 304)
        binders += f" (hm : Room m.length {slack})"
        proof_args += " hm"
    if "keygen" in operation:
        observe = "(fun r => (bytes r.1.val, bytes r.2.val))"
    elif "verify" in operation:
        observe = "id"
    elif "sign" in operation and context:
        observe = "(fun r => r.map (fun v => bytes v.val))"
    else:
        observe = "(fun r => bytes r.val)"
    return f"""
theorem {name} {binders} :
    PeerEquality.SameOutput ({lhs} {args}) ({rhs} {args}) {observe} :=
  PeerEquality.sameOutput ({lhs_proof} {proof_args}) ({rhs_proof} {proof_args})
#print axioms {name}
"""


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
    source = f"""import PeerEquality.Outputs
import Armplatform.Keygen
import Armplatform.LinuxMessageDigest
import Armplatform.LinuxContext
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
            if op in CONTEXT:
                owner = "AppleContext.SegmentedSdk."
                if namespace == "ArmLinuxTarget":
                    owner = "LinuxContext." + owner
                fips_proof = owner + fips_proof
                entry = owner + entry
            elif op in INTERNAL:
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
    for s in SETS:
        for op in OPERATIONS:
            source += arm_agreement(s, op, f"{namespace}.sets.{s}.{op}", namespace)
    proof = scratch / "PublicAPI.lean"
    proof.write_text(source)
    result = subprocess.run(["lake", "env", "lean", proof], cwd=LEAN, stdout=subprocess.PIPE, text=True)
    if result.returncode:
        raise RuntimeError(result.stdout)
    # Lean wraps long qualified names' axiom lists across multiple lines.
    # Normalize only bracketed audit records and retain every axiom name.
    output = re.sub(r"(?m)^('[^'\n]+' depends on axioms: )\[([^\]]*)\]",
                    lambda m: m[1] + "[" + " ".join(m[2].split()) + "]", result.stdout)
    for _, _, fresh in bindings:
        expected = f"'{fresh}_fips' depends on axioms: [propext, Classical.choice, Quot.sound]"
        if expected not in output.splitlines():
            raise ValueError(f"unexpected axiom audit for {fresh}\n{output}")
    for s in SETS:
        for op in OPERATIONS:
            name = f"{namespace}.sets.{s}.{op}_arm_agreement"
            if f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in output.splitlines():
                raise ValueError(f"unexpected axiom audit for {name}")
    print(f"{namespace}: checked {len(SETS) * len(OPERATIONS)} cross-target equivalences")
    print(f"{namespace}: checked {len(SETS) * len(OPERATIONS)} public-entry theorems and segmented H_msg", flush=True)


if __name__ == "__main__":
    run(["lake", "build", "PeerEquality.Outputs", "Armplatform.Keygen", "Armplatform.LinuxMessageDigest", "Armplatform.LinuxContext"], LEAN)
    for arch, namespace in TARGETS.items():
        with tempfile.TemporaryDirectory() as temp:
            check_target(arch, namespace, Path(temp))
