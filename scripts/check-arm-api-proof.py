#!/usr/bin/env python3
"""Re-extract the named public SHA-2 operations and check their FIPS theorems on both Arm targets."""
import os
from pathlib import Path
import re
import subprocess
import runpy

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


def checked_external_bindings(package, overrides=None):
    # Keep the exact Aeneas binder signatures. Every external resolves to an
    # existing model explicitly, and the fresh translation calls these bindings.
    overrides = overrides or {}
    selected = set()
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
            if name in overrides:
                selected.add(name)
                aliases.append(f"abbrev {name} {signature} := {overrides[name]}")
                continue
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
    if selected != set(overrides):
        raise ValueError(f"expected source cutpoints absent: {set(overrides) - selected}")
    return "\n".join(aliases)


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


if __name__ == "__main__":
    runpy.run_path(str(Path(__file__).with_name("check-arm-wide-signature.py")), run_name="__main__")
