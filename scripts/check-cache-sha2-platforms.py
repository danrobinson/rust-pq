#!/usr/bin/env python3
"""Bind the six SHA-2 cache primitive calls to fresh platform Rust extractions."""

import re
import subprocess
import runpy
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
cache = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
arm = cache["facade"]["common"]
x86 = runpy.run_path(str(HERE / "check-x86-core-proof.py"))
LEAN = cache["LEAN"]
ROOT = cache["ROOT"]

PRIMITIVES = (
    "hash.seed_ctx",
    "wots.wots_sign",
    "xmss.xmss_sign",
    "xmss.xmss_pk_from_sig",
    "fors.fors_sign",
    "fors.fors_pk_from_sig",
)
ARM_CUTS = (
    "crate::sha256::hw::arm",
    "crate::sha512::hw::arm",
    "sha2::sha256::compress256",
    "sha2::sha512::compress512",
    "crate::sha512::parents::parents",
    "crate::sha512::parents::path_parents",
)
PORTABLE = {
    f"sha{n}.compress_portable": f"slhdsa.sha{n}.compress_portable" for n in (256, 512)
}
TARGETS = {
    "aarch64-apple-darwin": "AppleCached",
    "aarch64-unknown-linux-gnu": "LinuxArmCached.AppleCached",
    "x86_64-unknown-linux-gnu": "X86Cached",
    "riscv64gc-unknown-none-elf": "PortableCached",
}


# The current Arm implementation adds six early returns before the older
# independently extracted fallbacks. Check the full guard and every argument
# before projecting those fallbacks; the enabled callbacks are checked separately
# by check-arm-sha256-wide.py and check-arm-sha512-callers.py.
def extract_arm(target, directory):
    crate = cache["copy_rust_crate"](directory)
    for module, calls in {
        "wots": [
            "arm::pk_gen(sk_seed, seed, adrs)",
            "arm::sign(m, sk_seed, seed, adrs)",
            "arm::recover(sig, m, seed, adrs)",
        ],
        "xmss": ["arm::batch_root(sk_seed, i, z, seed, adrs)"],
        "fors": [
            "arm::subtree(sk_seed, i, z, seed, adrs)",
            "arm::pk_from_sig(p, sig, md, seed, adrs)",
        ],
    }.items():
        path = crate / "src" / (module + ".rs")
        text = path.read_text()
        for call in calls:
            indent = "        " if module == "xmss" else "    "
            height = "(1..=4).contains(&z) && " if module == "xmss" else ""
            block = (
                indent
                + '#[cfg(all(feature = "platform-sha2", target_arch = "aarch64", target_endian = "little"))]\n'
                + indent
                + "if matches!(N, 16 | 24 | 32) && "
                + height
                + "crate::sha256::arm_wide::available() {\n"
                + indent
                + "    return "
                + call
                + ";\n"
                + indent
                + "}"
            )
            if text.count(block) != 1:
                raise ValueError(f"unrecognized Arm dispatch to {call}")
            text = text.replace(block, "")
        path.write_text(text)
    return cache["facade"]["extract"](
        crate,
        target,
        "Primitive",
        directory,
        ["crate::" + name.replace(".", "::") for name in PRIMITIVES],
        ARM_CUTS,
    )


def bind_external(package, bindings):
    aliases = []
    for path in sorted(package.glob("*External_Template.lean")):
        text = path.read_text()
        for item in arm["declarations"](text[text.index("/-- ") :]):
            match = re.fullmatch(r"axiom\s+(\S+)\s+(.*)", item, re.S)
            if not match or match[1] not in bindings:
                raise ValueError(f"unbound platform primitive: {item}")
            name, signature = match.groups()
            args = " N" if signature.startswith(("{N :", "(N :")) else ""
            aliases.append(f"abbrev {name} {signature} := @{bindings[name]}{args}")
    return "\n".join(aliases)


def check(target, owner, directory):
    bindings = PORTABLE if owner == "PortableCached" else x86["CORE_BINDINGS"]
    cuts = (
        ARM_CUTS
        if target.startswith("aarch64")
        else tuple("crate::" + name.replace(".", "::") for name in bindings)
    )
    package = (
        extract_arm(target, directory)
        if target.startswith("aarch64")
        else cache["facade"]["extract"](
            "rust",
            target,
            "Primitive",
            directory,
            ["crate::" + name.replace(".", "::") for name in PRIMITIVES],
            cuts,
        )
    )
    bind(target, owner, directory, package, bindings)


def bind(target, owner, directory, package, bindings):
    shared = set(arm["declarations"](arm["body"](LEAN / "Slhdsa/Types.lean")))
    if set(arm["declarations"](arm["body"](package / "Types.lean"))) - shared:
        raise ValueError(f"unmatched nominal type on {target}")
    aliases = (
        arm["checked_external_bindings"](package)
        if target.startswith("aarch64")
        else bind_external(package, bindings)
    )
    original = set(arm["declarations"](arm["body"](LEAN / "Slhdsa/Funs.lean")))
    functions = []
    for item in arm["declarations"](arm["body"](package / "Funs.lean")):
        literal = re.fullmatch(
            r"@\[global_simps, irreducible\] def (\S+) : (.*?) := ([\s\S]+)", item
        )
        # Intern only identical closed literals. Checking the entire declaration
        # includes the type and value of all domain tags, widths and IV words.
        if (
            literal
            and item in original
            and not re.search(r"[a-zA-Z_]\w*\.", literal[3])
        ):
            functions.append(
                f"abbrev {literal[1]} : {literal[2]} := slhdsa.{literal[1]}"
            )
        else:
            functions.append(item)
    proof = (
        """import Cachepath.PlatformSha2Linux
open Aeneas Aeneas.Std Result ControlFlow Error
open slhdsa
set_option maxRecDepth 65536
set_option maxHeartbeats 0
noncomputable section
namespace FreshCachePrimitives
"""
        + aliases
        + "\n"
        + "\n\n".join(functions)
        + "\nend FreshCachePrimitives\n"
    )
    # Name resolution uses the platform implementation when replay changed it
    # and the shared definition otherwise, including Linux inheriting Apple.
    # The second Linux replay can rewrite either an Apple-specific helper or
    # a shared helper. Resolve each through the actual signer's dependency graph.
    opened = ["CacheopsRust"]
    for part in reversed(owner.split(".")):
        opened += [part + "." + namespace for namespace in opened]
    calls = {
        "hash.seed_ctx": (
            "(seed : Std.Array U8 N)",
            "(do let s ← FreshCachePrimitives.hash.seed_ctx seed; ok (CacheopsRust.fromSlhSeed s))",
            "seed",
        ),
        "wots.wots_sign": ("(m sk : Std.Array U8 N)", "m sk cs ca", "m sk s a"),
        "xmss.xmss_sign": (
            "(m sk : Std.Array U8 N) (idx : U32)",
            "cp m sk idx cs ca",
            "p m sk idx s a",
        ),
        "xmss.xmss_pk_from_sig": (
            "(idx : U32) (sig : Slice U8) (m : Std.Array U8 N)",
            "cp idx sig m cs ca",
            "p idx sig m s a",
        ),
        "fors.fors_sign": (
            "(md : Slice U8) (sk : Std.Array U8 N)",
            "cp md sk cs ca",
            "p md sk s a",
        ),
        "fors.fors_pk_from_sig": (
            "(sig md : Slice U8)",
            "cp sig md cs ca",
            "p sig md s a",
        ),
    }
    namespaces = ", ".join("`" + ns for ns in opened)
    proof += f"""
open Lean Elab Command
private partial def visit (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  if let some decl := env.find? n then
    if let some body := decl.value? then
      for child in body.getUsedConstants do
        if [{namespaces}].any (·.isPrefixOf child) then visit env child
run_cmd do
  let env ← getEnv
  let (_, reached) := (visit env `{owner}.CacheopsRust.cache.sha2_ops.sign_from_digest).run {{}}
"""
    for name, (binders, fresh, args) in calls.items():
        choices = ", ".join("`" + ns + "." + name for ns in reversed(opened))
        if name != "hash.seed_ctx":
            fresh = (
                "FreshCachePrimitives."
                + name
                + " "
                + fresh.replace("cp", "(CacheopsRust.toSlhParams p)")
                .replace("cs", "(CacheopsRust.toSlhSeed s)")
                .replace("ca", "(CacheopsRust.toSlhAdrs a)")
            )
        proof += f"""  let some target := [{choices}].find? reached.contains | throwError "unreachable primitive {name}"
  let cmd ← `(example {{N : Usize}} (p : CacheopsRust.params.Params) (s : CacheopsRust.hash.Seed N)
    (a : CacheopsRust.address.Adrs) {binders} :
    {fresh} = $(mkIdent target) {args} := by with_unfolding_all rfl)
  elabCommand cmd
"""
    proof += f"#print axioms {owner}.slhdsa.cache.endtoend.sign_from_digest_with_cache_spec\n"
    path = directory / "Bindings.lean"
    path.write_text(proof)
    result = subprocess.run(
        ["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True
    )
    if result.returncode or "[propext, Classical.choice, Quot.sound]" not in " ".join(
        result.stdout.split()
    ):
        raise ValueError(result.stdout + result.stderr)
    scope = (
        "Arm wide-disabled fallbacks"
        if target.startswith("aarch64")
        else "selected primitives"
    )
    print(
        f"{target}: six freshly extracted {scope} match the cached signer", flush=True
    )


if __name__ == "__main__":
    arm["run"](["lake", "build", "Cachepath.PlatformSha2Linux", "Cachepath.PlatformPortable"], LEAN)
    cache["facade"]["audit_theorems"](
        "Cachepath.PlatformPortable",
        [
            f"PortableSession.CacheopsRust.Public.{name}"
            for name in ("scalar_build_and_sign_many", "scalar_keygen_then_sign_many", "scalar_keygen_sign_verify")
        ],
    )
    cache["facade"]["audit_theorems"](
        "Cachepath.PlatformSha2Linux",
        [
            f"{owner}.CacheopsRust.Public.{name}"
            for owner in TARGETS.values()
            for name in (
                "sign_cached_spec",
                "sign_deterministic_cached_spec",
                "sign_cached_mut_spec",
                "sign_deterministic_cached_mut_spec",
                "new_then_sign",
                "new_then_sign_many",
                "scalar_build_and_sign_many",
            )
        ],
    )
    for target, owner in TARGETS.items():
        with tempfile.TemporaryDirectory() as directory:
            check(target, owner, Path(directory))
