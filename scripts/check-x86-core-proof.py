#!/usr/bin/env python3
"""Bind the public SHA-2 internal algorithms, FORS and hypertree proofs to fresh x86 Rust."""
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-arm-api-proof.py")))
ROOT, LEAN = common["ROOT"], common["LEAN"]
body, declarations, run = common["body"], common["declarations"], common["run"]
ENTRIES = ("ht_sign", "ht_verify")
BINDINGS = {
    "sha256.compress": "X86RemainderRust.sha256.compress",
    "sha512.compress": "X86RemainderRust.sha512.compress",
    "sha256.x86.chain_blocks": "WotsApiRust.sha256.x86.chain_blocks",
    "xmss.xmss_node": "slhdsa.X86.Platform.node",
    "wots.wots_pk_from_sig": "slhdsa.X86.Platform.recover",
}


# Every external name below resolves to its separately source-gated extraction.
CORE_BINDINGS = {
    **BINDINGS,
    "sha256.x86.avx512_available": "WotsApiRust.sha256.x86.avx512_available",
    "fors.wide.subtree": "slhdsa.X86.Platform.subtree",
    "sha512.parents.parents": "Parentx86Rust.sha512.parents.parents",
    "sha512.parents.path_parents": "Parentx86Rust.sha512.parents.path_parents",
    "sha256.sha256_from": "X86StreamRust.sha256.sha256_from",
    "sha512.sha512_from": "X86StreamRust.sha512.sha512_from",
}
TREE_ENTRIES = [(f"ht.{e}", f"X86Platform.slhdsa.{e}_spec", f"X86Platform.slhdsa.ht.{e}") for e in ENTRIES]
CORE_ENTRIES = [(f"sets.{s}.{e}", f"X86Internal.slhdsa.{s}.{e}_spec", f"X86Internal.slhdsa.sets.{s}.{e}")
                for s in common["SETS"] for e in ("slh_keygen_internal", "slh_sign_internal", "slh_verify_internal")]
CORE_ENTRIES.extend((f"fors.{e}", f"X86Core.slhdsa.{e}_spec", f"X86Core.slhdsa.fors.{e}")
                    for e in ("fors_sign", "fors_pk_from_sig"))

PUBLIC_BINDINGS = {**CORE_BINDINGS,
                   "slh.message.randomizer": "X86Message.SegmentedApiRust.slh.message.randomizer",
                   "slh.message.digest": "X86Message.SegmentedApiRust.slh.message.digest"}
PUBLIC_ENTRIES = [(f"sets.{s}.{e}", f"X86Public.slhdsa.{s}.{e}_spec", f"X86Public.slhdsa.sets.{s}.{e}")
                  for s in common["SETS"]
                  for e in ("slh_sign", "slh_verify", "sign", "sign_deterministic", "verify")]


def check(scratch, entries, bindings, module, namespace, rust_target="x86_64-unknown-linux-gnu"):
    llbc = scratch / "slhdsa.llbc"
    target = scratch / "Slhdsa"
    roots = ["crate::" + entry.replace(".", "::") for entry, _, _ in entries]
    opaque = ["crate::" + name.replace(".", "::") for name in bindings]
    run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
         *(arg for name in roots for arg in ("--start-from", name)),
         *(arg for name in opaque for arg in ("--opaque", name)),
         "--dest-file", llbc, "--", "--locked", "--features", "platform-sha2",
         "--target", rust_target], ROOT / "rust")
    run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error",
         "-no-progress-bar", "-split-files", "-dest", target, llbc], ROOT)
    bind(target, scratch, entries, bindings, module, namespace)


def bind(target, scratch, entries, bindings, module, namespace):
    types = set(declarations(body(LEAN / "Slhdsa/Types.lean")))
    for declaration in declarations(body(target / "Types.lean")):
        if declaration not in types:
            raise ValueError(f"unmatched extracted type: {declaration}")
    aliases = {}
    for path in target.glob("*External_Template.lean"):
        text = path.read_text()
        for declaration in declarations(text[text.index("/-- "):]):
            match = re.fullmatch(r"axiom\s+([^\s:]+)\s*(.*)", declaration, re.DOTALL)
            if not match:
                raise ValueError(f"unexpected external in {path}: {declaration}")
            name, signature = match.groups()
            args = " N" if signature.startswith(("{N :", "(N :")) else ""
            aliases[name] = f"abbrev {name} {signature} := @{bindings[name]}{args}"
    if aliases.keys() != bindings.keys():
        raise ValueError(f"unexpected external names: {aliases.keys()}")
    source = [f"import {module}", "open Aeneas Aeneas.Std Result ControlFlow Error",
              "open slhdsa", "set_option maxRecDepth 65536", "set_option maxHeartbeats 0",
              "noncomputable section", f"namespace {namespace}", *aliases.values(),
              body(target / "Funs.lean"), f"end {namespace}"]
    for entry, theorem, reference in entries:
        source.append("run_cmd Lean.Elab.Command.liftCoreM <| PlatformProof.bindEntry "
                      f"`{theorem} `{reference} `{namespace}.{entry} `{namespace}.{entry}_fips")
        source.append(f"#print axioms {namespace}.{entry}_fips")
    proof = scratch / "SourceBinding.lean"
    proof.write_text("\n".join(source))
    result = subprocess.run(["lake", "env", "lean", proof], cwd=LEAN, stdout=subprocess.PIPE, text=True)
    if result.returncode:
        raise RuntimeError(result.stdout)
    for entry, _, _ in entries:
        expected = (f"'{namespace}.{entry}_fips' depends on axioms: "
                    "[propext, Classical.choice, Quot.sound]")
        if expected not in result.stdout.splitlines():
            raise ValueError(f"unexpected axiom audit for {entry}\n{result.stdout}")
        print(expected)


if __name__ == "__main__":
    for entries, bindings, module, ns in [
        (TREE_ENTRIES, BINDINGS, "X86platform.Hypertree", "X86Hypertree"),
        (CORE_ENTRIES, CORE_BINDINGS, "X86platform.Sets", "X86InternalTarget"),
        (PUBLIC_ENTRIES, PUBLIC_BINDINGS, "X86platform.Public", "X86PublicTarget"),
    ]:
        run(["lake", "build", module], LEAN)
        with tempfile.TemporaryDirectory() as temp:
            check(Path(temp), entries, bindings, module, ns)
