#!/usr/bin/env python3
"""Bind the two hypertree FIPS theorems to fresh x86 platform Rust extractions."""
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


def check(scratch):
    llbc = scratch / "slhdsa.llbc"
    target = scratch / "Slhdsa"
    roots = [f"crate::ht::{entry}" for entry in ENTRIES]
    opaque = ["crate::" + name.replace(".", "::") for name in BINDINGS]
    run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
         *(arg for name in roots for arg in ("--start-from", name)),
         *(arg for name in opaque for arg in ("--opaque", name)),
         "--dest-file", llbc, "--", "--locked", "--features", "platform-sha2",
         "--target", "x86_64-unknown-linux-gnu"], ROOT / "rust")
    run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error",
         "-no-progress-bar", "-split-files", "-dest", target, llbc], ROOT)
    bind(target, scratch)


def bind(target, scratch):
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
            aliases[name] = f"abbrev {name} {signature} := @{BINDINGS[name]}{args}"
    if aliases.keys() != BINDINGS.keys():
        raise ValueError(f"unexpected external names: {aliases.keys()}")
    source = ["import X86platform.Hypertree", "open Aeneas Aeneas.Std Result ControlFlow Error",
              "open slhdsa", "set_option maxRecDepth 65536", "set_option maxHeartbeats 0",
              "noncomputable section", "namespace X86Hypertree", *aliases.values(),
              body(target / "Funs.lean"), "end X86Hypertree"]
    for entry in ENTRIES:
        source.append("run_cmd Lean.Elab.Command.liftCoreM <| PlatformProof.bindEntry "
                      f"`X86Platform.slhdsa.{entry}_spec `X86Platform.slhdsa.ht.{entry} "
                      f"`X86Hypertree.ht.{entry} `X86Hypertree.ht.{entry}_fips")
        source.append(f"#print axioms X86Hypertree.ht.{entry}_fips")
    proof = scratch / "Hypertree.lean"
    proof.write_text("\n".join(source))
    result = subprocess.run(["lake", "env", "lean", proof], cwd=LEAN, stdout=subprocess.PIPE, text=True)
    if result.returncode:
        raise RuntimeError(result.stdout)
    for entry in ENTRIES:
        expected = (f"'X86Hypertree.ht.{entry}_fips' depends on axioms: "
                    "[propext, Classical.choice, Quot.sound]")
        if expected not in result.stdout.splitlines():
            raise ValueError(f"unexpected axiom audit for {entry}\n{result.stdout}")
        print(expected)


if __name__ == "__main__":
    run(["lake", "build", "X86platform.Hypertree"], LEAN)
    with tempfile.TemporaryDirectory() as temp:
        check(Path(temp))
