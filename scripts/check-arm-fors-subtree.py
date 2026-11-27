#!/usr/bin/env python3
"""Check Arm FORS subtree extraction, native leaf register routing and FIPS theorems."""
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

here = Path(__file__).resolve().parent
facade = runpy.run_path(str(here / "check-platform-facade.py"))
keygen = runpy.run_path(str(here / "check-arm-keygen.py"))
root, lean = facade["ROOT"], facade["LEAN"]
cuts = ["crate::sha256::arm_wide", "crate::sha512::paired", "crate::hash::thash_pair"]


def check_leaves(tmp):
    rust = (root / "rust/src/sha256/arm_wide.rs").read_text()
    helpers = ("load_shared_head", "step4_shared_head", "fors_leaves_active")
    body = "\n".join(keygen["function"](rust, name) for name in helpers)
    body = body.replace("super::K", "K").replace("first_idx: u32", "first_idx: Base")
    body = body.replace("out: &mut [[u8; N]]", "out: &mut [[usize; N]]")
    body = re.sub(r"vld1q_u32\((head\.(?:m0|a1|e1))\.as_ptr\(\)\)", r"\1", body)
    machine = (here / "arm-wots/hash-routes.rs").read_text().split("// PRODUCTION", 1)[0]
    machine = machine.replace("fn make_hdr(c: u32, t: u32)", "fn make_hdr(c: u32, t: Base)")
    machine = machine.replace("    (c, t)\n", "    (c, t.0)\n")
    harness = (here / "arm-forstree/leaves.rs").read_text()
    source = tmp / "leaves.rs"
    source.write_text(machine + harness.replace("// PRODUCTION", body))
    subprocess.run(["rustc","--edition=2021","-Awarnings","-C","overflow-checks=yes",source,"-o",tmp/"leaves"],check=True)
    subprocess.run([tmp/"leaves"],check=True)


def decls(path, ns):
    common = facade["common"]
    return list(common["declarations"](common["body"](path, ns)))


def check(target, tmp):
    tmp.mkdir()
    actual = facade["extract"]("rust", target, "ArmForsTree", tmp, ["crate::fors::arm::subtree"], cuts)
    translated = []
    for item in decls(actual/"Funs.lean", "slhdsa"):
        if "def fors.arm.subtree" not in item:
            if item not in decls(lean.parent/"lean/Slhdsa/Funs.lean", "slhdsa"):
                raise ValueError(f"{target}: unknown address operation")
            continue
        if any(name in item for name in ("def fors.arm.subtree_loop1.body", "def fors.arm.subtree_loop1\n", "def fors.arm.subtree\n")):
            item = item.replace("{N : Std.Usize}", "(enabled : Bool) {N : Std.Usize}")
            item = item.replace("sha512.paired.parents_batch", "parentSliceAt 128#usize enabled")
            item = item.replace("subtree_loop1.body index", "subtree_loop1.body enabled index")
            item = item.replace("subtree_loop1 iter", "subtree_loop1 enabled iter")
        translated.append(item.replace("sha256.arm_wide.parents_16","smallSliceAt 128#usize")
                          .replace("sha256.arm_wide.fors_leaves","fillLeaves"))
    checked = [item for item in decls(lean/"Armwide/ForsTree/Program.lean", "slhdsa.ArmForsTree")
               if "def fors.arm.subtree" in item]
    if len(translated) != 7 or translated != checked:
        raise ValueError(f"{target}: FORS subtree driver differs")
    if set(decls(actual/"Types.lean", "slhdsa")) - set(decls(lean.parent/"lean/Slhdsa/Types.lean", "slhdsa")):
        raise ValueError(f"{target}: seed or address changed")
    print(f"{target}: matched all seven FORS subtree declarations",flush=True)


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        check_leaves(folder)
        for target in facade["TARGETS"][:2]:
            check(target,folder / target)
    facade["run"](["lake","build","Armwide.ForsTree.Top"],lean)
    facade["audit_theorems"]("Armwide.ForsTree.Top",
        ["slhdsa.ArmForsTree." + name for name in ("fused_leaf_fips","shared_tail","reduceSmall","reduceWide","subtree_fips")])
