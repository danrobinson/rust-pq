#!/usr/bin/env python3
"""Bind native FORS signing and both dispatcher fallbacks to fresh Arm Rust extractions."""
from pathlib import Path
import re
import runpy
import tempfile

here = Path(__file__).resolve().parent
subtree = runpy.run_path(str(here / "check-arm-fors-subtree.py"))
facade, lean = subtree["facade"], subtree["lean"]
cuts = ["crate::fors::arm::subtree", "crate::sha256", "crate::sha512", "crate::hash::thash_pair", "crate::hash::short_block", "crate::hash::pair_block", "crate::hash::chain_blocks", "crate::hash::value",
        "crate::xmss", "crate::util", "crate::fors::fors_sk_gen"]


def flat(text):
    return " ".join(text.split())


def check(target, tmp):
    tmp.mkdir()
    actual = facade["extract"]("rust", target, "ForsSign", tmp, ["crate::fors::fors_sign"], cuts)
    program = flat((lean / "Armwide/ForsTree/EntryProgram.lean").read_text())
    common = flat((lean.parent / "lean/Slhdsa/Funs.lean").read_text())
    parents = flat((lean / "Armplatform/ForsProgram.lean").read_text())
    checked = set()
    for item in subtree["decls"](actual / "Funs.lean", "slhdsa"):
        name = re.search(r"\bdef (\S+)",item)[1]
        if name.startswith("fors.fors_batch_loop"):
            # Aeneas duplicated the fallback when lowering the two early returns.
            item = re.sub(r"fors_batch_loop([4-7])",lambda m: "fors_batch_loop"+str(int(m[1])-4),item)
            if "def fors.fors_batch_loop3.body" in item or "def fors.fors_batch_loop3\n" in item:
                item = re.sub(r"(def fors\.fors_batch_loop3(?:\.body)?)\n",r"\1 (target : Target)\n",item)
                item = item.replace("sha512.parents.parents ", "parents target ").replace("fors_batch_loop3.body i ", "fors_batch_loop3.body target i ")
                source = parents
            else:
                source = common
        elif name.startswith(("fors.fors_batch","fors.fors_node","fors.fors_sign")):
            source = program
        else:
            source = common
        if flat(item) not in source:
            raise ValueError(f"{target}: unmatched declaration {name}")
        checked.add(name)
    required = {"fors.fors_batch","fors.fors_node","fors.fors_sign","fors.fors_sign_loop0.body",
                "fors.fors_sign_loop0","fors.fors_sign_loop0_loop0","fors.fors_sign_loop0_loop0.body"}
    if not required <= checked:
        raise ValueError(f"missing production definitions {required-checked}")
    print(f"{target}: matched {len(checked)} native FORS signing declarations",flush=True)


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as folder:
        for target in facade["TARGETS"][:2]:
            check(target, Path(folder) / target)
    module = "Armwide.ForsTree.Sign"
    facade["run"](["lake","build",module],lean)
    facade["audit_theorems"](module,["slhdsa.ArmForsTree.Entry."+name for name in
                                      ("fors_batch_spec","fors_node_spec","fors_sign_spec")])
