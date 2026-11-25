#!/usr/bin/env python3
"""Source-bind the interleaved two-key and four-key WOTS generator on both hosts."""
from pathlib import Path
import re
import runpy
import tempfile

fused = runpy.run_path(str(Path(__file__).with_name("check-shake-fused-program.py")))
facade, lean = fused["facade"], fused["lean"]
module = lean / "Buffered/SmallWotsProgram.lean"


def program(pkg):
    types = (pkg / "Types.lean").read_text()
    calls = (pkg / "Funs.lean").read_text()
    start = "def\n  shake.batch.wots_leaves_small.closure_1.Insts"
    body = types[types.index("@[reducible]"):types.rindex("end slhdsa")] + "\n" + calls[
        calls.index(start):calls.rindex("end slhdsa")]
    body = re.sub(r"/--[\s\S]*?-/", "", body)
    substitutions = {"shake.batch.wots_leaves_small": "leaves",
                     "shake256.parallel.permute_active": "kernel.active", **fused["names"]}
    for source, target in substitutions.items():
        body = body.replace(source, target)
    return ("import Fused.Forest\nopen Aeneas Aeneas.Std Result ControlFlow Error\n"
            "namespace slhdsa.Buffered.SmallWots\nopen ShakeBatch NativeVerify\n"
            "set_option linter.concreteInstances false\nvariable [kernel : Fused.Kernel]\n"
            "local instance smallLeafMachine : Machine := Fused.machine kernel\n\n" + body.strip()
            + "\n\nend slhdsa.Buffered.SmallWots\n")


def main():
    proof = "Buffered.SmallWots"
    facade["run"](["lake", "build", proof], lean)
    facade["audit_theorems"](proof, ["slhdsa.Buffered.SmallWots." + name for name in (
        "raw_eq", "leaves_spec", "init_keys", "forest", "groups", "finish_keys")])
    with tempfile.TemporaryDirectory() as tmp:
        for target in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu"):
            folder = Path(tmp) / target
            folder.mkdir()
            pkg = facade["extract"]("rust", target, "Exact", folder,
                                    ["crate::shake::batch::wots_leaves_small"], fused["cuts"])
            if program(pkg).split() != module.read_text().split():
                raise ValueError(f"interleaved WOTS source differs on {target}")
    print("Matched both native extractions of the complete two-key and four-key WOTS generator.")


if __name__ == "__main__":
    main()
