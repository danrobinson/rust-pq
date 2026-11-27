#!/usr/bin/env python3
"""Bind the eight-key WOTS leaf program used by the buffered XMSS subtree."""
from pathlib import Path
import re
import runpy
import sys
import tempfile

fused = runpy.run_path(str(Path(__file__).with_name("check-shake-fused-program.py")))
facade, lean = fused["facade"], fused["lean"]
module = lean / "Buffered/FullProgram.lean"


def program(pkg):
    types = (pkg / "Types.lean").read_text()
    calls = (pkg / "Funs.lean").read_text()
    body = types[types.index("@[reducible]"):types.rindex("end slhdsa")] + "\n" + calls[
        calls.index("def\n  shake.batch.wots_leaves_batch.closure_2.Insts"):calls.rindex("end slhdsa")]
    body = re.sub(r"/--[\s\S]*?-/", "", body)
    for old, new in [("shake.batch.wots_leaves_batch", "leaves"), *fused["names"].items()]:
        body = body.replace(old, new)
    return ("import Fused.Forest\nopen Aeneas Aeneas.Std Result ControlFlow Error\n"
            "namespace slhdsa.Buffered.Full\nopen ShakeBatch NativeVerify\n"
            "set_option linter.concreteInstances false\nvariable [kernel : Fused.Kernel]\n"
            "local instance : Machine := Fused.machine kernel\n\n" + body.strip() + "\n\nend slhdsa.Buffered.Full\n")


def main():
    facade["run"](["lake", "build", "Buffered.Host"], lean)
    facade["audit_theorems"]("Buffered.Host", [
        "slhdsa.Buffered.Full.rounds_spec", "slhdsa.Buffered.Full.forest_spec",
        "slhdsa.Buffered.Full.leaves_spec", "slhdsa.Buffered.Host.apple_eight",
        "slhdsa.Buffered.Host.x86_eight", "slhdsa.Buffered.Host.apple_active", "slhdsa.Buffered.Host.x86_active"])
    with tempfile.TemporaryDirectory() as temp:
        for target in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu"):
            folder = Path(temp) / target
            folder.mkdir()
            pkg = facade["extract"]("rust", target, "Exact", folder, ["crate::shake::batch::wots_leaves_batch"], fused["cuts"])
            if program(pkg).split() != module.read_text().split():
                raise ValueError(f"full eight-key WOTS program differs on {target}")
            source = pkg / "Funs.lean"
            original = source.read_text()
            for before, after in [("params.W - 1#u32", "params.W - 2#u32"),
                                  ("shake.batch.read_active N pk6 i4", "shake.batch.read_active N pk5 i4")]:
                if original.count(before) != 1:
                    raise ValueError(f"mutation no longer identifies one WOTS instruction: {before}")
                source.write_text(original.replace(before, after))
                if program(pkg).split() == module.read_text().split():
                    raise ValueError(f"changed full width WOTS program passed on {target}")
    facade["run"]([sys.executable, Path(__file__).with_name("check-shake-small-wots.py")], lean.parent)
    print("Both Rust targets reproduce the eight-key WOTS program and reject shortened chains and unpermuted outputs.")


if __name__ == "__main__":
    main()
