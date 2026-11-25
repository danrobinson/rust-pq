#!/usr/bin/env python3
"""Re-extract both AArch64 FORS recovery paths and check the verified loop bodies."""
import re
import runpy
import tempfile
from pathlib import Path

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
root = facade["ROOT"]
program = root / "lean-hw/Armplatform/WideForsProgram.lean"
cuts = (
    "crate::sha256::arm_wide", "crate::sha512::paired", "crate::sha512::compress",
    "crate::hash::thash_pair", "crate::fors::arm::base_2b_stack",
)


def projected(text, loop):
    decls = re.findall(rf"(@\[rust_loop(?:_body)?\]\ndef fors\.arm\.pk_from_sig_loop{loop}(?:\.body)?\b.*?)(?=\n\n)", text, re.S)
    if len(decls) != 2:
        raise ValueError("expected both loop declarations")
    return "\n\n".join(decls)


def check():
    with tempfile.TemporaryDirectory() as temporary:
        for target in facade["TARGETS"][:2]:
            scratch = Path(temporary) / target
            scratch.mkdir()
            package = facade["extract"]("rust", target, "Armfors", scratch,
                                        ["crate::fors::arm::pk_from_sig"], cuts)
            actual = (package / "Funs.lean").read_text()
            for loop in (0, 2, 4, 5):
                if projected(actual, loop) != projected(program.read_text(), loop):
                    raise ValueError(f"{target}: recovery loop {loop} changed")
    facade["run"](["lake", "build", "Armplatform.WideFors"], root / "lean-hw")


if __name__ == "__main__":
    check()
