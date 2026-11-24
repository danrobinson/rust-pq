#!/usr/bin/env python3
"""Lift the MSL Keccak round into Lean bitvectors using the shader's C++ operations."""

import os
import re
import runpy
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

MODEL = r"""
#include <iostream>
#include <string>
#include <stdexcept>
struct Word {
    std::string term;
    Word operator^(Word b) const { return {"(" + term + " ^^^ " + b.term + ")"}; }
    Word operator&(Word b) const { return {"(" + term + " &&& " + b.term + ")"}; }
    Word operator|(Word b) const { return {"(" + term + " ||| " + b.term + ")"}; }
    Word operator~() const { return {"(~~~" + term + ")"}; }
    Word& operator^=(Word b) { return *this = *this ^ b; }
    Word shift(const char* op, unsigned long n) const {
        if (n >= 64) throw std::out_of_range("MSL shift count");
        return {"(" + term + op + "(" + std::to_string(n) + " : Nat))"};
    }
    Word operator<<(unsigned long n) const { return shift(" <<< ", n); }
    Word operator>>(unsigned long n) const { return shift(" >>> ", n); }
};
"""


def main():
    shader = (ROOT / "metal/shaders/slhdsa_shake.metal").read_text()
    rotation = re.search(
        r"inline uint64_t rotl64\(uint64_t x, uint64_t n\) \{[^}]+\}", shader
    )[0]
    rotation = rotation.replace("uint64_t n", "unsigned long n").replace(
        "uint64_t", "Word"
    )
    start = shader.index("#define KECCAK_PI_RHO")
    end = shader.index("\n}", shader.index("inline void keccak_f1600", start)) + 2
    original = shader[start:end]
    loop = r"inline void keccak_f1600\(thread uint64_t a\[25\]\) \{\s*for \(uint round = 0u; round < 24u; \+\+round\) \{(.*)\}\s*\}"
    match = re.fullmatch(
        loop, original[original.index("inline void keccak_f1600") :], re.S
    )
    if not match or match[1].count("KECCAK_RC[round]") != 1:
        raise ValueError("review the Metal round schedule")
    macros = original[: original.index("inline void keccak_f1600")]
    body = match[1].replace("KECCAK_RC[round]", "constant")
    round_fn = (
        macros + "void run(Word (&a)[25], Word constant) {" + body + "}"
    ).replace("uint64_t", "Word")
    driver = r"""
int main() {
    Word a[25];
    for(int i=0; i<25; ++i) a[i] = {"a[" + std::to_string(i) + "]!"};
    run(a, {"c"});
    for(const auto& w : a) std::cout << w.term << '\n';
}
"""
    constants = re.search(r"constant uint64_t KECCAK_RC\[24\] = \{([^}]+)\};", shader)[
        1
    ]
    rc = [
        re.fullmatch(r"(0x[0-9a-fA-F]+)ul", x.strip())[1] for x in constants.split(",")
    ]
    schedule = f"example : rc = #[{','.join(rc)}] := by decide"
    os.environ["PATH"] = (
        str(Path.home() / ".elan/bin") + os.pathsep + os.environ["PATH"]
    )
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        source, exe = folder / "round.cpp", folder / "round"
        source.write_text(MODEL + rotation + "\n" + round_fn + driver)
        subprocess.run(
            [
                "c++",
                "-std=c++17",
                "-fsanitize=undefined,bounds",
                "-fno-sanitize-recover=all",
                source,
                "-o",
                exe,
            ],
            check=True,
        )
        expressions = subprocess.check_output([exe], text=True).splitlines()
        if len(expressions) != 25:
            raise ValueError("missing Metal round outputs")
        runpy.run_path(str(HERE / "check-apple-hybrid.py"))["check_rounds"](
            folder, expressions, schedule
        )


if __name__ == "__main__":
    main()
