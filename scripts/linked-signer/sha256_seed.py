"""Word-level certificate for the inlined Arm SHA-256 prefix using the kcompress register model."""

import re
from pathlib import Path
import claripy as c


def vector(words):
    return c.Concat(*reversed(words))


def add4(x, y):
    return vector([x[32 * i + 31 : 32 * i] + y[32 * i + 31 : 32 * i] for i in range(4)])


class SeedCompression:
    def __init__(self, seed):
        # Treat the four hardware functions as arbitrary, consistent functions of
        # their operands. Equality of the two circuits then holds for the Arm model.
        self.applications = {}
        source = (
            Path(__file__).resolve().parents[2] / "lean/Spec/Sha256.lean"
        ).read_text()

        def constants(name):
            table = source.split(f"def {name} : List Word := [", 1)[1].split("]", 1)[0]
            return [c.BVV(int(x, 16), 32) for x in re.findall(r"0x(\w+)#32", table)]

        k, initial = constants("K"), constants("H0")
        ab, ef = vector(initial[:4]), vector(initial[4:])
        msg = [vector([seed.get_bytes(i * 4, 4) for i in range(4)])] + [
            c.BVV(0, 128)
        ] * 3
        # Slhdsa.Proofs.Hw.Model.kstep uses the previous pair in both update instructions.
        for i in range(16):
            j = i % 4
            wk = add4(msg[j], vector(k[i * 4 : i * 4 + 4]))
            ab, ef = self.op("H", ab, ef, wk), self.op("H2", ef, ab, wk)
            if i < 12:
                su = self.op("SU0", msg[j], msg[(j + 1) % 4])
                msg[j] = self.op("SU1", su, msg[(j + 2) % 4], msg[(j + 3) % 4])
        self.final_ring = tuple(msg)
        self.seed = c.Concat(
            c.BVV(0, 512),
            add4(vector(initial[:4]), ab).reversed,
            add4(vector(initial[4:]), ef).reversed,
            seed,
        )

    def op(self, opcode, *args):
        key = (opcode, *(c.simplify(arg) for arg in args))
        if key not in self.applications:
            self.applications[key] = c.BVS("sha256_" + opcode, 128)
        return self.applications[key]

    def install(self, project, pc, words):
        for i, word in enumerate(words):
            if word & 0xFFFFFC00 == 0x6E200800:  # REV32 Vd.16B,Vn.16B

                def reverse(s, w=word):
                    src = getattr(s.regs, f"q{(w >> 5) & 31}")
                    setattr(
                        s.regs,
                        f"q{w & 31}",
                        vector([src[i * 32 + 31 : i * 32].reversed for i in range(4)]),
                    )

                project.hook(pc + 4 * i, reverse, length=4)
                continue
            if word & 0xFFFFFC00 == 0x5E282800:
                op = "SU0"
            else:
                op = {0x5E004000: "H", 0x5E005000: "H2", 0x5E006000: "SU1"}.get(
                    word & 0xFFE0FC00
                )
            if op:

                def step(s, w=word, op=op):
                    regs = [
                        getattr(s.regs, f"q{r}")
                        for r in [w & 31, (w >> 5) & 31, (w >> 16) & 31]
                    ]
                    setattr(
                        s.regs,
                        f"q{w & 31}",
                        self.op(op, *regs[: 2 if op == "SU0" else 3]),
                    )

                project.hook(pc + 4 * i, step, length=4)
