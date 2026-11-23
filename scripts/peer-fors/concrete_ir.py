"""Concrete HashSuite method identity and recursive calls from the pinned FORS implementation."""

from pathlib import Path
import runpy
import re

forest = runpy.run_path(str(Path(__file__).with_name("forest_ir.py")))
Forest, Bits, parts = (forest[n] for n in ("Forest", "Bits", "parts"))


class ConcreteForest(Forest):
    def __init__(self, ir, n, a, k, suite):
        super().__init__(ir, n, a, k)
        self.provider = (
            "shake"
            if suite.startswith("Shake")
            else ("sha2l1" if n == 16 else "sha2l35")
        )

    def allocate(self, cells, align):
        if cells is self.state:
            self.receiver = super().allocate([], 1)
            return self.receiver
        return super().allocate(cells, align)

    def region(self, p, *args, **kwargs):
        if (
            hasattr(self, "receiver")
            and getattr(p, "block", None) == self.receiver.block
        ):
            raise ValueError(
                "FORS accessed provider state outside a checked provider method"
            )
        return super().region(p, *args, **kwargs)

    def same_receiver(self, state):
        return state == self.receiver

    def extended_instruction(self, ins, val, final_arg):
        vector = re.fullmatch(
            r"insertelement <(\d+) x i(\d+)> (<[^>]*>|%[-\w.$]+), i(\d+) (%[-\w.$]+|-?\d+), i64 (\d+)",
            ins,
        )
        if vector:
            count, width, operand, elem_width, elem, lane = vector.groups()
            count, width, lane = int(count), int(width), int(lane)
            if int(elem_width) != width or lane >= count:
                raise ValueError("vector shape")
            if operand.startswith("<"):
                values = []
                for item in parts(operand[1:-1]):
                    typ, n = item.split()
                    if typ != "i" + str(width):
                        raise ValueError("vector element type")
                    values.append(
                        None if n == "poison" else self.bdd.word(int(n), width).bits
                    )
            else:
                prior = val(operand)
                if not isinstance(prior, tuple) or prior[:2] != ("partial", width):
                    raise ValueError("unexpected partial vector")
                values = list(prior[2])
            if len(values) != count:
                raise ValueError("vector insertion size")
            values[lane] = self.bdd.word(val(elem), width).bits
            if any(v is None for v in values):
                return True, ("partial", width, tuple(values))
            return True, self.bdd.narrow(Bits(bit for x in values for bit in x))
        m = re.fullmatch(
            r"(?:tail )?call .*?@((?:sha2l1|sha2l35|shake)_(?:prf|f|h|t)|node)_observe\((.*)\)(?: #[0-9]+)?",
            ins,
        )
        if m:
            method = m[1]
            if method != "node":
                family, method = method.split("_")
                if family != self.provider:
                    raise ValueError(
                        f"FORS dispatched to {family}, expected {self.provider}"
                    )
            args = [final_arg(a) for a in parts(m[2])]
            if args[1] != self.receiver:
                raise ValueError("provider receiver changed")
            if hasattr(self, "height"):
                self.node_child(method, args)
            elif method == "prf":
                dst, _, seed, addr = args
                tree, slot = divmod(self.calls, self.a + 1)
                if slot != 0 or tree >= self.k:
                    raise ValueError("unexpected signing PRF")
                leaf = self.leaf(tree)
                if self.read(seed, self.n) != self.seed or self.read(
                    addr, 32
                ) != self.secret_addr(leaf):
                    raise ValueError("incorrect concretely bound signing PRF")
                output = [self.bdd.newword(8) for _ in range(self.n)]
                self.write_output(dst, output)
                self.output += output
                self.calls += 1
            else:
                if method == "node":
                    self.sign_child("node_observe", args)
                else:
                    self.recover_child(method + "_observe", args)
            return True, None
        if "_observe(" in ins:
            raise ValueError("unqualified or unknown provider observation")
        return super().extended_instruction(ins, val, final_arg)

    def secret_addr(self, index):
        return (
            self.addr[:16]
            + [0, 0, 0, 6]
            + self.addr[20:24]
            + [0] * 4
            + self.bytes_be(index, 32)
        )

    def write_output(self, dest, bytes_):
        block, span = self.region(dest, len(bytes_), write=True)
        block[span] = bytes_

    def node_child(self, op, args):
        dst, _, *args = args
        if self.height == 0 and self.calls == 0 and op == "prf":
            seed, addr = args
            if self.read(seed, self.n) != self.seed or self.read(
                addr, 32
            ) != self.secret_addr(self.index):
                raise ValueError("wrong FORS leaf secret seed or PRF address")
        elif self.height == 0 and self.calls == 1 and op == "f":
            addr, secret = args
            expected = self.addr[:24] + [0] * 4 + self.bytes_be(self.index, 32)
            if (
                self.read(addr, 32) != expected
                or self.read(secret, self.n) != self.children[0]
            ):
                raise ValueError("wrong FORS leaf address or F payload")
        elif self.height > 0 and self.calls < 2 and op == "node":
            seed, addr, index, z = args
            if self.read(seed, self.n) != self.seed or self.read(addr, 32) != self.addr:
                raise ValueError("recursive call changed the FORS seed or address")
            doubled = self.bdd.alu("shl", 32, "", self.index, 1)
            child = self.bdd.alu("or", 32, "", doubled, self.calls)
            if z != self.height - 1 or self.bdd.word(index, 32) != self.bdd.word(
                child, 32
            ):
                raise ValueError("wrong recursive FORS index or height")
        elif self.height > 0 and self.calls == 2 and op == "h":
            addr, left, right = args
            expected = (
                self.addr[:24]
                + list(self.height.to_bytes(4, "big"))
                + self.bytes_be(self.index, 32)
            )
            if self.read(addr, 32) != expected:
                raise ValueError("wrong FORS parent address")
            if (
                self.read(left, self.n) != self.children[0]
                or self.read(right, self.n) != self.children[1]
            ):
                raise ValueError("wrong FORS parent hash inputs")
        else:
            raise ValueError("wrong sequence of concrete FORS node calls")
        self.write_output(dst, self.children[self.calls])
        self.calls += 1

    def node(self, name, height):
        self.height = height
        # All valid global indices i < K * 2^(A-z) are in this bit width.
        width = (self.k * (1 << (self.a - height)) - 1).bit_length()
        self.index = Bits(self.bdd.newword(width).bits + (0,) * (32 - width))
        self.children = [
            [self.bdd.newword(8) for _ in range(self.n)]
            for _ in range(3 if height else 2)
        ]
        state, seed, addr = [
            self.allocate(x, 1) for x in (self.state, self.seed, self.addr)
        ]
        self.readonly.update(p.block for p in [state, seed, addr])
        out = self.allocate([None] * self.n, 1)
        self.execute(name, [state, seed, addr, self.index, height, out])
        if (
            self.calls != len(self.children)
            or self.blocks[out.block] != self.children[-1]
        ):
            raise ValueError(
                "node return does not come from its specified provider call"
            )
        return self.steps
