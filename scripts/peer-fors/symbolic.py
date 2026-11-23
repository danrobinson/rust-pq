"""Reduced ordered BDDs for exact boolean equalities over independent digest bits."""


class Bits:
    def __init__(self, bits):
        self.bits = tuple(bits)

    def __len__(self):
        return len(self.bits)

    def __eq__(self, other):
        return isinstance(other, Bits) and self.bits == other.bits

    def __hash__(self):
        return hash(self.bits)


class BDD:
    def __init__(self):
        self.nodes = [None, None]
        self.last_var = 0
        self.unique = {}
        self.cache = {}

    def node(self, var, low, high):
        if low == high:
            return low
        key = (var, low, high)
        if key not in self.unique:
            self.unique[key] = len(self.nodes)
            self.nodes.append(key)
        return self.unique[key]

    def variable(self):
        self.last_var += 1
        return self.node(self.last_var, 0, 1)

    def op(self, op, a, b):
        if op not in {"or", "and", "xor"}:
            raise ValueError(f"unknown boolean operation {op}")
        if a > b:
            a, b = b, a
        if op == "and":
            if a == 0:
                return 0
            if a == 1 or a == b:
                return b
        if op == "or":
            if a == 0 or a == b:
                return b
            if a == 1:
                return 1
        if op == "xor":
            if a == 0:
                return b
            if a == b:
                return 0
            if b == 1:
                return 1 - a
        key = (op, a, b)
        if key not in self.cache:
            av = self.last_var + 1 if a <= 1 else self.nodes[a][0]
            bv = self.last_var + 1 if b <= 1 else self.nodes[b][0]
            v = min(av, bv)
            al, ah = self.nodes[a][1:] if av == v else (a, a)
            bl, bh = self.nodes[b][1:] if bv == v else (b, b)
            self.cache[key] = self.node(v, self.op(op, al, bl), self.op(op, ah, bh))
        return self.cache[key]

    def newword(self, width):
        return Bits(self.variable() for _ in range(width))

    @staticmethod
    def word(x, width):
        if isinstance(x, Bits):
            if len(x) != width:
                raise ValueError(f"bit width {len(x)} differs from {width}")
            return x
        if not isinstance(x, int):
            raise ValueError("unsupported bitvector input")
        return Bits((x >> i) & 1 for i in range(width))

    @staticmethod
    def narrow(bits):
        return (
            sum(b << i for i, b in enumerate(bits.bits))
            if all(b <= 1 for b in bits.bits)
            else bits
        )

    def alu(self, op, width, flags, x, y):
        a = self.word(x, width).bits
        b = self.word(y, width).bits
        if op in ("shl", "lshr"):
            if not isinstance(y, int) or not 0 <= y < width:
                raise ValueError("unproved shift range")
            if op == "shl":
                if "nuw" in flags and y and any(a[-y:]):
                    raise ValueError("shift unsigned overflow")
                if "nsw" in flags and y and any(v != a[-1] for v in a[-1 - y :]):
                    raise ValueError("shift signed overflow")
                out = (0,) * y + a[: width - y]
            else:
                if "exact" in flags and any(a[:y]):
                    raise ValueError("inexact shift")
                out = a[y:] + (0,) * y
        elif op in ("or", "and", "xor"):
            if "disjoint" in flags and any(self.op("and", u, v) for u, v in zip(a, b)):
                raise ValueError("overlap")
            out = tuple(self.op(op, u, v) for u, v in zip(a, b))
        elif op == "add":
            out = []
            carry = 0
            for u, v in zip(a, b):
                mixed = self.op("xor", u, v)
                out.append(self.op("xor", mixed, carry))
                carry = self.op(
                    "or", self.op("and", u, v), self.op("and", mixed, carry)
                )
            if "nuw" in flags and carry:
                raise ValueError("add unsigned overflow")
            if "nsw" in flags:
                same = self.op("xor", 1, self.op("xor", a[-1], b[-1]))
                if self.op("and", same, self.op("xor", a[-1], out[-1])):
                    raise ValueError("add signed overflow")
        else:
            raise ValueError(f"unsupported symbolic opcode {op}")
        return self.narrow(Bits(out))
