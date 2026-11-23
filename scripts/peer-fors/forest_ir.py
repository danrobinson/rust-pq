"""Symbolic execution of the monomorphic peer FORS algorithm at its hash-call boundaries."""

from pathlib import Path
import runpy
import re

core = runpy.run_path(str(Path(__file__).with_name("origins.py")))
logic = runpy.run_path(str(Path(__file__).with_name("symbolic.py")))
Machine, REG, TOKEN, size_of, parts = (
    core[n] for n in ("Machine", "REG", "TOKEN", "size_of", "parts")
)
BDD, Bits = logic["BDD"], logic["Bits"]


class Forest(Machine):
    def __init__(self, ir, n, a, k):
        super().__init__(ir)
        self.bdd = BDD()
        self.n, self.a, self.k = n, a, k
        self.md = [self.bdd.newword(8) for _ in range((a * k + 7) // 8)]
        self.state = [self.bdd.newword(8) for _ in range(n)]
        self.seed = [self.bdd.newword(8) for _ in range(n)]
        # FORS runs at layer zero. Keep the full tree number, key-pair,
        # incoming height and incoming index symbolic.
        self.addr = (
            [0] * 4
            + [self.bdd.newword(8) for _ in range(12)]
            + [0, 0, 0, 3]
            + [self.bdd.newword(8) for _ in range(12)]
        )
        self.output = []
        self.calls = 0
        self.path = 1

    def same_receiver(self, state):
        return self.read(state, self.n) == self.state

    def read(self, p, n, align=1):
        block, sl = self.region(p, n, align)
        values = block[sl]
        if None in values:
            raise ValueError("uninitialized read")
        return values

    def extended_instruction(self, ins, val, final_arg):
        if m := re.fullmatch(r"load (.*?), ptr (" + REG + r"), align (\d+)", ins):
            data = self.read(val(m[2]), size_of(m[1]), int(m[3]))
            if any(isinstance(v, Bits) for v in data):
                return True, self.bdd.narrow(
                    Bits(b for v in data for b in self.bdd.word(v, 8).bits)
                )
        if m := re.fullmatch(
            r"store (.*?) (" + TOKEN + r"), ptr (" + REG + r"), align (\d+)", ins
        ):
            value = val(m[2])
            if isinstance(value, Bits):
                width = size_of(m[1])
                if len(value) != 8 * width:
                    raise ValueError("store width")
                dest, sl = self.region(val(m[3]), width, int(m[4]), write=True)
                dest[sl] = [
                    self.bdd.narrow(Bits(value.bits[8 * i : 8 * i + 8]))
                    for i in range(width)
                ]
                return True, None
        if m := re.fullmatch(
            r"(add|sub|mul|and|or|xor|shl|lshr) ((?:(?:nuw|nsw|disjoint|exact) )*)i(\d+) ("
            + TOKEN
            + r"), ("
            + TOKEN
            + r")",
            ins,
        ):
            a, b = val(m[4]), val(m[5])
            if isinstance(a, Bits) or isinstance(b, Bits):
                return True, self.bdd.alu(m[1], int(m[3]), m[2], a, b)
        if m := re.fullmatch(
            r"zext <(\d+) x i(\d+)> (" + TOKEN + r") to <(\d+) x i(\d+)>", ins
        ):
            lanes, w, v, out_lanes, wide = (
                int(m[1]),
                int(m[2]),
                val(m[3]),
                int(m[4]),
                int(m[5]),
            )
            if out_lanes != lanes or wide < w:
                raise ValueError("vector widening shape")
            bits = self.bdd.word(v, lanes * w).bits
            data = Bits(
                bit
                for i in range(lanes)
                for bit in bits[w * i : w * i + w] + (0,) * (wide - w)
            )
            return True, self.bdd.narrow(data)
        if m := re.fullmatch(
            r"(trunc|zext) ((?:(?:nuw|nsw|nneg) )*)i(\d+) (" + TOKEN + r") to i(\d+)",
            ins,
        ):
            x = val(m[4])
            w = int(m[5])
            if isinstance(x, Bits):
                if len(x) != int(m[3]):
                    raise ValueError("cast width")
                if "nuw" in m[2] and any(x.bits[w:]):
                    raise ValueError("truncation overflow")
                if "nsw" in m[2] and any(b != x.bits[w - 1] for b in x.bits[w:]):
                    raise ValueError("signed truncation")
                if "nneg" in m[2] and x.bits[-1]:
                    raise ValueError("negative nneg operand")
                return True, self.bdd.narrow(Bits((x.bits + (0,) * w)[:w]))
        if m := re.fullmatch(
            r"(?:tail )?call .*?@(secret_observe|node_observe)\((.*)\)(?: #[0-9]+)?",
            ins,
        ):
            av = [final_arg(arg) for arg in parts(m[2])]
            self.sign_child(m[1], av)
            return True, None
        if m := re.fullmatch(
            r"icmp (?:samesign )?(eq|ne) i(\d+) (" + TOKEN + r"), (" + TOKEN + r")", ins
        ):
            x, y = val(m[3]), val(m[4])
            if isinstance(x, Bits) or isinstance(y, Bits):
                width = int(m[2])
                a = self.bdd.word(x, width).bits
                b = self.bdd.word(y, width).bits
                if "samesign" in ins and a[-1] != b[-1]:
                    raise ValueError("unproved equal signs")
                diff = 0
                for u, v in zip(a, b):
                    diff = self.bdd.op("or", diff, self.bdd.op("xor", u, v))
                return True, self.bdd.narrow(
                    Bits([self.bdd.op("xor", int(m[1] == "eq"), diff)])
                )
        if m := re.fullmatch(
            r"(?:tail )?call .*?@llvm.bswap.i(\d+)\((.*)\)(?: #[0-9]+)?", ins
        ):
            width = int(m[1])
            bits = self.bdd.word(final_arg(m[2]), width).bits
            return True, self.bdd.narrow(
                Bits(z for i in reversed(range(0, width, 8)) for z in bits[i : i + 8])
            )
        if m := re.fullmatch(
            r"(?:tail )?call .*?@(f_observe|h_observe|t_observe)\((.*)\)(?: #[0-9]+)?",
            ins,
        ):
            self.recover_child(m[1], [final_arg(a) for a in parts(m[2])])
            return True, None
        return False, None

    def leaf(self, t):
        digit = [
            self.md[(t * self.a + q) // 8].bits[7 - (t * self.a + q) % 8]
            for q in range(self.a)
        ]
        return Bits(tuple(reversed(digit)) + self.bdd.word(t, 32 - self.a).bits)

    def sign_child(self, name, args):
        dst, state, seed, addr, index, *heights = args
        if (
            not self.same_receiver(state)
            or self.read(seed, self.n) != self.seed
            or self.read(addr, 32) != self.addr
        ):
            raise ValueError("wrong FORS signing state, seed or address")
        tree, ordinal = divmod(self.calls, 1 + self.a)
        if tree >= self.k:
            raise ValueError("extra FORS signature hash")
        expected = self.leaf(tree)
        if ordinal == 0:
            if name != "secret_observe" or heights:
                raise ValueError("expected a secret call")
        else:
            height = ordinal - 1
            if name != "node_observe" or heights != [height]:
                raise ValueError("wrong sibling height")
            expected = self.bdd.alu(
                "xor", 32, "", self.bdd.alu("lshr", 32, "", expected, height), 1
            )
        if self.bdd.word(index, 32) != self.bdd.word(expected, 32):
            raise ValueError("incorrect FORS signing index")
        result = [self.bdd.newword(8) for _ in range(self.n)]
        storage, sl = self.region(dst, self.n, write=True)
        storage[sl] = result
        self.output += result
        self.calls += 1

    def sign(self, name):
        ps = [self.allocate(x, 1) for x in [self.md, self.state, self.seed, self.addr]]
        self.readonly.update(p.block for p in ps)
        out = self.allocate([None] * (self.n * self.k * (self.a + 1)), 1)
        self.execute(name, [*ps, out])
        if self.calls != self.k * (self.a + 1) or self.blocks[out.block] != self.output:
            raise ValueError("wrong FORS signature output")
        return self.steps

    def symbolic_diamond(self, condition, yes, no, blocks, registers, local_objects):
        """Prove both arms converge to the same state before continuing once."""
        if not isinstance(condition, Bits) or len(condition) != 1:
            raise ValueError("nonboolean branch")
        final = []
        for side in [yes, no]:
            m = re.fullmatch(r"br label %([-\w.$]+)", blocks[side][-1])
            if not m or any(
                x.startswith(("br ", "ret ", "switch ")) or " phi " in x
                for x in blocks[side][:-1]
            ):
                raise ValueError(f"unmodeled symbolic CFG at {side}")
            final.append(m[1])
        if final[0] != final[1]:
            raise ValueError("branch does not form a diamond")
        destination = final[0]
        original = [b.copy() for b in self.blocks]
        dead = self.dead.copy()
        calls = self.calls
        path = self.path
        outcomes = []
        for i, side in enumerate([yes, no]):
            self.blocks = [b.copy() for b in original]
            self.dead = dead.copy()
            self.calls = calls
            self.path = self.bdd.op(
                "and", path, self.bdd.op("xor", condition.bits[0], i)
            )
            if not self.path:
                raise ValueError("unexpected infeasible diamond")
            regs = {}
            if "__checked_diamond" in self.functions:
                raise ValueError("reserved name collision")
            self.functions["__checked_diamond"] = (
                list(registers),
                {side: blocks[side][:-1] + ["ret void"]},
            )
            self.execute(
                "__checked_diamond", list(registers.values()), local_objects, regs
            )
            del self.functions["__checked_diamond"]
            if len(self.blocks) != len(original):
                raise ValueError("unmodeled allocation in symbolic diamond")
            outcomes.append((self.blocks, self.dead, self.calls, regs))
        self.path = path
        left, right = outcomes
        if left[1] != right[1] or left[2] != right[2] or len(left[0]) != len(right[0]):
            raise ValueError(f"FORS branch effects differ at {yes}, {no}")
        for idx, (a, b) in enumerate(zip(left[0], right[0])):
            if idx not in left[1] and a != b:
                raise ValueError(f"live branch memory differs at {yes} block {idx}")
        for ins in blocks[destination]:
            if " = phi " not in ins:
                break
            phis = dict(
                (pred, v)
                for v, pred in re.findall(rf"\[ ({TOKEN}), %([-\w.$]+) \]", ins)
            )

            def value(side, regs):
                x = phis[side]
                return regs[x] if x.startswith("%") else int(x)

            if value(yes, left[3]) != value(no, right[3]):
                raise ValueError("FORS branch PHIs differ")
        return yes, destination, left[3]

    def bytes_be(self, x, width):
        word = self.bdd.word(x, width).bits
        return [
            self.bdd.narrow(Bits(word[i : i + 8])) for i in reversed(range(0, width, 8))
        ]

    def recover_child(self, name, args):
        dst, state, addr, *values = args
        if not self.same_receiver(state):
            raise ValueError("FORS recovery state")
        tree, level = divmod(self.calls, 1 + self.a)
        if name == "t_observe":
            if (
                self.calls != self.k * (1 + self.a)
                or len(values) != 2
                or values[1] != self.k
            ):
                raise ValueError("FORS roots call")
            expected = self.addr[:16] + [0, 0, 0, 4] + self.addr[20:24] + [0] * 8
            roots = [
                byte
                for t in range(self.k)
                for byte in self.hashes[(t + 1) * (1 + self.a) - 1]
            ]
            if self.read(values[0], self.k * self.n) != roots:
                raise ValueError("FORS root order")
        else:
            if tree >= self.k:
                raise ValueError("too many FORS path calls")
            leaf = self.leaf(tree)
            index = self.bdd.alu("lshr", 32, "", leaf, level) if level else leaf
            expected = (
                self.addr[:24]
                + list(level.to_bytes(4, "big"))
                + self.bytes_be(index, 32)
            )
            start = tree * (1 + self.a) * self.n
            if level == 0:
                if (
                    name != "f_observe"
                    or len(values) != 1
                    or self.read(values[0], self.n) != self.sig[start : start + self.n]
                ):
                    raise ValueError("FORS leaf input")
            else:
                if name != "h_observe" or len(values) != 2:
                    raise ValueError("FORS parent call")
                parity = leaf.bits[level - 1]
                if self.bdd.op("and", self.path, parity) == 0:
                    even = True
                elif self.bdd.op("and", self.path, self.bdd.op("xor", parity, 1)) == 0:
                    even = False
                else:
                    raise ValueError("unresolved left/right parity at hash")
                node, auth = values if even else list(reversed(values))
                source = start + level * self.n
                if (
                    self.read(node, self.n) != self.hashes[self.calls - 1]
                    or self.read(auth, self.n) != self.sig[source : source + self.n]
                ):
                    raise ValueError("FORS node or ordered authentication sibling")
        if self.read(addr, 32) != expected:
            raise ValueError(
                f"FORS address at tree {tree}, level {level}; mismatches {[(i,x if type(x)==int else None) for i,(x,y) in enumerate(zip(self.read(addr,32),expected)) if x!=y]}"
            )
        dest, sl = self.region(dst, self.n, write=True)
        dest[sl] = self.hashes[self.calls]
        self.calls += 1

    def recover(self, name):
        self.sig = [self.bdd.newword(8) for _ in range(self.k * (1 + self.a) * self.n)]
        self.hashes = [
            [self.bdd.newword(8) for _ in range(self.n)]
            for _ in range(self.k * (1 + self.a) + 1)
        ]
        ps = [self.allocate(x, 1) for x in [self.md, self.state, self.addr, self.sig]]
        self.readonly.update(p.block for p in ps)
        out = self.allocate([None] * self.n, 1)
        self.execute(name, [*ps, out])
        if self.calls != len(self.hashes) or self.blocks[out.block] != self.hashes[-1]:
            raise ValueError("FORS recovery output")
        return self.steps
