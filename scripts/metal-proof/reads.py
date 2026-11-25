"""Slice production MSL to the scalar control/address computations for device reads."""

import re

from effects import Effects, OUT_ARGS, PRIVATE_CALLS, ast, gen, names, parse

BUFFERS = {
    "keys",
    "trees",
    "jobs",
    "layers",
    "leaves",
    "in_sub_roots",
    "chain_tips",
    "fors_roots",
    "pk_fors",
    "xmss_roots",
}
RECORDS = {"keys", "trees", "jobs", "layers"}


class ReadSlice(Effects):
    def __init__(self, shake):
        super().__init__()
        self.shake = shake
        self.seen = set()
        self.loops = []
        self.sites = {}

    def operations(self, node, dest=None, helper=None):
        """Inventory every use, rejecting bare pointers except known helper inputs."""
        if node is None:
            return []
        if isinstance(node, ast.ArrayRef):
            name = gen.visit(node.name)
            if name in BUFFERS:
                self.seen.add(name)
                owner = ""
                if name in {"leaves", "in_sub_roots"}:
                    if dest not in {"node", "left", "right"}:
                        raise ValueError(f"{name}: unknown consumer {dest}")
                    owner = "_" + dest
                args = [self.expr(node.subscript)]
                if name in {"chain_tips", "fors_roots"}:
                    sites = self.sites.setdefault(name, {})
                    args += [str(sites.setdefault(id(node), len(sites))), *self.loops]
                elif name in {"leaves", "in_sub_roots", "pk_fors", "xmss_roots"}:
                    args.append(self.loops[-1])
                return [f"check_{name}{owner}({', '.join(args)});"] + self.operations(
                    node.subscript
                )
            if isinstance(node.name, ast.StructRef):
                field = node.name.field.name
                who = gen.visit(node.name.name)
                if who in {"km", "job"} or who.startswith("keys["):
                    if field not in {
                        "state256",
                        "state512",
                        "sk_seed",
                        "pk_seed",
                        "indices",
                    }:
                        raise ValueError("unsupported device record field " + field)
                    self.seen.add(field)
                    expected = "" if field == "indices" else ", " + self.loops[-1]
                    return (
                        self.operations(node.name.name, helper="field")
                        + [f"check_{field}({self.expr(node.subscript)}{expected});"]
                        + self.operations(node.subscript)
                    )
        if isinstance(node, ast.StructRef):
            if helper == "init" and node.field.name != (
                "pk_seed" if self.shake else "state512"
            ):
                raise ValueError("wrong sponge seed field")
            if (
                node.field.name
                in {"pk_seed", "state512", "indices", "sk_seed", "state256"}
                and helper != "init"
            ):
                raise ValueError(
                    "unreviewed device array passed by address " + gen.visit(node)
                )
            return self.operations(node.name, helper="field")
        if isinstance(node, ast.ID):
            if node.name in BUFFERS or (
                node.name in {"km", "job"}
                and helper not in {"field", "thash_pair_words", "shake_thash_pair"}
            ):
                raise ValueError("unreviewed input pointer use " + node.name)
            return []
        if isinstance(node, ast.FuncCall):
            fn = (
                node.name.field.name
                if isinstance(node.name, ast.StructRef)
                else node.name.name
            )
            known = PRIVATE_CALLS | {
                "wots_digit_at",
                "shake_wots_digit_at",
                "bswap32",
                "threadgroup_barrier",
                "write_node_bytes",
                "write_shake_node_bytes",
                "write_node_bytes_tg",
                "write_shake_node_bytes_tg",
            }
            if fn not in known:
                raise ValueError("unreviewed call in device read slice " + fn)
            ops = []
            for i, arg in enumerate(node.args.exprs if node.args else []):
                ops.extend(self.operations(arg, helper=fn if i == 0 else None))
            return ops
        return [
            op
            for _, child in node.children()
            for op in self.operations(child, dest=dest)
        ]

    def emit(self, node):
        if isinstance(node, (ast.Compound, ast.Return)):
            return super().emit(node)
        if isinstance(node, ast.If):
            pre = self.operations(node.cond)
            return "\n".join(pre + [super().emit(node)])
        if isinstance(node, ast.For):
            self.loops.append(node.init.decls[0].name)
            loop = self.emit(node.stmt)
            self.loops.pop()
            if not loop:
                return ""
            init = node.init.decls[0]
            var = init.name
            if (
                len(node.init.decls) != 1
                or gen.visit(init.init) not in {"0", "2u"}
                or gen.visit(node.next) != "++" + var
                or not isinstance(node.cond, ast.BinaryOp)
                or node.cond.op not in ("<", "<=")
                or gen.visit(node.cond.left) != var
                or self.operations(node.cond)
                or self.operations(init.init)
            ):
                raise ValueError("unreviewed loop control " + gen.visit(node.init))
            # A witness at any iteration suffices for read safety. A live value
            # carried across iterations would invalidate this reduction.
            locals_ = set()
            writes = set()

            def visit(st):
                if isinstance(st, ast.Decl):
                    locals_.add(st.name)
                if isinstance(st, ast.Assignment):
                    left = st.lvalue
                    while isinstance(left, (ast.ArrayRef, ast.StructRef)):
                        left = left.name
                    writes.update(names(left))
                for _, child in st.children():
                    visit(child)

            visit(node.stmt)
            if (writes - locals_) & self.live:
                raise ValueError(
                    "loop-carried read dependency: "
                    + str((writes - locals_) & self.live)
                )
            return (
                f"{{uint {var}=arbitrary(); if ({var} >= {gen.visit(init.init)} && "
                f"{self.expr(node.cond)}) {{ {loop} }} }}"
            )
        if isinstance(node, ast.Decl):
            if isinstance(node.type, ast.PtrDecl):
                raise ValueError("unreviewed pointer alias")
            ops = self.operations(node.init)
            if node.name in self.live:
                if (
                    isinstance(node.init, ast.ArrayRef)
                    and gen.visit(node.init.name) in RECORDS
                ):
                    buf = gen.visit(node.init.name)
                    ops.append(
                        f"{gen.visit(node.type)} {node.name} = get_{buf}({self.expr(node.init.subscript)});"
                    )
                else:
                    self.expr(node.init)
                    ops.append(gen.visit(node) + ";")
            return "\n".join(ops)
        if isinstance(node, ast.Assignment):
            if names(node.lvalue) & (BUFFERS | {"km", "job", "desc"}):
                raise ValueError("write to input resource")
            dest = (
                gen.visit(node.lvalue.name)
                if isinstance(node.lvalue, ast.ArrayRef)
                else None
            )
            ops = self.operations(node.rvalue, dest=dest) + self.operations(node.lvalue)
            if isinstance(node.lvalue, ast.ID) and node.lvalue.name in self.live:
                ops.append(self.expr(node) + ";")
            return "\n".join(ops)
        if isinstance(node, ast.FuncCall):
            ops = self.operations(node)
            fn = (
                node.name.field.name
                if isinstance(node.name, ast.StructRef)
                else node.name.name
            )
            allowed = PRIVATE_CALLS | {
                "threadgroup_barrier",
                "write_node_bytes",
                "write_shake_node_bytes",
                "write_node_bytes_tg",
                "write_shake_node_bytes_tg",
            }
            if fn not in allowed:
                raise ValueError("unreviewed helper " + fn)
            args = node.args.exprs if node.args else []
            if any(names(args[i]) & self.live for i in OUT_ARGS.get(fn, ())):
                raise ValueError("helper changes read address")
            return "\n".join(ops)
        raise ValueError("unreviewed read statement " + type(node).__name__)


def projection(source, name):
    parsed = parse(source, name)
    s = ReadSlice(name.startswith("shake_"))
    while True:
        old = s.live.copy()
        ir = s.emit(parsed)
        if s.live == old:
            break
    start = source.index("inline void " + name + "(")
    signature = source[start : source.index("{", start)]
    expected = set(re.findall(r"const device \w+\s*\*(\w+)", signature))
    if (s.seen & BUFFERS) != expected:
        raise ValueError(
            "missing read-only buffer: " + str(expected ^ (s.seen & BUFFERS))
        )
    return ir


def key_helpers(source, shake):
    """Extract each device-key field read in thash_pair and sponge initialization.
    Reject raw pointer uses elsewhere; private hash arithmetic is irrelevant here."""
    pair = "shake_thash_pair" if shake else "thash_pair_words"
    seed = "pk_seed" if shake else "seed_st"
    header = f"void init(const device uint64_t {seed}[{4 if shake else 8}]"
    start = source.index("{", source.index(header))
    end = source.index("\n    }", start)
    init = parse("inline void key_init() " + source[start:end] + "\n}", "key_init")

    def emit(st, pointer, loops):
        if pointer not in names(st):
            return ""
        if isinstance(st, ast.Compound):
            return (
                "{"
                + "".join(emit(child, pointer, loops) for child in st.block_items or [])
                + "}"
            )
        if isinstance(st, ast.If):
            # Pair chooses each path using only its compile-time digest width.
            if names(st.cond) - {"NW", "NL"}:
                raise ValueError("unexpected helper input dependency")
            return (
                f"if ({gen.visit(st.cond)}) {{"
                + emit(st.iftrue, pointer, loops)
                + "}"
                + (
                    "else {" + emit(st.iffalse, pointer, loops) + "}"
                    if st.iffalse
                    else ""
                )
            )
        if isinstance(st, ast.For):
            var = st.init.decls[0].name
            if (
                len(st.init.decls) != 1
                or gen.visit(st.init.decls[0].init) != "0"
                or gen.visit(st.next) != "++" + var
                or not isinstance(st.cond, ast.BinaryOp)
                or gen.visit(st.cond.left) != var
                or st.cond.op not in {"<", "<="}
                or names(st.cond.right) - {"NW", "NL"}
                or not isinstance(st.stmt, ast.Assignment)
            ):
                raise ValueError("unreviewed device-key copy loop")
            return (
                f"{{uint {var}=arbitrary();if({gen.visit(st.cond)}){{"
                + emit(st.stmt, pointer, [var])
                + "}}"
            )
        if (
            isinstance(st, ast.Assignment)
            and st.op == "="
            and pointer not in names(st.lvalue)
            and isinstance(st.rvalue, ast.ArrayRef)
        ):
            a = st.rvalue
            member = gen.visit(a.name)
            allowed = (
                {"km.pk_seed": "pk_seed", "pk_seed": "pk_seed"}
                if shake
                else {
                    "km.state256": "state256",
                    "km.state512": "state512",
                    "seed_st": "state512",
                }
            )
            if member in allowed and len(loops) == 1:
                return f"check_helper_{allowed[member]}({gen.visit(a.subscript)},{loops[0]});"
        raise ValueError("unexpected device key pointer use: " + gen.visit(st))

    return [emit(parse(source, pair), "km", []), emit(init, seed, [])]
