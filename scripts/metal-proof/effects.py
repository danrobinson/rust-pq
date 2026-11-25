"""Extract the control flow determining shared reads, writes and barriers.

Only private hash arithmetic and unused local values are discarded. The input
language is the straight-line, if and counted-loop subset in the MSL kernels.
Unexpected uses of memory resources or control transfers fail the extraction.
"""

import re

from pycparser import c_ast as ast, c_generator, c_parser

gen = c_generator.CGenerator()
TYPES = "uint uint8_t uint32_t uint64_t bool XmssTreeDesc ForsJobDesc WotsSignLayerDesc KeyMaterial ShakeKeyMaterial TlenStream256 TlenStream512 ShakeSponge".split()
OUTPUTS = {
    "out_roots",
    "out_sub_roots",
    "out_fors_roots",
    "out_chain_tips",
    "out_leaves",
    "out_pk_fors",
    "out_sigs",
    "tg_nodes",
}
PRIVATE_CALLS = {
    "adrs_to_w256",
    "adrs_full_lanes",
    "thash_short_words",
    "shake_thash_short",
    "thash_pair_words",
    "shake_thash_pair",
    "run_wots_chain",
    "shake_run_wots_chain",
    "init",
    "finish",
    "push_word",
    "push_word64",
    "absorb_lane",
}


PURE = {"bswap32", "bswap64", "wots_digit_at", "shake_wots_digit_at"}
COPY = {
    "write_node_bytes",
    "write_shake_node_bytes",
    "write_node_bytes_tg",
    "write_shake_node_bytes_tg",
}


def names(node):
    if node is None:
        return set()
    if isinstance(node, ast.ID):
        return {node.name}
    if isinstance(node, ast.StructRef):
        return names(node.name)
    return set().union(*(names(child) for _, child in node.children()))


def body(source, name):
    start = source.index("inline void " + name + "(")
    start = source.index("{", start)
    return source[start : source.index("\n}", start) + 2]


def parse(source, name):
    src = re.sub(r"//[^\n]*|/\*.*?\*/", "", body(source, name), flags=re.S)
    src = re.sub(r"(\w+)<(?:NW|NL)>\(", r"\1(", src)
    src = re.sub(
        r"\b(?:uint64_t|uint32_t|uint8_t)\(", lambda m: "(" + m[0][:-1] + ")(", src
    )
    src = re.sub(r"const device (\w+) &(\w+) =", r"\1 \2 =", src)
    src = src.replace("mem_flags::mem_threadgroup", "mem_threadgroup")
    # Device input references above become immutable descriptor snapshots. The
    # remaining private variables are values or fixed-size arrays. Refuse
    # address-taking, hidden pointer declarators and indirect control flow.
    decls = "".join(f"typedef unsigned {t};\n" for t in TYPES)
    parsed = c_parser.CParser().parse(decls + "void run()" + src).ext[-1].body

    if not name.endswith("_impl"):
        return parsed

    signature = source.split("inline void " + name + "(", 1)[1].split(") {", 1)[0]
    for argument in signature.split(","):
        if "device " in argument or "threadgroup " in argument:
            match = re.fullmatch(
                r"\s*(const\s+)?(device|threadgroup)\s+\w+\s*\*\s*(\w+)\s*", argument
            )
            if not match or (match[1] is None) != (match[3] in OUTPUTS):
                raise ValueError("unrecognized memory resource: " + argument)
    class Syntax(ast.NodeVisitor):
        def visit_UnaryOp(self, node):
            if node.op in ("&", "*", "++", "--", "p++", "p--"):
                raise ValueError("indirect memory access or embedded update in shader")
            self.generic_visit(node)

        def visit_For(self, node):
            init = gen.visit(node.init)
            match = re.fullmatch(r"(uint|uint32_t) (\w+) = (0|2u)", init)
            if not match or gen.visit(node.next) != "++" + match[2]:
                raise ValueError("unsupported loop update")
            self.visit(node.cond)
            self.visit(node.stmt)

        def visit_FuncCall(self, node):
            fn = (
                node.name.field.name
                if isinstance(node.name, ast.StructRef)
                else node.name.name
            )
            if fn not in PRIVATE_CALLS | PURE | COPY | {"threadgroup_barrier"}:
                raise ValueError("unsupported shader helper: " + fn)
            self.generic_visit(node)

        def visit_Compound(self, node):
            for stmt in node.block_items or []:
                # Side effects may only be top-level statements. This makes
                # dropping unused private expressions sound for this subset.
                for child in expressions(stmt):
                    ImpureExpression().visit(child)
                self.visit(stmt)

    class ImpureExpression(ast.NodeVisitor):
        def visit_Assignment(self, node):
            raise ValueError("embedded shader assignment")

        def visit_FuncCall(self, node):
            if not isinstance(node.name, ast.ID) or node.name.name not in PURE:
                raise ValueError("impure or unknown shader expression")
            self.generic_visit(node)

    def expressions(stmt):
        if isinstance(stmt, ast.Decl):
            return [stmt.init] if stmt.init else []
        if isinstance(stmt, ast.Assignment):
            return [stmt.lvalue, stmt.rvalue]
        if isinstance(stmt, ast.If):
            return [stmt.cond]
        if isinstance(stmt, ast.For):
            return [stmt.cond]
        if isinstance(stmt, ast.FuncCall):
            return [stmt.args] if stmt.args else []
        return []

    Syntax().visit(parsed)
    return parsed


def helper_contract(source, family):
    width, word = ("NL", 8) if family else ("NW", 4)
    store = "store_le64" if family else "store_be32"
    compact = lambda text: re.sub(r"\s+", "", text)
    # Derive mutable output argument positions from the shader declarations.
    for fn in PRIVATE_CALLS | PURE:
        for signature in re.findall(
            r"\b(?:void|uint32_t|uint64_t)\s+" + fn + r"\s*\(([^)]*)\)\s*\{", source
        ):
            args = signature.split(",")
            mutable = {
                i
                for i, arg in enumerate(args)
                if "const" not in arg and any(c in arg for c in "*&[")
            }
            if mutable != {i % len(args) for i in OUT_ARGS.get(fn, ())}:
                raise ValueError("private helper signature changed: " + fn)
    for suffix in ("", "_tg"):
        src = compact(body(source, "write_" + family + "node_bytes" + suffix))
        if (
            src
            != "{for(uinti=0;i<"
            + width
            + ";++i){"
            + store
            + "(dst+"
            + str(word)
            + "u*i,node[i]);}}"
        ):
            raise ValueError("unsupported node byte store or scratch read")
    stores = compact(body(source, store))[1:-1]
    if [
        int(i) for i in re.findall(r"dst\[(\d+)\]=uint8_t\(v(?:>>\d+)?\);", stores)
    ] != list(range(word)) or len(stores.split(";")) != word + 1:
        raise ValueError("unsupported output byte footprint")


# Output/reference arguments of the private cryptographic helpers. Everything
# else is read-only or passed by value. None may mutate a live index/condition.
OUT_ARGS = {
    "adrs_to_w256": tuple(range(6, 12)),
    "adrs_full_lanes": (6, 7, 8, 9),
    "thash_short_words": (-1,),
    "shake_thash_short": (-1,),
    "thash_pair_words": (-1,),
    "shake_thash_pair": (-1,),
    "run_wots_chain": (-1,),
    "shake_run_wots_chain": (-1,),
    "finish": (-1,),
}


class Effects:
    def __init__(self):
        self.live = set()
        self.barriers = {}

    def expr(self, node):
        self.live.update(names(node))
        return gen.visit(node)

    def offset(self, node, base):
        # Each production pointer walks forward from the allocation base.
        # Reject integer casts, pointer differences and cancellation through
        # an out-of-allocation intermediate value in the lifted subset.
        cursor = node
        while (
            isinstance(cursor, ast.BinaryOp)
            and cursor.op == "+"
            and not names(cursor.right) & OUTPUTS
        ):
            cursor = cursor.left
        if isinstance(cursor, ast.ID) and cursor.name == base:
            return self.expr(node)
        raise ValueError("unsupported pointer offset: " + gen.visit(node))

    def emit(self, node):
        if isinstance(node, ast.Compound):
            lines = [self.emit(s) for s in node.block_items or []]
            return "{\n" + "\n".join(filter(None, lines)) + "\n}" if any(lines) else ""
        if isinstance(node, ast.If):
            a, b = (
                self.emit(node.iftrue),
                self.emit(node.iffalse) if node.iffalse else "",
            )
            if a or b:
                return f"if ({self.expr(node.cond)}) {{ {a} }}" + (
                    f" else {{ {b} }}" if b else ""
                )
            return ""
        if isinstance(node, ast.For):
            nested = self.emit(node.stmt)
            if not nested:
                return ""
            # Only local bounded induction variables may be discarded with a loop.
            init = gen.visit(node.init)
            if not re.fullmatch(r"(uint|uint32_t) \w+ = (0|2u)", init):
                raise ValueError("unexpected loop initializer " + init)
            return f"for ({init}; {self.expr(node.cond)}; {self.expr(node.next)}) {{ {nested} }}"
        if isinstance(node, ast.Return) and node.expr is None:
            return "return;"
        if isinstance(node, ast.FuncCall):
            fn = (
                node.name.field.name
                if isinstance(node.name, ast.StructRef)
                else node.name.name
            )
            args = node.args.exprs if node.args else []
            if fn == "threadgroup_barrier":
                if gen.visit(node.args) != "mem_threadgroup":
                    raise ValueError("unexpected barrier scope")
                index = self.barriers.setdefault(id(node), len(self.barriers))
                return f"barrier({index});"
            if fn in (
                "write_node_bytes",
                "write_shake_node_bytes",
                "write_node_bytes_tg",
                "write_shake_node_bytes_tg",
            ):
                if len(args) != 2 or names(args[0]) & OUTPUTS != {"out_sigs"}:
                    raise ValueError("unexpected signature destination")
                start = self.offset(args[0], "out_sigs")
                if fn.endswith("_tg"):
                    if names(args[1]) & OUTPUTS != {"tg_nodes"}:
                        raise ValueError("unexpected scratch copy")
                    return f"copy_node({start}, {self.offset(args[1], 'tg_nodes')});"
                if names(args[1]) & OUTPUTS:
                    raise ValueError("shared pointer passed to private node copy")
                return f"sig_write({start});"
            if fn not in PRIVATE_CALLS or names(node) & OUTPUTS:
                raise ValueError("unmodeled shader call " + gen.visit(node))
            outputs = [args[i] for i in OUT_ARGS.get(fn, ())]
            if isinstance(node.name, ast.StructRef):
                outputs.append(node.name.name)
            if any(names(arg) & self.live for arg in outputs):
                raise ValueError(
                    "private helper changes live control or addressing: " + fn
                )
            return ""
        if isinstance(node, ast.Assignment):
            left, right = node.lvalue, node.rvalue
            lnames, rnames = names(left) & OUTPUTS, names(right) & OUTPUTS
            action = ""
            if rnames:
                if (
                    rnames != {"tg_nodes"}
                    or not isinstance(right, ast.ArrayRef)
                    or gen.visit(right.name) != "tg_nodes"
                ):
                    raise ValueError("unmodeled shared read " + gen.visit(node))
                action = f"scratch_read({self.expr(right.subscript)});"
            if lnames:
                if (
                    node.op != "="
                    or not isinstance(left, ast.ArrayRef)
                    or not isinstance(left.name, ast.ID)
                    or left.name.name not in OUTPUTS
                ):
                    raise ValueError("unmodeled shared write " + gen.visit(node))
                op = (
                    "scratch_write"
                    if left.name.name == "tg_nodes"
                    else "write_" + left.name.name
                )
                return action + f"{op}({self.expr(left.subscript)});"
            if isinstance(left, ast.ID) and left.name in self.live:
                if rnames:
                    raise ValueError(
                        "scratch data affects an address or control decision"
                    )
                return self.expr(node) + ";"
            if not isinstance(left, (ast.ArrayRef, ast.ID)) or (
                names(left) & self.live
                and isinstance(left, ast.ArrayRef)
                and names(left.name) & self.live
            ):
                raise ValueError("unmodeled assignment " + gen.visit(node))
            return action
        if isinstance(node, ast.Decl):
            if isinstance(node.type, ast.PtrDecl):
                raise ValueError("unsupported pointer alias in memory-effects lift")
            if names(node.init) & OUTPUTS:
                raise ValueError("unexpected memory alias " + gen.visit(node))
            if node.name in self.live:
                self.expr(node.init)
                return gen.visit(node) + ";"
            return ""
        raise ValueError("unsupported shader statement " + type(node).__name__)


def extract(source, name):
    parsed = parse(source, name)
    effects = Effects()
    while True:
        old = effects.live.copy()
        result = effects.emit(parsed)
        if effects.live == old:
            return result, len(effects.barriers)
