# /// script
# requires-python = ">=3.10"
# dependencies = ["pycparser==3.0", "z3-solver==4.15.4.0"]
# ///
"""Prove read footprints of the production MSL against its initialized host slices."""

import operator
from pathlib import Path
import re
import runpy
import sys

from pycparser import c_ast as ast, c_parser
import z3

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "metal-proof"))
from reads import key_helpers, projection

ROOT = HERE.parent
NAMES = (
    "wots_chains",
    "wots_tlen",
    "xmss_leaves_streaming",
    "xmss_reduce",
    "fors_pass1",
    "fors_pass2",
    "fors_pk",
    "wots_sign",
)
M = 2**32
DECLS = "typedef unsigned uint,uint32_t,bool,XmssTreeDesc,ForsJobDesc,WotsSignLayerDesc,KeyMaterial,ShakeKeyMaterial;"


class ReadFailure(Exception):
    pass


class Check:
    def __init__(self, row, kernel, keygen):
        _, family, n, _, d, hp, a, k, _ = row
        self.kernel, self.shake, self.keygen = kernel, family == "shake", keygen
        self.words = w = n // (8 if self.shake else 4)
        self.wots = l = n * 2 + 3
        self.leaves = leaves = 1 << hp
        s1 = a if a <= 8 else 7
        self.subs = subs = 1 << (a - s1)
        self.layers = d
        self.k = k
        self.s = z3.Solver()
        self.s.set(timeout=10000)
        self.checks = 0
        self.count, self.work, self.tid, self.key, self.target, self.nkeys = z3.Ints(
            "count work tid key target keys"
        )
        trees = self.count * (1 if keygen else d)
        sig = n * (1 + k * (1 + a) + d * (hp + l))
        # The replay checks the widest admitted streaming geometry for the
        # reduction: two-phase has an additional guard and a smaller domain.
        limit = (
            (M - 1) // (leaves * w)
            if keygen
            else min((M - 1) // max(sig, d * leaves * w), (M - 1) // (k * subs * w))
        )
        if kernel in ("wots_chains", "wots_tlen"):
            limit = min(limit, (M - 1) // ((1 if keygen else d) * leaves * l * w))
        self.s.add(
            self.count >= 0,
            self.count <= limit,
            self.work >= 0,
            self.work < M,
            self.tid >= 0,
            self.tid
            < {
                "xmss_reduce": leaves // 2,
                "fors_pass1": (1 << s1) // 2,
                "fors_pass2": subs // 2,
            }.get(kernel, 1),
            self.nkeys >= 0,
            self.nkeys <= self.count,
            z3.Implies(self.count > 0, z3.And(self.key >= 0, self.key < self.nkeys)),
            self.target >= 0,
            self.target < leaves,
        )
        self.grid = {
            "wots_chains": trees * leaves * l,
            "wots_tlen": trees * leaves,
            "xmss_leaves_streaming": trees * leaves,
            "xmss_reduce": trees,
            "fors_pass1": self.count * k * subs,
            "fors_pass2": self.count * k,
            "fors_pk": self.count,
            "wots_sign": self.count * d * l,
        }[kernel]
        step = {
            "wots_chains": leaves * l,
            "wots_tlen": leaves,
            "xmss_leaves_streaming": leaves,
            "xmss_reduce": 1,
            "wots_sign": l,
            "fors_pass1": k * subs,
            "fors_pass2": k,
            "fors_pk": 1,
        }[kernel]
        self.record = self.work / step
        p = dict(
            num_trees=trees,
            num_layers=self.count * d,
            d=d,
            num_sigs=self.count,
            k=k,
            a=a,
            hp=hp,
            wots_len=l,
            leaves_per_tree=leaves,
            subtrees_per_tree=subs,
            s1=s1,
            s2=a - s1,
        )
        self.env = dict(
            p=p,
            gid=self.work,
            tg_id=self.work,
            sig_idx=self.work,
            tid=self.tid,
            NW=w,
            NL=w,
        )
        self.expected_key = self.record if keygen else self.key

    def goal(self, cond, label):
        self.s.push()
        self.s.add(z3.Not(cond))
        status = self.s.check()
        if status == z3.sat:
            raise ReadFailure(f"{self.kernel}/{label}: {self.s.model()}")
        if status != z3.unsat:
            raise RuntimeError(
                f"inconclusive {self.kernel}/{label}: {self.s.reason_unknown()}"
            )
        self.s.pop()
        self.checks += 1

    def read(self, name, args):
        pos = args[0]
        w, l = self.words, self.wots
        tree_count = self.count * (1 if self.keygen else self.layers)
        if name.startswith("helper_"):
            extent = w if name == "helper_pk_seed" else 8
            self.goal(
                z3.And(pos == args[1], pos >= 0, pos < extent),
                name + " initialized key field",
            )
            return
        if name in {"trees", "layers", "jobs"}:
            expected = self.record
            extent = self.count if name == "jobs" else tree_count
        elif name == "keys":
            expected = self.expected_key
            extent = self.count if self.keygen else self.nkeys
        elif name == "indices":
            expected = (
                self.work / (self.subs if self.kernel == "fors_pass1" else 1)
            ) % self.k
            extent = self.k
        elif name in {"state256", "state512", "sk_seed", "pk_seed"}:
            expected = args[1]
            extent = 8 if name.startswith("state") else w
        elif name.startswith("leaves_") or name.startswith("in_sub_roots_"):
            if name.startswith("leaves_"):
                size = self.leaves
                extent = tree_count * size * w
            else:
                size = self.subs
                extent = self.count * self.k * size * w
            offset = (
                self.target + z3.If(self.target % 2 == 0, 1, -1)
                if name.endswith("_node")
                else 2 * self.tid + int(name.endswith("_right"))
            )
            expected = (self.work * size + offset) * w + args[1]
        elif name in {"chain_tips", "fors_roots"}:
            width = l if name == "chain_tips" else self.k
            extent = (
                (tree_count * self.leaves if name == "chain_tips" else self.count)
                * width
                * w
            )
            site = int(str(args[1]))
            if self.shake:
                if site != 0 or len(args) != 3:
                    raise ValueError("unsupported SHAKE stream read")
                local = args[2]
            elif len(args) == 3 and 0 <= site < 4:
                local = args[2] * w + site
            elif len(args) == 4 and 4 <= site < 6:
                local = args[2] * w + 2 * args[3] + (site - 4)
            else:
                raise ValueError("unsupported SHA2 stream read")
            expected = self.work * width * w + local
            # A loop bound mistakenly widened into the next item can give the
            # right expression but the wrong owner's word.
            self.goal(z3.And(local >= 0, local < width * w), name + " stream position")
        elif name in {"pk_fors", "xmss_roots"}:
            owner = self.record / self.layers
            if name == "pk_fors":
                self.goal(
                    self.record % self.layers == 0, "FORS root only at bottom layer"
                )
                extent = self.count * w
            else:
                self.goal(
                    self.record % self.layers != 0,
                    "prior layer only above bottom layer",
                )
                owner = self.record - 1
                extent = tree_count * w
            expected = owner * w + args[1]
        else:
            raise ValueError("unreviewed read " + name)
        if name.startswith(("leaves_", "in_sub_roots_")) or name in {
            "pk_fors",
            "xmss_roots",
        }:
            self.goal(z3.And(args[1] >= 0, args[1] < w), name + " word within node")
        self.goal(
            z3.And(self.work < self.grid, pos >= 0, pos < extent, pos == expected),
            name + " intended initialized slice",
        )

    def value(self, node, env):
        if isinstance(node, ast.ID):
            return env[node.name]
        if isinstance(node, ast.Constant):
            return z3.IntVal(int(node.value.rstrip("uUlL"), 0))
        if isinstance(node, ast.StructRef):
            return self.value(node.name, env)[node.field.name]
        if isinstance(node, ast.FuncCall):
            fn = node.name.name
            if fn == "arbitrary":
                x = z3.FreshInt("loop")
                self.s.add(x >= 0, x < M)
                return x
            index = self.value(node.args.exprs[0], env)
            if fn not in {"get_trees", "get_jobs", "get_layers", "get_keys"}:
                raise ValueError("unmodeled call " + fn)
            # The index has its own proof obligation at the actual read. All
            # admissible signing key indices are possible; keygen is one-to-one.
            return dict(
                key_idx=index if self.keygen else self.key,
                layer=index % self.layers,
                sig_idx=index / self.layers,
                target_leaf=M - 1 if self.keygen else self.target,
            )
        if isinstance(node, ast.BinaryOp):
            a, b = self.value(node.left, env), self.value(node.right, env)
            a = z3.IntVal(a) if type(a) is int else a
            b = z3.IntVal(b) if type(b) is int else b
            logic = {
                "<": operator.lt,
                "<=": operator.le,
                ">=": operator.ge,
                "==": operator.eq,
                "!=": operator.ne,
                ">": operator.gt,
                "&&": z3.And,
                "||": z3.Or,
                "/": operator.truediv,
                "%": operator.mod,
            }
            if node.op in logic:
                if node.op in {"/", "%"}:
                    self.goal(b > 0, "defined division")
                return z3.simplify(logic[node.op](a, b))
            arithmetic = {"+": operator.add, "-": operator.sub, "*": operator.mul}
            if node.op in arithmetic:
                # Use exact unsigned 32-bit wrapping at every MSL operation.
                return z3.simplify(arithmetic[node.op](a, b) % M)
            if node.op == "^" and z3.is_int_value(b) and b.as_long() == 1:
                return a + z3.If(a % 2 == 0, 1, -1)
        raise ValueError("unreviewed read-address expression " + str(node))

    def block(self, node, env):
        for stmt in node.block_items or []:
            if isinstance(stmt, ast.Compound):
                self.block(stmt, env.copy())
            elif isinstance(stmt, ast.Decl):
                if not isinstance(
                    stmt.type, ast.TypeDecl
                ) or stmt.type.type.names not in (
                    ["uint"],
                    ["uint32_t"],
                    ["bool"],
                    ["XmssTreeDesc"],
                    ["ForsJobDesc"],
                    ["WotsSignLayerDesc"],
                    ["KeyMaterial"],
                    ["ShakeKeyMaterial"],
                ):
                    raise ValueError("unsupported live address type in " + stmt.name)
                if stmt.name in env:
                    # Kernel FORS indices shadow the unused invocation argument.
                    if stmt.name != "sig_idx":
                        raise ValueError(
                            "unexpected live variable redeclaration " + stmt.name
                        )
                env[stmt.name] = self.value(stmt.init, env)
            elif isinstance(stmt, ast.If):
                cond = self.value(stmt.cond, env)

                def branch(branch_node, condition):
                    if branch_node is None:
                        return
                    self.s.push()
                    self.s.add(condition)
                    if self.s.check() != z3.unsat:
                        self.block(branch_node, env.copy())
                    self.s.pop()

                # Early exit at the production grid guard restricts all later
                # accesses. Other live branches carry no scalar assignments.
                if len(stmt.iftrue.block_items or []) == 1 and isinstance(
                    stmt.iftrue.block_items[0], ast.Return
                ):
                    if stmt.iffalse:
                        raise ValueError("unreviewed early exit")
                    self.s.add(z3.Not(cond))
                else:
                    branch(stmt.iftrue, cond)
                    branch(stmt.iffalse, z3.Not(cond))
            elif isinstance(stmt, ast.FuncCall) and stmt.name.name.startswith("check_"):
                self.read(
                    stmt.name.name[6:], [self.value(v, env) for v in stmt.args.exprs]
                )
            else:
                raise ValueError(
                    "unreviewed control in read slice " + type(stmt).__name__
                )

    def verify(self, program):
        self.block(program, self.env.copy())
        if self.checks == 0:
            raise ValueError("empty read footprint")
        return self.checks


def compile_reads(msl, prefix, name):
    return (
        c_parser.CParser()
        .parse(DECLS + "void run()" + projection(msl, prefix + name + "_impl"))
        .ext[-1]
        .body
    )


def negatives(sources, rows):
    cases = [
        (
            "SHA2 wrong tree",
            "sha2-128f",
            "wots_chains",
            "trees[tree_idx]",
            "trees[0]",
            "trees intended",
        ),
        (
            "SHA2 wrong signing key",
            "sha2-128f",
            "wots_chains",
            "keys[desc.key_idx].state256",
            "keys[0].state256",
            "keys intended",
        ),
        (
            "SHA2 wrong chain word",
            "sha2-128f",
            "wots_tlen",
            "chain_tips[off + 1u]",
            "chain_tips[off + 2u]",
            "chain_tips intended",
        ),
        (
            "SHAKE sibling/left swap",
            "shake-128s",
            "xmss_reduce",
            "left[i] = leaves[l_off",
            "left[i] = leaves[r_off",
            "leaves_left intended",
        ),
        (
            "SHAKE wrong FORS tree",
            "shake-128s",
            "fors_pass1",
            "job.indices[tree_i]",
            "job.indices[tree_i+1]",
            "indices intended",
        ),
        (
            "SHA2 wrong subtree sibling",
            "sha2-128s",
            "fors_pass2",
            "in_sub_roots[l_off + i]",
            "in_sub_roots[r_off + i]",
            "in_sub_roots_left intended",
        ),
        (
            "SHAKE stream crosses signature",
            "shake-128f",
            "fors_pk",
            "i < total_lanes",
            "i <= total_lanes",
            "fors_roots stream position",
        ),
        (
            "SHAKE wrong previous layer",
            "shake-128f",
            "wots_sign",
            "xmss_roots[off + i]",
            "xmss_roots[off + NL + i]",
            "xmss_roots intended",
        ),
        (
            "SHA2 wrong FORS signature",
            "sha2-128f",
            "wots_sign",
            "pk_fors[off + i]",
            "pk_fors[i]",
            "pk_fors intended",
        ),
        (
            "SHA2 launches past last signature",
            "sha2-128f",
            "fors_pk",
            "sig_idx >= p.num_sigs",
            "sig_idx > p.num_sigs",
            "jobs intended",
        ),
        (
            "SHA2 helper overreads key state",
            "sha2-256s",
            None,
            "st[i] = km.state512[i]",
            "st[i] = km.state512[i+1]",
            "helper_state512 initialized",
        ),
    ]
    for label, row_name, name, original, changed, reason in cases:
        row = next(r for r in rows if r[0] == row_name)
        src = sources[row[1]]
        prefix = "shake_" if row[1] == "shake" else ""
        start = src.index(
            "inline void "
            + prefix
            + (name + "_impl" if name else "thash_pair_words")
            + "("
        )
        end = src.index("\n}", start)
        if original not in src[start:end]:
            raise ValueError("missing mutation target " + label)
        mutant = src[:start] + src[start:end].replace(original, changed, 1) + src[end:]
        if name:
            prog = compile_reads(mutant, prefix, name)
        else:
            program = key_helpers(mutant, False)[0]
            prog = c_parser.CParser().parse(DECLS + "void run()" + program).ext[-1].body
        try:
            Check(row, name or "xmss_reduce", False).verify(prog)
        except ReadFailure as counterexample:
            if reason not in str(counterexample):
                raise
        else:
            raise AssertionError("accepted source mutation: " + label)
        print("Rejected " + label, flush=True)


def host_contracts(rows, sources):
    """Check the descriptor producers, grid limits, and the actual binding of
    every array in the read model, including the no-second-pass FORS alias."""
    c = runpy.run_path(str(HERE / "metal-command.py"))
    b = runpy.run_path(str(HERE / "metal-bindings.py"))
    lib = (ROOT / "metal/src/lib.rs").read_text()
    c["geometry_sources"](lib, (ROOT / "rust/src/params.rs").read_text(), rows)
    b["verify"](lib, sources["sha2"], sources["shake"])
    compact = c["compact"](lib)
    if c["body"](compact, "fncheck_grid(") != c["compact"](
        """if count > u32::MAX as usize / stride {return Err(MetalError("batch exceeds Metal's 32-bit index range".into()));}Ok(())"""
    ):
        raise ValueError("grid admission no longer implies the modeled limit")
    for sign in (False, True):
        for shake in (False, True):
            c["host_access"](lib, sign, shake)
        fn = "sign" if sign else "keygen"
        src = c["body"](compact, f"fn{fn}_internal_batch_family<")
        guards = (
            [
                ("check_grid(num_sigs,sig_bytes.max(d*leaves_per_tree*words))?;", []),
                (
                    "check_grid(num_sigs,p.kasusize*subtrees_per_treeasusize*words)?;",
                    [],
                ),
                (
                    "check_grid(num_sigs,d*leaves_per_tree*wots_len*words)?;",
                    ["ifuse_two_phase"],
                ),
            ]
            if sign
            else [
                ("check_grid(count,leaves_per_tree*words)?;", []),
                (
                    "check_grid(count,leaves_per_tree*wots_len*words)?;",
                    ["ifuse_two_phase"],
                ),
            ]
        )
        guards.append(("letwords=N/iffamily==HashFamily::Shake{8}else{4};", []))
        for guard, path in guards:
            if (
                src.count(guard) != 1
                or c["scopes"](src, src.index(guard)) != path
                or src.index(guard) > src.index("letmutlocked=")
            ):
                raise ValueError("unexpected host read-footprint precondition " + guard)


def main():
    rows = runpy.run_path(str(HERE / "check-metal-kernels.py"))["PARAM_SETS"]
    paths = {"sha2": "slhdsa.metal", "shake": "slhdsa_shake.metal"}
    sources = {
        fam: (ROOT / "metal/shaders" / path).read_text() for fam, path in paths.items()
    }
    host_contracts(rows, sources)
    progs = {
        (fam, name): compile_reads(src, "shake_" if fam == "shake" else "", name)
        for fam, src in sources.items()
        for name in NAMES
    }
    total = 0
    cases = 0
    for row in rows:
        for name in NAMES:
            if name == "fors_pass2" and row[6] <= 8:
                continue
            for keygen in [False, True] if name in NAMES[:4] else [False]:
                total += Check(row, name, keygen).verify(progs[row[1], name])
                cases += 1
        for ir in key_helpers(sources[row[1]], row[1] == "shake"):
            program = c_parser.CParser().parse(DECLS + "void run()" + ir).ext[-1].body
            total += Check(row, "xmss_reduce", False).verify(program)
        print("Verified device read footprints for " + row[0], flush=True)
    negatives(sources, rows)
    print(f"Proved {total} access conditions over {cases} kernel/geometry/mode cases.")


if __name__ == "__main__":
    main()
