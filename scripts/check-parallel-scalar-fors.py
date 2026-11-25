#!/usr/bin/env python3
"""Bind scalar direct/split worker publications and the native FORS node dispatcher."""

from pathlib import Path
import os
import re
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
ticket = runpy.run_path(str(HERE / "check-parallel-wots-ticket.py"))
common, lean = ticket["common"], ticket["lean"]
decls = runpy.run_path(str(HERE / "check-cache-construction.py"))["decls"]
targets = {
    "aarch64-apple-darwin": 8,
    "aarch64-unknown-linux-gnu": 3,
    "x86_64-unknown-linux-gnu": 8,
}


def project(source):
    rust = source
    for table, size in [
        ("fors_direct", "k * fors_stride"),
        ("fors_split", "fors_split_count"),
    ]:
        allocation = f"let {table}: Vec<OnceLock<[u8; N]>> = (0..{size}).map(|_| OnceLock::new()).collect();"
        if " ".join(rust.split()).count(allocation) != 1:
            raise ValueError("scalar FORS destination allocation changed")
    body = (
        ticket["shared"]["signer"].function(rust, "sign").split("match item.kind {")[-1]
    )
    for variant, after, table in [
        ("Direct", "ForsNodeSplit", "fors_direct"),
        ("Split", "ForsShakeLow", "fors_split"),
    ]:
        head = "WorkKind::ForsNode" + variant + " {"
        if body.count(head) != 1:
            raise ValueError("scalar FORS branch changed")
        fields, code = body.split(head)[1].split("} => {", 1)
        if re.findall(r"\w+", fields) != ["idx", "height", "slot"]:
            raise ValueError("scalar FORS ticket fields changed")
        arm = code.split("WorkKind::" + after + " {")[0]
        match = re.fullmatch(
            r"(.*?)\b"
            + table
            + r'\[([^\]]+)\]\s*\.set\(node\)\s*\.expect\("unique FORS '
            + variant.lower()
            + r' slot"\);\s*}\s*',
            arm,
            re.S,
        )
        if not match:
            raise ValueError("scalar FORS publication changed")
        rust += f"""
fn {variant.lower()}_node_ticket<const N: usize>(sk:&[u8; N],seed:&Seed<N>,fors_addr:Adrs,
    idx:u32,height:u32,slot:usize) -> (usize,[u8;N]) {{
    {match[1]} ({match[2]},node)
}}
"""
    # Both queue producers use the same geometry for the direct/split variants.
    emit = ticket["shared"]["signer"].function(source, "sign").split("let run = ||")[0]
    stride = "let fors_stride = a as usize + 1;"
    root = "let root_idx = (t << (a - j)) + ((idx >> j) ^ 1);"
    if emit.count(stride) != 1 or emit.count(root) != 2:
        raise ValueError("scalar job geometry changed")
    if emit.count("let idx = fors_indices[t as usize];") != 2:
        raise ValueError("scalar FORS queue selection changed")
    for variant in ("Direct", "Split"):
        records = re.findall(
            r"kind:\s*WorkKind::ForsNode" + variant + r"\s*\{([^}]+)\}", emit
        )
        if len(records) != 2:
            raise ValueError("scalar FORS ticket producer count changed")
        normalize = lambda x: re.sub(r"\s+", "", x)
        if normalize(records[0]) != normalize(records[1]):
            raise ValueError("the two scalar FORS queue producers differ")
        fields = dict(re.findall(r"(idx|height|slot):\s*([^,]+),", records[0]))
        if set(fields) != {"idx", "height", "slot"}:
            raise ValueError("scalar FORS queue record changed")
        if variant == "Split":
            for formula in (
                "let split = j - fors_target;",
                "let split = j.saturating_sub(fors_target);",
            ):
                if formula not in emit:
                    raise ValueError("scalar FORS subdivision changed")
            # The saturated variant is extracted below from the same producer record.
            prelude = "let split = j - fors_target;"
            args = ", fors_target:u32, slot_start:usize, c:usize"
        else:
            prelude, args = "", ""
        rust += f"""
fn prepare_{variant.lower()}(t:u32, a:u32, j:u32, idx:u32{args}) -> (u32,u32,usize) {{
    {stride} {root} {prelude}
    ({fields["idx"]},{fields["height"]},{fields["slot"]})
}}
"""
    raw = ticket["shared"]["signer"].function(rust, "prepare_split")
    rust += "\n" + raw.replace("fn prepare_split(", "fn prepare_saturating(").replace(
        "let split = j - fors_target;", "let split = j.saturating_sub(fors_target);"
    )
    return rust


def extract(folder, target):
    crate = common["copy_rust_crate"](folder)
    src = crate / "src/slh/parallel.rs"
    source = src.read_text()
    for before, after in [
        ("fors_direct[slot]", "fors_split[slot]"),
        ("fors_split[slot].set(node)", "fors_direct[slot].set(node)"),
    ]:
        if before not in source:
            raise ValueError(f"missing source mutation site {before}")
        try:
            project(source.replace(before, after))
        except ValueError:
            pass
        else:
            raise ValueError("accepted mutated worker destination")
    src.write_text(project(source))
    return common["extract_target"](
        target,
        folder / "generated",
        [
            "crate::shake::slh::parallel::" + name + "_node_ticket"
            for name in ("direct", "split")
        ]
        + [
            "crate::shake::slh::parallel::prepare_" + n
            for n in ("direct", "split", "saturating")
        ],
        [
            "crate::shake::fors_batch::fors_subtree_horiz",
            "crate::shake::batch::available",
            "crate::shake::fors::fors_sk_gen",
            "crate::shake::hash::thash",
            "crate::shake::hash::thash_pair",
        ],
        crate=crate,
        features="parallel,platform-sha2",
    )


def program(pkg, width):
    known = set(decls(lean.parent / "lean/Slhdsa/Funs.lean", "slhdsa"))
    expected = {
        "shake.fors_batch.fors_subtree_horiz",
        "shake.batch.available",
        "shake.fors.fors_sk_gen",
        "shake.hash.thash",
        "shake.hash.thash_pair",
    }
    ext = set(
        re.findall(
            r"^axiom ([\w.]+)", (pkg / "FunsExternal_Template.lean").read_text(), re.M
        )
    )
    if ext != expected:
        raise ValueError(f"changed scalar FORS cut points: {ext ^ expected}")
    constant = f"@[global_simps, irreducible] def shake256.parallel.WIDTH : Std.Usize := {width}#usize"
    functions = decls(pkg / "Funs.lean", "CacheopsRust")
    if constant not in functions:
        raise ValueError("compiled FORS lane count changed")
    selected = []
    for decl in functions:
        if re.match(
            r"def (?:shake.fors.fors_node|shake.slh.parallel.(?:(direct|split)_node_ticket|prepare_(direct|split|saturating)))\s",
            decl,
        ):
            selected.append(decl)
        elif decl != constant and decl not in known:
            raise ValueError("unbound scalar FORS dependency: " + decl)
    if len(selected) != 6 or not set(
        decls(pkg / "Types.lean", "CacheopsRust")
    ).issubset(decls(lean.parent / "lean/Slhdsa/Types.lean", "slhdsa")):
        raise ValueError("scalar FORS ticket definitions or input types changed")
    body = "\n\n".join(selected)
    for old, new in [
        ("shake.fors.fors_node", "node"),
        ("shake.slh.parallel.", ""),
        ("shake256.parallel.WIDTH", "host.width"),
        ("shake.batch.available", "host.probe"),
        ("shake.fors_batch.fors_subtree_horiz", "host.horizontal"),
    ]:
        body = body.replace(old, new)
    return (
        """import Shakebatch.WidthEightModel
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelScalarFors
class Host where
  width : Usize
  probe : Usize → Result Bool
  horizontal {N : Usize} : Array U8 N → Array U8 N → address.Adrs → U32 → U32 → Result (Array U8 N)

variable [host : Host]

"""
        + body
        + "\nend slhdsa.ParallelScalarFors\n"
    )


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    )
    checked = (lean / "Parallel/ScalarForsProgram.lean").read_text().split()
    with tempfile.TemporaryDirectory() as d:
        for target, width in targets.items():
            folder = Path(d) / target
            folder.mkdir()
            pkg = extract(folder, target)
            if program(pkg, width).split() != checked:
                raise ValueError(f"{target} scalar FORS extracted program changed")
            path = pkg / "Funs.lean"
            body = path.read_text()
            for old, new in [
                (
                    "fors_subtree_horiz sk seed adrs i z",
                    "fors_subtree_horiz sk seed adrs z i",
                ),
                ("ok (slot, node)", "ok (0#usize, node)"),
                ("let i3 ← idx >>> j", "let i3 ← idx >>> a"),
            ]:
                if old not in body:
                    raise ValueError(f"missing mutation site: {old}")
                path.write_text(body.replace(old, new, 1))
                if program(pkg, width).split() == checked:
                    raise ValueError(f"{target} accepted mutation: {new}")
            path.write_text(body)
    facade = ticket["shared"]["facade"]
    module = "Parallel.ScalarForsPublish"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](
        module,
        [
            "slhdsa.ParallelScalarFors." + name
            for name in (
                "sibling_room",
                "direct_geometry",
                "split_geometry",
                "saturating_eq",
                "direct_published",
                "split_published",
                "native_laws",
            )
        ],
    )


if __name__ == "__main__":
    main()
