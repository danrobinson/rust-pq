#!/usr/bin/env python3
"""Re-extract the phase-one width-three direct/split SHAKE FORS ticket bodies."""
from pathlib import Path
import os
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-parallel-wots-ticket.py")))
common, lean = shared["common"], shared["lean"]
fields = {
    "Direct": "first: u16, active: u8, height: u8",
    "Split": "first: u16, active: u8, height: u8, sub_h: u8, chunk: u32, split_base: usize, chunks: usize",
}


def region(body, kind):
    raw = body.split("WorkKind::ForsShake" + kind + " {", 1)[1]
    pattern, raw = raw.split("} => {", 1)
    expected = [field.partition(":")[0] for field in fields[kind].split(", ")]
    if re.findall(r"\w+", pattern) != expected:
        raise ValueError(f"{kind}: ticket destructuring changed")
    pre, raw = raw.split("let first = first as usize;", 1)
    guard = "let _ = (" + ", ".join(expected) + "); shake_only! { #[cfg(any( all(target_arch = \"aarch64\", target_endian = \"little\"), all(target_arch = \"x86_64\", target_feature = \"sse2\") ))] {"
    if pre.split() != guard.split():
        raise ValueError(f"{kind}: unexpected worker availability guard")
    table = "fors_" + kind.lower()
    prefix, store = raw.split("for lane in 0..active {", 1)
    value = "sibs" if kind == "Direct" else "vals"
    m = re.match(r'\s*' + table + r'\[([^\]]+)\]\s*\.set\(' + value +
                 r'\[lane\]\)\s*\.expect\("unique SHAKE FORS ' + kind.lower() + r' slot"\);\s*}\s*}\s*}\s*}', store)
    if not m:
        raise ValueError(f"{kind}: destination or once-cell publication changed")
    suffix = store[m.end():].lstrip()
    if not suffix.startswith("WorkKind::ForsShakeSplit {" if kind == "Direct" else "}"):
        raise ValueError(f"{kind}: unexpected trailing worker actions")
    stride = ", fors_stride: usize" if kind == "Direct" else ""
    return f"""
fn {kind.lower()}_ticket<const N: usize>(sk: &[u8; N], seed: &[u8; N], fors_addr: Adrs,
    fors_indices: &Vec<u32>, a: u32, {fields[kind]}{stride}) ->
    [(usize,[u8; N]); crate::shake256::parallel::WIDTH] {{
    let first = first as usize;
    {prefix}
    let mut writes = [(0usize,[0u8;N]); crate::shake256::parallel::WIDTH];
    for lane in 0..active {{
        writes[lane] = ({m[1]}, {value}[lane]);
    }}
    writes
}}
"""


def extract(folder, target):
    crate = common["copy_rust_crate"](folder)
    path = crate / "src/slh/parallel.rs"
    source = path.read_text()
    for kind, expected in fields.items():
        declaration = re.search(r"^    ForsShake" + kind + r" \{([^}]+)\}", source, re.M)
        if not declaration or declaration[1].strip().removesuffix(",").split() != expected.split():
            raise ValueError(f"{kind}: production ticket field types changed")
    body = shared["shared"]["signer"].function(source, "sign").split("match item.kind {")[-1]
    path.write_text(source + "\nshake_only! {\n" + "\n".join(region(body, k) for k in fields) + "}\n")
    stem = "crate::shake::slh::parallel::"
    return common["extract_target"](target, folder / "generated", [stem + k.lower() + "_ticket" for k in fields],
                                  [stem + "shake_fors_simd::nodes_active"], crate=crate, features="parallel,platform-sha2")

node_name = "shake.slh.parallel.shake_fors_simd.nodes_active"
decls = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))["decls"]


def declarations(pkg, stem, rejects, bound):
    definitions = []
    known = {file: set(decls(lean.parent / f"lean/Slhdsa/{file}.lean", "slhdsa")) for file in ("Types", "Funs")}
    for file in ("Types", "Funs"):
        for decl in decls(pkg / (file + ".lean"), "CacheopsRust"):
            if re.search(r"\bdef\s+" + re.escape(stem), decl):
                definitions.append(decl)
            elif decl not in known[file] and decl not in bound:
                raise ValueError("unknown ticket dependency: " + decl)
    extern = set(re.findall(r"^axiom ([\w.]+)", (pkg / "FunsExternal_Template.lean").read_text(), re.M))
    if extern != rejects:
        raise ValueError(f"unexpected external declarations: {extern ^ rejects}")
    return "\n\n".join(definitions)


def nodes_program(pkg):
    width = "@[global_simps, irreducible] def shake256.parallel.WIDTH : Std.Usize := 3#usize"
    if width not in decls(pkg / "Funs.lean", "CacheopsRust"):
        raise ValueError("actual parallel::WIDTH did not evaluate to three")
    raw = declarations(pkg, node_name, {"core.array.Array.map", "shake.batch.pair_active", "shake.fors_batch.fors_subtree_horiz",
                                       "shake.fors_batch.fors_leaves_fused"}, {width})
    for old, new in [(node_name, "nodes"), ("shake256.parallel.WIDTH", "3#usize"), ("shake.fors_batch.fors_subtree_horiz", "wide.run"),
                     ("shake.fors_batch.fors_leaves_fused", "(ForsFused.fused activeHash)"),
                     ("shake.batch.pair_active", "(ActiveHash.pair_active activeHash)")]:
        raw = raw.replace(old, new)
    return ("""import Cachepath.NativeVerify.ActiveHashes
import Cachepath.NativeVerify.ForsFused
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelForsTicket
open ShakeBatch NativeVerify
noncomputable section
local instance ticketNodeMachine : Machine := Kldisp.machine
def activeHash := fullActive Kldisp.machine KldispRust.shake256.parallel.available
class Wide where
  run {N : Usize} : Array U8 N → Array U8 N → address.Adrs → U32 → U32 → Result (Array U8 N)
variable [wide : Wide]

""" + raw + "\nend\nend slhdsa.ParallelForsTicket\n")


def ticket_program(pkg):
    defs = declarations(pkg, "shake.slh.parallel.", {node_name}, set())
    raw = defs.replace(node_name, "nodes").replace("shake.slh.parallel.", "")
    return ("""import Parallel.ForsTicketNodesProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelForsTicket
noncomputable section
variable [wide : Wide]

""" + raw + "\nend\nend slhdsa.ParallelForsTicket\n")

def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    with tempfile.TemporaryDirectory() as d:
        folder = Path(d)
        target = "aarch64-unknown-linux-gnu"
        pkg = extract(folder / "tickets", target)
        nodes = common["extract_target"](
            target, folder / "nodes", ["crate::shake::slh::parallel::shake_fors_simd::nodes_active"],
            ["crate::shake::fors_batch::fors_leaves_fused", "crate::shake::fors_batch::fors_subtree_horiz",
             "crate::shake::batch::pair_active"], crate=folder / "tickets/rust", features="parallel,platform-sha2")
        for name, source in [("ForsTicketNodesProgram", nodes_program(nodes)), ("ForsTicketProgram", ticket_program(pkg))]:
            if source.split() != (lean / f"Parallel/{name}.lean").read_text().split():
                raise ValueError(f"extracted Linux Arm {name} changed")
        path = pkg / "Funs.lean"
        src = path.read_text()
        for old, new in [("i9 >>> i3", "i9 >>> 0#u32"), ("root_idx <<< i4", "root_idx <<< 0#u32"),
                         ("lane * chunks", "lane + chunks")]:
            path.write_text(shared["shared"]["signer"].once(src, old, new))
            if ticket_program(pkg).split() == (lean / "Parallel/ForsTicketProgram.lean").read_text().split():
                raise ValueError("accepted modified FORS ticket")
    facade = shared["shared"]["facade"]
    module = "Parallel.ForsTickets"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](module, ["slhdsa.ParallelForsTicket." + n for n in
                             ("nodes_spec", "direct_ticket_spec", "split_ticket_spec")])


if __name__ == "__main__":
    main()
