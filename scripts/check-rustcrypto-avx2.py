#!/usr/bin/env python3
"""Bind RustCrypto's locked paired/single SHA-512 compressor to its Lean refinement."""
import copy
import json
from pathlib import Path
import re
import runpy
import shutil
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-arm-api-proof.py")))
ROOT, LEAN, run = common["ROOT"], common["LEAN"], common["run"]
TARGET = "x86_64-unknown-linux-gnu"
HELPERS = ("rk", "cast_ms", "cast_rs", "load_data_avx", "load_data_avx2")
ANCHOR = "fn proof_slice_len(blocks: &[[u8; 128]]) -> usize { blocks.len() }"


def descendants(tree):
    if isinstance(tree, dict):
        yield tree
        for child in tree.values():
            yield from descendants(child)
    elif isinstance(tree, list):
        for child in tree:
            yield from descendants(child)


def lower_slice_metadata(path):
    # For a shared reference to [T], Rust's PtrMetadata yields the usize element
    # count. Aeneas models the same operation through core::slice::len, but does
    # not currently interpret this MIR projection in a slice pattern match.
    ir = json.loads(path.read_text())
    functions = [f for f in ir["translated"]["fun_decls"] if f]

    def lookup(name):
        function, = (f for f in functions if f["item_meta"]["name"][-1] == {"Ident": [name, 0]})
        return function["body"]

    anchor, = (node["Call"] for node in descendants(lookup("proof_slice_len")) if "Call" in node)
    body = lookup("compress")
    instruction, = (node for node in descendants(body) if "Assign" in node
                    and "Use" in node["Assign"][1] and "PtrMetadata" in str(node["Assign"][1]))
    dest, rhs = instruction["Assign"]
    place, _copy_trait = rhs["Use"][0]["Copy"]
    reference, projection = place["kind"]["Projection"]
    region, pointee, mode = reference["ty"]["Untagged"]["Ref"]
    element, _ = pointee["Untagged"]["Slice"]
    call = copy.deepcopy(anchor)
    generics = call["call"]["func"]["Regular"]["generics"]
    if (projection != "PtrMetadata" or mode != "Shared" or generics["types"] != [element]
            or place["ty"] != dest["ty"] or dest["ty"] != anchor["dest"]["ty"]):
        raise ValueError("unsupported pointer metadata projection")
    generics["regions"] = [region]
    call["call"]["args"] = [{"Read": reference}]
    call["dest"] = dest
    # No unwind is possible for a metadata read. Give the replacement a bare
    # unwind-resume edge instead of copying cleanup instructions from the anchor.
    call["on_unwind"]["statements"] = [call["on_unwind"]["statements"][-1]]
    if call["on_unwind"]["statements"][0]["kind"] != "UnwindResume":
        raise ValueError("unexpected unwind terminator")
    instruction.clear()
    instruction["Call"] = call
    path.write_text(json.dumps(ir))


def check_memory(crate):
    source = (crate / "src/sha512/x86_avx2.rs").read_text()
    bodies = "\n\n".join(re.search(r"^fn " + name + r"\(.*?^}", source, re.M | re.S)[0]
                         for name in HELPERS)
    template = (ROOT / "scripts/fixtures/rustcrypto-avx2-memory.rs").read_text().strip()
    pattern = re.escape(template)
    for name in ("MASK128", "MASK256"):
        pattern = pattern.replace(re.escape("{" + name + "}"), rf"(?P<{name}>[\s0-9a-fA-Fx_,i]+)")
    match = re.fullmatch(pattern, bodies)
    if not match:
        raise ValueError("unsupported Rust pointer/cast program")
    a, b, c, d = (int(x.strip(), 16) for x in match["MASK128"].split(","))
    h, l, h2, l2 = (int(x.strip().removesuffix("_i64"), 16) for x in match["MASK256"].split(",") if x.strip())
    masks = (f"def mask128 := (0x{d:08X}#32 ++ 0x{c:08X}#32) ++ (0x{b:08X}#32 ++ 0x{a:08X}#32)\n"
             f"def mask256half := 0x{h:016X}#64 ++ 0x{l:016X}#64\n")
    lean = (LEAN / "Rcavx/FunsExternal.lean").read_text()
    if (h, l) != (h2, l2) or masks not in lean:
        raise ValueError("PSHUFB byte selectors differ")
    constants = (crate / "src/consts.rs").read_text().split("const K64: [u64; 80] = [", 1)[1].split("];", 1)[0]
    values = lean.split("def roundConstants : List (BitVec 64) := [", 1)[1].split("]", 1)[0]
    if constants.strip() != values.strip() or len(re.findall(r"0x[0-9a-f]+", values)) != 80:
        raise ValueError("SHA-512 round constants differ")


def main():
    graph = json.loads(run(["cargo", "metadata", "--locked", "--format-version", "1",
                            "--features", "platform-sha2", "--filter-platform", TARGET],
                           ROOT / "rust", capture_output=True).stdout)
    root, = (n for n in graph["resolve"]["nodes"] if n["id"] == graph["resolve"]["root"])
    dep, = (d for d in root["deps"] if d["name"] == "sha2_platform")
    crate, = (Path(p["manifest_path"]).parent for p in graph["packages"] if p["id"] == dep["pkg"])
    check_memory(crate)
    with tempfile.TemporaryDirectory(prefix="rustcrypto-avx2-") as temp:
        scratch = Path(temp)
        copied = scratch / "sha2"
        shutil.copytree(crate, copied)
        # Only the unrelated, private extraction anchor is appended. The backend
        # file, configuration, feature attributes and caller remain as shipped.
        with (copied / "src/lib.rs").open("a") as f:
            f.write("\n" + ANCHOR + "\n")
        llbc = scratch / "rcavx.llbc"
        start = "crate::sha512::x86_avx2::"
        run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
             "--no-dedup-serialized-ast", "--start-from", start + "compress",
             "--start-from", "crate::proof_slice_len",
             *(arg for name in HELPERS for arg in ("--opaque", start + name)),
             "--dest-file", llbc, "--", "--locked", "--manifest-path", copied / "Cargo.toml",
             "--target", TARGET, "--target-dir", scratch / "target"], ROOT / "rust")
        lower_slice_metadata(llbc)
        target = scratch / "Rcavx"
        run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error",
             "-no-progress-bar", "-namespace", "RcAvxRust", "-split-files", "-dest", target, llbc], ROOT)
        for name in ("Funs.lean", "Types.lean"):
            if (target / name).read_bytes() != (LEAN / "Rcavx" / name).read_bytes():
                raise ValueError(f"fresh RustCrypto SHA-512 extraction differs in {name}")
        generated = (target / "Funs.lean").read_text()
        widths = re.findall(r"core\.mem\.size_of ([^\s]+)", generated)
        pointer_casts = re.findall(r"core\.ptr\.const_ptr\.RawPtrConstT\.cast ([^\s]+)", generated)
        if widths != ["Std.U64", "Std.U64"] or pointer_casts != ["core.core_arch.x86.__m128i"]:
            raise ValueError("unexpected generic size or raw pointer cast instantiation")
        run(["lake", "build", "Rcavx.Top"], LEAN)
        check = scratch / "Check.lean"
        theorem = "slhdsa.X86.RustCrypto512.refines_bulk"
        check.write_text(f"import Rcavx.Top\n#print axioms {theorem}\n")
        output = run(["lake", "env", "lean", check], LEAN, capture_output=True, text=True).stdout
        if f"'{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in output:
            raise ValueError(output)


if __name__ == "__main__":
    main()
