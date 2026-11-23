#!/usr/bin/env python3
"""Re-extract the locked SHA-NI compressor and check its SHA-256 refinement."""
import json
import re
from pathlib import Path
import runpy
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-arm-api-proof.py")))
ROOT, LEAN, run = common["ROOT"], common["LEAN"], common["run"]
TARGET = "x86_64-unknown-linux-gnu"
HELPERS = ("load_block", "load_state", "store_state")


def check_memory(source):
    # Match the complete helper bodies. Every captured operand below is translated
    # into the exact memory primitives consumed by the compression theorem.
    template = (ROOT / "scripts/fixtures/rustcrypto-shani-memory.rs").read_text().strip()
    pattern = re.escape(template)
    for name, expression in (
        ("MASK_HIGH", "0x[0-9A-Fa-f_]+"), ("MASK_LOW", "0x[0-9A-Fa-f_]+"),
        ("FIRST_OFFSET", "[01]"), ("SECOND_OFFSET", "[01]"),
        ("FIRST_VALUE", "dcba|hgef"), ("SECOND_VALUE", "dcba|hgef"),
    ):
        pattern = pattern.replace(re.escape("{" + name + "}"), f"(?P<{name}>{expression})")
    match = re.fullmatch(pattern, source)
    if match is None:
        raise ValueError("unsupported raw memory helper program")
    fields = match.groupdict()
    hi, lo = (int(fields["MASK_" + part], 16) for part in ("HIGH", "LOW"))
    program = f"""def sha256.x86_sha.load_block (b : Array U8 64#usize) : Result (Array Reg 4#usize) :=
  let lane := Memory.shuffled b 0x{hi:016X} 0x{lo:016X}
  ok (Array.make 4#usize [lane 0,lane 1,lane 2,lane 3])
def sha256.x86_sha.load_state (s : Array U32 8#usize) : Result (Array Reg 2#usize) :=
  ok (Array.make 2#usize [Memory.readState s 0,Memory.readState s 1])
def sha256.x86_sha.store_state (s : Array U32 8#usize) (v : Array Reg 2#usize) : Result (Array U32 8#usize) :=
"""
    for insn in ("FIRST", "SECOND"):
        register = ("dcba", "hgef").index(fields[insn + "_VALUE"])
        program += f"  let s := Memory.store s {fields[insn + '_OFFSET']} v.val[{register}]!\n"
    program += "  ok s\nend RcNiRust\n"
    committed = (LEAN / "Rcni/FunsExternal.lean").read_text()
    if committed[committed.index("def sha256.x86_sha.load_block"):] != program:
        raise ValueError("generated pointer load/shuffle/store program differs from Lean inputs")


def main():
    graph = json.loads(run(["cargo", "metadata", "--locked", "--format-version", "1",
                            "--features", "platform-sha2", "--filter-platform", TARGET],
                           ROOT / "rust", capture_output=True).stdout)
    root, = (node for node in graph["resolve"]["nodes"] if node["id"] == graph["resolve"]["root"])
    dependency, = (dep for dep in root["deps"] if dep["name"] == "sha2_platform")
    sha2, = (package for package in graph["packages"] if package["id"] == dependency["pkg"])
    manifest = Path(sha2["manifest_path"])
    source = (manifest.parent / "src/sha256/x86_sha.rs").read_text()
    first = source.index("fn load_block(")
    last = source.index('#[target_feature(enable = "sha,sse4.1")]', first)
    check_memory(source[first:last].strip())
    with tempfile.TemporaryDirectory(prefix="rc-shani-") as temp:
        scratch = Path(temp)
        llbc = scratch / "rcni.llbc"
        target = scratch / "Rcni"
        start = "crate::sha256::x86_sha::"
        run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
             "--start-from", start + "compress",
             *(arg for name in HELPERS for arg in ("--opaque", start + name)),
             "--dest-file", llbc, "--", "--locked", "--manifest-path", manifest,
             "--target", TARGET, "--target-dir", scratch / "target"], ROOT / "rust")
        run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error",
             "-no-progress-bar", "-namespace", "RcNiRust", "-split-files",
             "-dest", target, llbc], ROOT)
        for name in ("Funs.lean", "Types.lean"):
            if (target / name).read_bytes() != (LEAN / "Rcni" / name).read_bytes():
                raise ValueError(f"fresh RustCrypto extraction differs in {name}")
        run(["lake", "build", "Rcni.Top"], LEAN)
        check = scratch / "Check.lean"
        check.write_text("import Rcni.Top\n#print axioms slhdsa.Intel.RustCrypto.refines_bulk\n")
        output = run(["lake", "env", "lean", check], LEAN, capture_output=True, text=True).stdout
        if "'slhdsa.Intel.RustCrypto.refines_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]" not in output:
            raise ValueError(output)


if __name__ == "__main__":
    main()
