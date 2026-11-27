#!/usr/bin/env python3
"""Compare the native XMSS SHA-512 scalar remainder with fresh Rust translations."""
from pathlib import Path
import runpy
import subprocess
import tempfile

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
lean = facade["LEAN"]
common = facade["common"]
cuts = ("crate::sha256::arm_wide", "crate::sha512::paired", "crate::sha512::compress",
        "crate::hash::trunc512", "crate::xmss::hash2", "crate::xmss::arm::prepare_tlen")
target_name = "xmss.arm.batch_root_512_loop0_loop0"


def declarations(path, namespace):
    return list(common["declarations"](common["body"](path, namespace)))


def check(target, tmp):
    tmp.mkdir()
    package = facade["extract"]("rust", target, "ArmXmss", tmp, ["crate::xmss::arm::batch_root"], cuts)
    actual = [d for d in declarations(package / "Funs.lean", "slhdsa") if f"def {target_name}" in d]
    checked = declarations(lean / "Armwide/Xmss/ParentsProgram.lean", "slhdsa.ArmXmss")
    # The same extracted scalar loop also handles the 128-row FORS array.
    actual = [d.replace("{N : Std.Usize}", "{N cap : Std.Usize}").replace("16#usize", "cap") for d in actual]
    if actual != checked or len(actual) != 2:
        raise ValueError(f"{target}: scalar parent remainder changed")
    native = declarations(package / "Funs.lean", "slhdsa")
    levels = []
    for d in native:
        if "def xmss.arm.batch_root_512_loop0.body" in d or "def xmss.arm.batch_root_512_loop0\n" in d:
            d = d.replace("{N : Std.Usize}", "(enabled : Bool) {N : Std.Usize}")
            d = d.replace("sha512.paired.parents_batch a2", "parentSlice enabled a2")
            levels.append(d.replace("512_loop0.body a a1", "512_loop0.body enabled a a1"))
    checked_levels = declarations(lean / "Armwide/Xmss/LevelsProgram.lean", "slhdsa.ArmXmss")
    if len(levels) != 2 or levels != checked_levels[-2:]:
        raise ValueError(f"{target}: native XMSS level traversal changed")
    small = [d.replace("sha256.arm_wide.parents_16", "smallSlice") for d in native
             if "def xmss.arm.batch_root_16_loop0.body" in d
             or "def xmss.arm.batch_root_16_loop0\n" in d]
    checked_small = declarations(lean / "Armwide/Xmss/SmallLevelsProgram.lean", "slhdsa.ArmXmss")
    if len(small) != 2 or small != checked_small[-2:]:
        raise ValueError(f"{target}: 16-byte XMSS level traversal changed")
    portable = lean.parent / "lean/Slhdsa"
    types = declarations(package / "Types.lean", "slhdsa")
    if not types or set(types) - set(declarations(portable / "Types.lean", "slhdsa")):
        raise ValueError(f"{target}: seed or address layout differs from the checked model")
    adrs = [d for d in declarations(package / "Funs.lean", "slhdsa") if "def address.Adrs.with_word3" in d]
    if len(adrs) != 1 or adrs[0] not in declarations(portable / "Funs.lean", "slhdsa"):
        raise ValueError(f"{target}: scalar parent's native address setter differs")
    print(f"{target}: all six SHA-2 parent/level loop declarations and the seed/address models match", flush=True)


def check_small_stores(tmp):
    harness = Path(__file__).with_name("arm-xmss") / "parents.rs"
    source = (facade["ROOT"] / "rust/src/sha256/arm_wide.rs").read_text()
    body = []
    for name in ("parents_16_active", "step4_shared_head"):
        start = source.index("fn " + name)
        body.append(source[start:source.index("\n}", start) + 2])
    code = harness.read_text().replace("// PROJECT_FUNCTIONS", "pub(super) " + "\n".join(body))
    rust = tmp / "parents.rs"
    binary = tmp / "parents"
    rust.write_text(code)
    subprocess.run(["rustc", "--edition=2021", "-Awarnings", "-C", "overflow-checks=yes",
                    rust, "-o", binary], check=True)
    subprocess.run([binary], check=True)
    print("Checked native SHA-256 parent reads, stores and hash modes for 16,384 node configurations.", flush=True)


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as tmp:
        check_small_stores(Path(tmp))
        for target in facade["TARGETS"][:2]:
            check(target, Path(tmp) / target)
    for module, theorem in (("Parents", "remainder"), ("PairedParents", "paired_then_remainder"),
                            ("PhysicalParents", "full_level"), ("Levels", "reduceTree"),
                            ("SmallHash", "smallHash_fips"), ("SmallLevels", "reduceSmall")):
        name = "Armwide.Xmss." + module
        facade["run"](["lake", "build", name], lean)
        facade["audit_theorems"](name, ["slhdsa.ArmXmss." + theorem])
