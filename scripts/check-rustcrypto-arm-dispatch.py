"""Check the linked AArch64 Linux capability probe, cache and backend branches."""

import argparse
import re
from pathlib import Path


def require(value, message):
    if not value:
        raise ValueError(message)


def function(assembly, suffix):
    (symbol,) = re.findall(r"^([^\s:]*" + re.escape(suffix) + r"):$", assembly, re.M)
    region = assembly.split(symbol + ":\n", 1)[1].split("\t.cfi_endproc", 1)[0]
    lines = []
    for line in region.splitlines():
        tokens = line.split()
        if tokens and not tokens[0].startswith((".cfi_", ".size", ".Lfunc_end")):
            lines.append(" ".join(tokens))
    return symbol, lines


def check(sha, probe, bits):
    small = bits == 256
    feature = "sha2" if small else "sha3"
    index = 0 if small else 1
    label = f".LBB{index}_"
    save = 8 if small else 16
    cache_suffix = f"sha{bits}10{feature}_hwcap7STORAGE.0"
    (cache,) = re.findall(
        r"^([^\s:]*" + re.escape(cache_suffix) + r"):\n\s*\.byte\s+255$", sha, re.M
    )
    _, lines = function(sha, f"sha{bits}11compress{bits}")
    hardware, _ = function(sha, f"sha{bits}12aarch64_{feature}8compress")
    start = lines.index(f"adrp x19, {cache}")
    require(
        lines[start : start + 8]
        == [
            f"adrp x19, {cache}",
            f"ldrb w8, [x19, :lo12:{cache}]",
            f"str x0, [sp, #{save}]",
            "cmp w8, #1",
            f"b.eq {label}7",
            "cmp w8, #255",
            f"b.eq {label}6",
            f"{label}2:",
        ],
        "cached hardware decision",
    )
    fresh = lines.index(f"{label}6:")
    dispatch = lines.index(f"{label}7:")
    compute = (
        ["mov x8, x0", "mov x2, x21", "mov x1, x20", "ubfx w9, w8, #6, #1"]
        if small
        else [
            "mov w9, #2228224",
            "mov x2, x21",
            "mov x1, x20",
            "ands x8, x0, x9",
            "cset w9, ne",
        ]
    )
    branch = f"tbz w8, #6, {label}2" if small else f"cbz x8, {label}2"
    require(
        lines[fresh + 1 : dispatch]
        == [
            "mov x20, x1",
            "mov x21, x2",
            f"bl {probe}",
            *compute,
            f"strb w9, [x19, :lo12:{cache}]",
            branch,
        ],
        "initial hardware decision",
    )
    branches = [
        x
        for x in lines
        if re.match(r"^(?:b\.|b |bl |br |blr |cbz |cbnz |tbz |tbnz |ret)", x)
    ]
    require(
        branches
        == [
            f"b.eq {label}7",
            f"b.eq {label}6",
            f"cbz x2, {label}5",
            f"b.ne {label}4",
            "ret",
            f"bl {probe}",
            branch,
            f"b {hardware}",
        ],
        "software loop and hardware tail-call control flow",
    )
    require(
        lines[dispatch + 1] == f"ldr x0, [sp, #{save}]"
        and lines[-1] == f"b {hardware}",
        "hardware arguments",
    )
    require(
        len([line for line in lines if cache in line]) == 3, "unique cache read/write"
    )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("sha2", type=Path)
    p.add_argument("cpufeatures", type=Path)
    args = p.parse_args()
    probe, body = function(args.cpufeatures.read_text(), "aarch6415getauxval_hwcap")
    require(body == ["mov w0, #16", "b getauxval"], "Linux AT_HWCAP selector")
    sha2 = args.sha2.read_text()
    for bits in (256, 512):
        check(sha2, probe, bits)


if __name__ == "__main__":
    main()
