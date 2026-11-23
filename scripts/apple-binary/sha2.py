"""Bind the linked Arm SHA-2 compression routines to the existing Rcarmcode theorems."""

from pathlib import Path
import re
import runpy
import struct

from hypertree import instructions
from image import require, sign_extend


ROOT = Path(__file__).resolve().parents[2]
decode = runpy.run_path(str(ROOT / "scripts/check-rustcrypto-arm-code.py"))["decode"]


def verify(image, path, bits):
    suffix = f"4sha26sha{bits}11compress{bits}".encode()
    candidates = []
    for name, _ in image.symbols:
        if name.endswith(suffix):
            pc, words = image.function(name, suffix)
            if words[0] & 0xFFC003E0 != 0xAD400000:  # paired vector state load from x0
                continue
            obj = instructions(path, pc, words)
            if any(
                op == f"sha{bits}h." + ("4s" if bits == 256 else "2d")
                for op, _ in obj.values()
            ):
                candidates.append((pc, words, obj))
    require(len(candidates) == 1, "missing or ambiguous hardware compression function")
    pc, words, obj = candidates[0]
    model_file = "Code.lean" if bits == 256 else "Code512.lean"
    model = (ROOT / "lean-hw/Rcarmcode" / model_file).read_text()
    (pool_text,) = re.findall(r"def appleConstants [^=]+:= \[([^\]]+)\]", model)
    pool = list(map(int, re.findall(r"\d+", pool_text)))
    count = 4 if bits == 256 else 2
    unpack = "<4I" if bits == 256 else "<2Q"
    chunks = [tuple(pool[i : i + count]) for i in range(0, len(pool), count)]

    # Adapt linked addresses to the local labels expected by the existing symbolic executor.
    # The reconstructed constant directives contain the words read at the encoded address.
    labels = {}
    data = []
    rows = []
    pending = {}
    i = 0
    while i < len(words):
        op, args = obj[i]
        w = words[i]
        if op == "adrp":
            require(w & 0x9F000000 == 0x90000000, "unexpected page instruction")
            pages = sign_extend(((w >> 5 & 0x7FFFF) << 2) | (w >> 29 & 3), 21)
            page = ((pc + 4 * i) & ~4095) + 4096 * pages
            reg = w & 31
            require(reg not in pending, "unconsumed page address")
            pending[reg] = (i, page)
            rows.append(None)
            i += 1
            continue
        if w & 0xFFC00000 == 0x3DC00000 and (w >> 5 & 31) in pending:
            reg = w >> 5 & 31
            page_i, page = pending.pop(reg)
            va = page + 16 * (w >> 10 & 4095)
            values = struct.unpack(unpack, image.read(b"__const", va, 16))
            require(values in chunks, "incorrect linked SHA-2 constants")
            label = f"LCPI0_{chunks.index(values)}"
            directive = ".long" if bits == 256 else ".quad"
            data += [label + ":", *(f"  {directive} {x}" for x in values)]
            rows[page_i] = f"adrp x{reg}, {label}@PAGE"
            rows.append(f"ldr q{w & 31}, [x{reg}, {label}@PAGEOFF]")
            i += 1
            continue
        if op in ("cbz", "b.ne"):
            require(
                (
                    w & 0xFF00001F == 0x54000001
                    if op == "b.ne"
                    else w & 0xFF00001F == 0xB4000002
                ),
                "unexpected SHA-2 branch",
            )
            target = i + sign_extend(w >> 5 & 0x7FFFF, 19)
            labels[target] = f"LBB0_{target}"
            args = ("x2, " if op == "cbz" else "") + labels[target]
        else:
            args = re.sub(
                r"#(-?)0x([0-9a-f]+)", lambda m: "#" + m[1] + str(int(m[2], 16)), args
            )
        rows.append((op + " " + args).rstrip())
        i += 1
    require(
        not pending
        and len(rows) == len(words)
        and all(0 <= j < len(rows) for j in labels),
        "bad control-flow boundary",
    )
    asm = data + [suffix.decode() + ":"]
    for j, row in enumerate(rows):
        if j in labels:
            asm.append(labels[j] + ":")
        asm.append(row)
    actual_pool, code = decode("\n".join(asm) + "\n\t.cfi_endproc", True, bits)
    expected_code = (
        model.split("\ndef apple (", 1)[1].split(" :=\n", 1)[1].split("\n\nend ", 1)[0]
    )
    require(
        actual_pool == pool and "\n".join(code) == expected_code,
        "linked SHA-2 register program differs from Lean proof",
    )
    return len(words) * 4
