#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["pyelftools==0.32"]
# ///
"""Bind Linux AArch64 SHA-256/512 compression in a linked ELF to Rcarmcode.Proof.

Run scripts/check-arm-sha2-elf.py --negative-controls /path/to/executable.
The executable may be stripped. The checker builds the locked dependency's release
assembly, reassembles the validated instruction stream with its Lean constant pool,
and checks every linked instruction and relocated literal. To reuse existing output,
pass a second positional argument pointing at sha2-*.s from the same release build
with RUSTFLAGS=--emit=asm,link. Requires the Rust aarch64-unknown-linux-gnu target,
the repository's Lean dependencies, and clang's AArch64 integrated assembler.
"""

import argparse
import hashlib
from io import BytesIO
import json
import os
from pathlib import Path
import re
import runpy
import struct
import subprocess
import tempfile

from elftools.dwarf.callframe import FDE
from elftools.elf.elffile import ELFFile

ROOT = Path(__file__).resolve().parents[1]
decode = runpy.run_path(str(ROOT / "scripts/check-rustcrypto-arm-code.py"))["decode"]
elf_checks = runpy.run_path(str(ROOT / "scripts/check-keccak-elf.py"))
mapped = elf_checks["mapped"]
require = elf_checks["require"]


def reference(assembly, bits, tmp, clang):
    suffix = f"sha{bits}12aarch64_sha{2 if bits == 256 else 3}8compress"
    pool, program = decode(assembly, False, bits)
    model = (
        ROOT / "lean-hw/Rcarmcode" / ("Code.lean" if bits == 256 else "Code512.lean")
    ).read_text()
    (constants,) = re.findall(r"def linuxConstants [^=]+:= \[([^\]]+)\]", model)
    require(
        pool == list(map(int, re.findall(r"\d+", constants))),
        "Lean constant pool differs",
    )
    body = (
        model.split("\ndef linux (", 1)[1].split(" :=\n", 1)[1].split("\n\ndef ", 1)[0]
    )
    require(
        "\n".join(program) == body, "Linux register program differs from the Lean model"
    )

    (symbol,) = re.findall(r"^(\w*" + suffix + r"):$", assembly, re.M)
    source = assembly.split(symbol + ":\n", 1)[1].split("\t.cfi_endproc", 1)[0]
    rows = []
    for line in source.splitlines():
        row = line.strip()
        if (
            not row
            or row.startswith((".cfi_", ".size\t"))
            or re.fullmatch(r"\.Lfunc_end\d+:", row)
        ):
            continue
        require(
            re.fullmatch(r"\.LBB\d+_\d+:|[a-z][\w.]*[ \t\w.#,:\[\]!\-]*", row),
            "unexpected assembly directive or operand",
        )
        rows.append(row)
    labels = set(re.findall(r"\.LCPI\d+_\d+", "\n".join(rows)))
    lanes = 4 if bits == 256 else 2
    require(len(labels) == len(pool) // lanes, "wrong constant label count")
    asm = [".section .rodata", ".balign 16"]
    directive = ".word " if bits == 256 else ".xword "
    for label in sorted(labels):
        index = int(label.rsplit("_", 1)[1]) * lanes
        asm.extend(
            [label + ":", directive + ", ".join(map(str, pool[index : index + lanes]))]
        )
    asm.extend([".text", *rows])
    path = tmp / "reference.o"
    subprocess.run(
        [
            clang,
            "-target",
            "aarch64-linux-gnu",
            "-march=armv8.2-a+crypto+sha3",
            "-x",
            "assembler",
            "-c",
            "-o",
            path,
            "-",
        ],
        check=True,
        input="\n".join(asm) + "\n",
        text=True,
    )
    obj = ELFFile(BytesIO(path.read_bytes()))
    code = obj.get_section_by_name(".text").data()
    rels = obj.get_section_by_name(".rela.text")
    symtab = obj.get_section(rels["sh_link"])
    fixes = {}
    for r in rels.iter_relocations():
        symbol = symtab.get_symbol(r["r_info_sym"])
        section = obj.get_section(symbol["st_shndx"])
        offset, kind = r["r_offset"], r["r_info_type"]
        require(
            section.name == ".rodata"
            and offset not in fixes
            and 0 <= offset <= len(code) - 4
            and offset % 4 == 0
            and kind in (275, 299),
            "unexpected reference relocation",
        )
        start = symbol["st_value"] + r["r_addend"]
        require(
            start % 16 == 0 and 0 <= start <= section["sh_size"] - 16,
            "invalid reference constant range",
        )
        fixes[offset] = (kind, start, section.data()[start : start + 16])
    require(len(fixes) == 2 * len(labels), "incomplete constant relocations")
    return suffix, code, fixes


def bind(raw, loads, code, ref, fixes):
    pages = {}
    addresses = []
    for off in range(0, len(ref), 4):
        (expected,) = struct.unpack_from("<I", ref, off)
        (actual,) = struct.unpack_from("<I", code.data, off)
        if off not in fixes:
            # Rcarmcode.Linked.linked_add_equivalent proves this exact pair of encodings.
            require(
                actual == expected or (actual, expected) == (0x4EF98463, 0x4EE38723),
                f"instruction differs at +{off:#x}",
            )
            continue
        kind, index, value = fixes[off]
        if kind == 275:  # R_AARCH64_ADR_PREL_PG_HI21
            require(
                expected & ~31 == 0x90000000 and expected == actual & ~0x60FFFFE0,
                "unexpected ADRP encoding",
            )
            delta = ((actual >> 5 & 0x7FFFF) << 2) | (actual >> 29 & 3)
            signed = (delta ^ (1 << 20)) - (1 << 20)
            reg = actual & 31
            require(reg not in pages, "unconsumed page register")
            pages[reg] = (index, ((code.address + off) & ~4095) + (signed << 12))
        else:  # R_AARCH64_LDST128_ABS_LO12_NC
            require(
                expected & 0xFFC00000 == 0x3DC00000
                and expected == actual & ~0x003FFC00,
                "unexpected LDR Q encoding",
            )
            reg = actual >> 5 & 31
            require(reg in pages, "missing ADRP before vector load")
            target, page = pages.pop(reg)
            address = page + 16 * (actual >> 10 & 0xFFF)
            require(
                target == index
                and mapped(raw, loads, address, 16, 4, 65536).data == value,
                f"wrong SHA-2 literal at {address:#x}",
            )
            addresses.append(address)
    require(not pages, "incomplete page/load pair")
    return addresses


def negative_controls(raw, loads, code, ref, fixes, constants):
    words = list(struct.iter_unpack("<I", code.data))
    (branch,) = [
        i for i, (word,) in enumerate(words) if word & 0xFF00001F == 0xB4000002
    ]
    page = next(off for off, (kind, _, _) in fixes.items() if kind == 275)
    literal = mapped(raw, loads, constants[0], 16, 4, 65536)
    # Change the CBZ target, the ADRP target page, and the first referenced literal.
    for position, mask in [
        (code.offset + 4 * branch, 32),
        (code.offset + page + 3, 32),
        (literal.offset, 1),
    ]:
        damaged = bytearray(raw)
        damaged[position] ^= mask
        changed = mapped(damaged, loads, code.address, len(ref), 5, 65536)
        try:
            bind(damaged, loads, changed, ref, fixes)
        except ValueError:
            continue
        raise ValueError("corrupt linked image passed verification")


def check_theorems():
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env["PATH"]
    cwd = ROOT / "lean-hw"
    subprocess.run(
        ["lake", "build", "Rcarmcode.Linked"],
        cwd=cwd,
        env=env,
        stdout=subprocess.DEVNULL,
        check=True,
    )
    names = [
        "slhdsa.RcArmCode.execute_is_fips",
        "slhdsa.RcArmCode.S512.execute_is_fips",
        "slhdsa.RcArmCode.Linked.linked_add_equivalent",
    ]
    query = "import Rcarmcode.Linked\n" + "".join(f"#print axioms {n}\n" for n in names)
    report = subprocess.check_output(
        ["lake", "env", "lean", "--stdin"], input=query, text=True, cwd=cwd, env=env
    )
    for name in names:
        (axioms,) = re.findall(
            r"^'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", report, re.M
        )
        require(
            set(map(str.strip, axioms.split(",")))
            <= {"propext", "Classical.choice", "Quot.sound"},
            f"unexpected axiom in {name}",
        )


def verify(raw, assembly, clang, controls):
    elf = ELFFile(BytesIO(raw))
    require(
        elf.elfclass == 64
        and elf.little_endian
        and elf["e_machine"] == "EM_AARCH64"
        and elf["e_type"] in ("ET_EXEC", "ET_DYN"),
        "expected a linked little-endian AArch64 ELF",
    )
    loads = list(elf.iter_segments("PT_LOAD"))
    for p in loads:
        require(
            p["p_vaddr"] % 65536 == p["p_offset"] % 65536
            and p["p_filesz"] <= p["p_memsz"]
            and p["p_offset"] + p["p_filesz"] <= len(raw)
            and p["p_vaddr"] + p["p_memsz"] <= 2**64,
            "invalid 64 KiB compatible load segment",
        )
    elf_checks["check_relocations"](elf, loads, (257, 1025, 1026, 1027))
    entries = elf.get_dwarf_info().EH_CFI_entries()
    symtab = elf.get_section_by_name(".symtab")
    results = []
    with tempfile.TemporaryDirectory() as tmp:
        for bits in (256, 512):
            suffix, ref, fixes = reference(assembly, bits, Path(tmp), clang)
            candidates = [
                mapped(raw, loads, f["initial_location"], len(ref), 5, 65536)
                for f in entries
                if isinstance(f, FDE) and f["address_range"] == len(ref)
            ]
            (code,) = [c for c in candidates if c.data[:4] == ref[:4]]
            if symtab is not None:
                (sym,) = [s for s in symtab.iter_symbols() if s.name.endswith(suffix)]
                require(
                    sym["st_info"]["type"] == "STT_FUNC"
                    and (sym["st_value"], sym["st_size"]) == (code.address, len(ref)),
                    "symbol disagrees with unwind extent",
                )
            constants = bind(raw, loads, code, ref, fixes)
            if controls:
                negative_controls(raw, loads, code, ref, fixes, constants)
            ns = "slhdsa.RcArmCode." + ("" if bits == 256 else "S512.")
            results.append(
                dict(
                    algorithm=f"SHA-{bits}",
                    entry=hex(code.address),
                    function_bytes=len(ref),
                    function_sha256=hashlib.sha256(code.data).hexdigest(),
                    literal_loads=len(constants),
                    theorem=ns + "execute_is_fips",
                )
            )
    check_theorems()
    return dict(
        elf_sha256=hashlib.sha256(raw).hexdigest(),
        compressors=results,
        negative_controls_per_compressor=3 if controls else 0,
    )


def release_assembly():
    with tempfile.TemporaryDirectory() as tmp:
        env = dict(os.environ, CARGO_TARGET_DIR=tmp, RUSTFLAGS="--emit=asm,link")
        env["PATH"] = str(Path.home() / ".cargo/bin") + os.pathsep + env["PATH"]
        target = "aarch64-unknown-linux-gnu"
        subprocess.run(
            [
                "cargo",
                "build",
                "--manifest-path",
                "rust/Cargo.toml",
                "--locked",
                "--release",
                "--features",
                "platform-sha2",
                "--target",
                target,
            ],
            cwd=ROOT,
            env=env,
            check=True,
        )
        (asm,) = (Path(tmp) / target / "release").rglob("sha2-*.s")
        return asm.read_text()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("assembly", type=Path, nargs="?")
    parser.add_argument("--clang", default="clang")
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    assembly = args.assembly.read_text() if args.assembly else release_assembly()
    print(
        json.dumps(
            verify(args.elf.read_bytes(), assembly, args.clang, args.negative_controls),
            indent=2,
        )
    )
