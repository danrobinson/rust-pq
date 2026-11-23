#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["capstone==5.0.6"]
# ///
"""Inventory direct transfers from 24 SHAKE signer exports in a thin arm64 Mach-O.

Print JSON. Every site is a preferred virtual address in the hashed input. A local
node is scanned across its entire LC_FUNCTION_STARTS extent, including cold code.
Indirect targets, imported implementations and exception dispatch are open edges.
"""

import argparse
from bisect import bisect_right
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import tempfile

from capstone import CS_ARCH_ARM64, CS_MODE_LITTLE_ENDIAN, Cs
from capstone.arm64_const import (
    ARM64_GRP_BRANCH_RELATIVE,
    ARM64_GRP_CALL,
    ARM64_GRP_INT,
    ARM64_GRP_JUMP,
    ARM64_GRP_RET,
)

from image import Image, require, sign_extend


def import_stubs(image, path):
    # Use the indirect symbol table to label dyld stub destinations. This identifies
    # the requested import, without making assumptions about the loaded dylib.
    table = subprocess.check_output(
        ["xcrun", "llvm-objdump", "--macho", "--indirect-symbols", path], text=True
    )
    entries = {}
    section = None
    for line in table.splitlines():
        header = re.fullmatch(
            r"Indirect symbols for \(([^,]+),([^\)]+)\) (\d+) entries", line
        )
        if header:
            section = header[2] if header[1] == "__TEXT" else None
        row = re.fullmatch(r"(0x[0-9a-f]+)\s+\d+\s+(\S+)", line)
        if section in ("__stubs", "__auth_stubs") and row:
            addr = int(row[1], 16)
            image.read(section.encode(), addr, 4)
            require(addr not in entries, "duplicate import stub")
            entries[addr] = row[2]
    require(entries, "no import stubs identified")
    return entries


def demangle(symbols):
    names = sorted({name.decode() for name, _ in symbols})
    output = subprocess.check_output(
        ["xcrun", "llvm-cxxfilt", "--strip-underscore"],
        input="\n".join(names) + "\n",
        text=True,
    ).splitlines()
    require(len(output) == len(names), "demangler output length")
    return dict(zip(names, output))


def transfer(insn, word):
    pc = insn.address
    if not insn.id:
        return "undecoded", None, True
    if word & 0x7C000000 == 0x14000000:
        call = bool(word & 0x80000000)
        return (
            ("call" if call else "branch"),
            pc + 4 * sign_extend(word & 0x3FFFFFF, 26),
            call,
        )
    if word & 0xFF000000 == 0x54000000 or word & 0x7E000000 == 0x34000000:
        return "conditional", pc + 4 * sign_extend((word >> 5) & 0x7FFFF, 19), True
    if word & 0x7E000000 == 0x36000000:
        return "conditional", pc + 4 * sign_extend((word >> 5) & 0x3FFF, 14), True
    groups = set(insn.groups)
    if insn.mnemonic in ("ret", "retaa", "retab") and insn.op_str in ("", "lr", "x30"):
        return "return", None, False
    if ARM64_GRP_CALL in groups or insn.mnemonic.startswith("blr"):
        return "indirect_call", None, True
    if (
        ARM64_GRP_INT in groups
        or word & 0xFF000000 == 0xD4000000
        or insn.mnemonic == "udf"
    ):
        return "exception", None, True
    if (
        groups.intersection((ARM64_GRP_BRANCH_RELATIVE, ARM64_GRP_JUMP, ARM64_GRP_RET))
        or word & 0xFE000000 == 0xD6000000
    ):
        return "indirect_branch", None, False
    return None, None, True


def build(image, path):
    text_start, text_size, _ = image.sections[b"__text"]
    ends_at = text_start + text_size
    starts = image.starts
    require(
        all(text_start <= x < ends_at and x % 4 == 0 for x in starts)
        and starts == sorted(set(starts)),
        "invalid text function starts",
    )
    names = defaultdict(list)
    pretty = demangle(image.symbols)
    roots = {}
    for mangled, pc in image.symbols:
        symbol = mangled.decode()
        if text_start <= pc < ends_at:
            names[pc].append(symbol)
        m = re.search(
            r"6slhdsa4sets10(shake_(?:128|192|256)[fs])(?:17slh_sign_internal|8slh_sign|4sign|18sign_deterministic)$",
            symbol,
        )
        if m:
            label = pretty[symbol]
            require(pc in starts and label not in roots, "ambiguous signing entry")
            roots[label] = pc
    require(len(roots) == 24, "expected four signing APIs on each of six sets")
    stubs = import_stubs(image, path)
    decoder = Cs(CS_ARCH_ARM64, CS_MODE_LITTLE_ENDIAN)
    decoder.detail = True
    decoder.skipdata = True
    nodes = {}
    todo = list(roots.values())
    while todo:
        start = todo.pop()
        if start in nodes:
            continue
        idx = bisect_right(starts, start)
        end = starts[idx] if idx < len(starts) else ends_at
        data = image.read(b"__text", start, end - start)
        edges, exits, returns = [], [], []
        pos = start

        def edge(pc, kind, target):
            if target in stubs:
                edges.append(
                    dict(
                        site=hex(pc),
                        kind=kind,
                        stub=hex(target),
                        imported=stubs[target],
                    )
                )
            elif starts[0] <= target < ends_at and target % 4 == 0:
                entry = starts[bisect_right(starts, target) - 1]
                edges.append(
                    dict(site=hex(pc), kind=kind, target=hex(target), local=hex(entry))
                )
                todo.append(entry)
            else:
                exits.append(dict(site=hex(pc), kind=kind, target=hex(target)))

        for inst in decoder.disasm(data, start):
            require(
                inst.address == pos and inst.size == 4,
                "missing or misaligned disassembly",
            )
            pc = pos
            pos += 4
            (word,) = struct.unpack_from("<I", data, pc - start)
            kind, target, falls = transfer(inst, word)
            if kind == "return":
                returns.append(hex(pc))
            elif target is not None:
                if kind == "call" or not start <= target < end:
                    edge(pc, "tail_branch" if kind == "branch" else kind, target)
            elif kind:
                exits.append(
                    dict(
                        site=hex(pc),
                        kind=kind,
                        instruction=inst.mnemonic + " " + inst.op_str,
                    )
                )
            if pos == end and falls:
                # A final BL may invoke a nonreturning panic/unwind routine. Do not
                # manufacture a call edge into an unrelated adjacent function.
                exits.append(
                    dict(site=hex(pc), kind="possible_fallthrough", target=hex(end))
                )
        require(pos == end, "incomplete function disassembly")
        nodes[start] = dict(
            names=[pretty[n] for n in names[start]],
            symbols=names[start],
            size=len(data),
            sha256=hashlib.sha256(data).hexdigest(),
            edges=edges,
            open_exits=exits,
            returns=returns,
        )

    summaries = {}
    for label, root in sorted(roots.items()):
        seen = set()
        stack = [root]
        while stack:
            addr = stack.pop()
            if addr not in seen:
                seen.add(addr)
                stack.extend(
                    int(e["local"], 16) for e in nodes[addr]["edges"] if "local" in e
                )
        imports = {
            e["imported"]
            for addr in seen
            for e in nodes[addr]["edges"]
            if "imported" in e
        }
        summaries[label] = dict(
            entry=hex(root),
            local_functions=len(seen),
            imports=sorted(imports),
            open_sites=sum(len(nodes[addr]["open_exits"]) for addr in seen),
        )
    return dict(
        artifact_sha256=hashlib.sha256(image.data).hexdigest(),
        artifact_bytes=len(image.data),
        architecture="arm64 Mach-O",
        scope="Explicit direct-transfer closure, including cold blocks and padding. "
        "Returns follow the ABI. Import behavior, runtime-selected callees, exceptions "
        "and possible cross-extent fallthrough are unresolved.",
        local_extents=len(nodes),
        direct_sites=dict(
            Counter(e["kind"] for node in nodes.values() for e in node["edges"])
        ),
        open_exits=dict(
            Counter(e["kind"] for node in nodes.values() for e in node["open_exits"])
        ),
        roots=summaries,
        functions={hex(k): nodes[k] for k in sorted(nodes)},
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    args = parser.parse_args()
    data = args.binary.read_bytes()
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "snapshot"
        path.write_bytes(data)
        print(json.dumps(build(Image(data), path), indent=2))
