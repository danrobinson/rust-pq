"""Check direct XMSS call schedules on every normal path through linked SHAKE ht_sign."""

import re
import subprocess
from graphlib import TopologicalSorter

from image import require, sign_extend


def instructions(path, pc, words):
    # LLVM supplies register destinations for straight-line, flag-preserving instructions.
    # All control flow and instructions that compute the abstract state are decoded from bytes.
    output = subprocess.check_output(
        [
            "xcrun",
            "llvm-objdump",
            "-d",
            f"--start-address={pc}",
            f"--stop-address={pc + 4 * len(words)}",
            path,
        ],
        text=True,
    )
    decoded = {}
    for line in output.splitlines():
        m = re.match(r"^([0-9a-f]+):\s+([0-9a-f]{8})\s+([\w.]+)\s*(.*)", line)
        if m:
            offset = int(m[1], 16) - pc
            require(
                0 <= offset < 4 * len(words) and offset % 4 == 0,
                "unexpected instruction address",
            )
            i = offset // 4
            require(i not in decoded, "duplicate decoded instruction")
            require(words[i] == int(m[2], 16), "disassembly differs from snapshot")
            decoded[i] = (m[3], m[4].split(";")[0].strip())
    require(len(decoded) == len(words), "incomplete disassembly")
    return decoded


def verify_schedule(words, pc, decoded, depth, sign, recover, stubs, alloc):
    # Abstract state includes the PC, layer, public depth register, NZCV comparison,
    # whether x0 still contains the parameter pointer, and length of the observed trace.
    initial = (0, None, None, None, True, 0)
    todo = [initial]
    graph = {}
    returns = 0
    while todo:
        state = todo.pop()
        if state in graph:
            continue
        i, layer, count, flags, param, events = state
        require(0 <= i < len(words), "branch escapes signer")
        word = words[i]
        op, operands = decoded[i]
        next_pcs = [i + 1]
        if word == 0xB940141C:  # LDR w28,[x0,#20]
            require(param, "invalid parameter base")
            count = depth
        elif word == 0x52800013:  # MOV w19,#0
            layer = 0
        elif word == 0x11000673:  # ADD w19,w19,#1
            require(layer is not None and layer < depth, "wrong layer increment")
            layer += 1
        elif word in (0x6B13039F, 0x6B1C027F):  # CMP w28,w19 or w19,w28
            require(
                layer is not None and count is not None, "unknown public comparison"
            )
            flags = count - layer if word == 0x6B13039F else layer - count
        elif word == 0xEB08037F:  # CMP x27,x8 (buffer capacity)
            flags = None
        elif word & 0xFF000010 == 0x54000000:
            cond = word & 15
            require(cond in (0, 2, 8), "unsupported branch condition")
            target = i + sign_extend(word >> 5 & 0x7FFFF, 19)
            if flags is None:
                next_pcs.append(target)
            elif {0: flags == 0, 2: flags >= 0, 8: flags > 0}[cond]:
                next_pcs = [target]
        elif word & 0x7F000000 == 0x34000000:  # CBZ W/X
            reg = word & 31
            val = count if reg == 28 else layer if reg == 19 else None
            target = i + sign_extend(word >> 5 & 0x7FFFF, 19)
            if val is None:
                next_pcs.append(target)
            elif val == 0:
                next_pcs = [target]
        elif word & 0xFC000000 == 0x14000000:
            next_pcs = [i + sign_extend(word & 0x3FFFFFF, 26)]
        elif word & 0xFC000000 == 0x94000000:
            target = pc + 4 * (i + sign_extend(word & 0x3FFFFFF, 26))
            if target in (sign, recover):
                require(
                    events < 2 * depth - 1
                    and target == (sign, recover)[events % 2]
                    and layer == (events + 1) // 2,
                    "incorrect XMSS call schedule",
                )
                events += 1
            else:
                require(target in alloc or target in stubs, "unrecognized helper call")
            flags = None
            param = False
        elif word == 0xD65F03C0:
            require(events == 2 * depth - 1, "incorrect XMSS count on return")
            next_pcs = []
            returns += 1
        else:
            # Only non-writeback, flag-preserving data transfers and ALU instructions.
            require(
                "]!" not in operands and "]," not in operands,
                "unexpected base writeback",
            )
            if op not in {"stp", "str", "stur"}:
                require(
                    op
                    in {
                        "ldp",
                        "ldr",
                        "ldur",
                        "add",
                        "sub",
                        "and",
                        "bic",
                        "mov",
                        "lsl",
                        "lsr",
                    },
                    f"unmodeled instruction {op}",
                )
                destinations = operands.split(",")[: 2 if op == "ldp" else 1]
                for reg in (s.strip() for s in destinations):
                    if reg in ("w19", "x19"):
                        layer = None
                    if reg in ("w28", "x28"):
                        count = None
                    if reg in ("w0", "x0"):
                        param = False
        edges = [(j, layer, count, flags, param, events) for j in next_pcs]
        graph[state] = edges
        todo.extend(edges)
    # Acyclicity and total successor coverage prove every modeled execution reaches a RET.
    list(TopologicalSorter(graph).static_order())
    require(returns > 0, "no returning path")


def verify(image, path):
    stubs_addr, stubs_size, _ = image.sections[b"__stubs"]
    # Calls into an import stub or an allocation helper are modeled as normal ABI returns.
    stubs = range(stubs_addr, stubs_addr + stubs_size, 12)
    alloc = {
        a
        for name, a in image.symbols
        if b"do_reserve_and_handle" in name or name.endswith(b"___rust_dealloc")
    }
    for width, depths in ((16, (7, 22)), (24, (7, 22)), (32, (8, 17))):
        suffix = f"Kj{width:x}_EB6_".encode()
        pc, words = image.function(b"7ht_sign" + suffix, b"6slhdsa5shake2ht")
        sign, _ = image.function(b"9xmss_sign" + suffix, b"6slhdsa5shake4xmss")
        recover, _ = image.function(
            b"16xmss_pk_from_sig" + suffix, b"6slhdsa5shake4xmss"
        )
        decoded = instructions(path, pc, words)
        for depth in depths:
            verify_schedule(words, pc, decoded, depth, sign, recover, stubs, alloc)
