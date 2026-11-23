#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["pyelftools==0.32"]
# ///
"""Prove the complete linked AVX-512 Keccak permutation in a Linux ELF executable.

The input is never executed. Each run embeds its instruction and constant bytes as
Lean literals, checks every byte against the modeled instruction encoding, and proves
the specialized theorem for all eight independent states. Use --save-certificate to
retain the exact proposition, addresses and evidence for this artifact.
"""
import argparse
from dataclasses import dataclass
import hashlib
from io import BytesIO
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from elftools.dwarf.callframe import FDE
from elftools.elf.elffile import ELFFile

ROOT = Path(__file__).resolve().parents[1]
SYMBOL = re.compile(r"_R\w*6slhdsa8shake2568parallel6avx5127permute")
# Fast candidate selection only. Symbol discovery and disassembly are outside the
# mathematical proof; Lean independently checks the *whole* discovered function.
INITIAL_LOAD = bytes.fromhex("6261fe486f07")
LEA = bytes.fromhex("31c9488d05")


def require(condition, message):
    if not condition:
        raise ValueError(message)


@dataclass(frozen=True)
class Region:
    address: int
    offset: int
    data: bytes


def mapped(raw, loads, addr, size, flags, page_size=4096):
    require(0 < size < 2**32 and 0 <= addr < addr + size <= 2**64, "invalid virtual range")
    # Reject load overlap even when it arises solely from page rounding in mmap.
    mask = page_size - 1
    mappings = [ph for ph in loads if (ph["p_vaddr"] & ~mask) < addr + size and
                addr < ((ph["p_vaddr"] + ph["p_memsz"] + mask) & ~mask)]
    require(len(mappings) == 1, "ambiguous or missing load mapping")
    ph = mappings[0]
    delta = addr - ph["p_vaddr"]
    require(ph["p_flags"] == flags and 0 <= delta <= ph["p_filesz"] - size,
            "range lacks the required file backing or permissions")
    offset = ph["p_offset"] + delta
    require(offset + size <= len(raw), "truncated file-backed range")
    return Region(addr, offset, raw[offset:offset+size])


def check_relocations(elf, loads, pointer_types=(1, 6, 7, 8)):
    dynamic = list(elf.iter_segments("PT_DYNAMIC"))
    require(len(dynamic) <= 1, "multiple dynamic segments")
    if not dynamic:
        return
    dyn = dynamic[0]
    for tag in dyn.iter_tags():
        name = tag.entry.d_tag
        require(isinstance(name, str) and "ANDROID" not in name, "unsupported dynamic tag")
        require(name != "DT_TEXTREL" and not (name == "DT_FLAGS" and tag.entry.d_val & 4),
                "load image permits text relocations")
    # All supported target-specific pointer relocations write one 8-byte value.
    # Reject COPY, other variable-width writes, or targets outside writable loads.
    for table, entries in dyn.get_relocation_tables().items():
        for r in entries.iter_relocations():
            require(table == "RELR" or r["r_info_type"] in pointer_types,
                    "unsupported dynamic relocation")
            place = r["r_offset"]
            require(any(p["p_flags"] & 2 and p["p_vaddr"] <= place and
                        place+8 <= p["p_vaddr"]+p["p_memsz"] for p in loads),
                    "relocation targets an immutable mapping")


def extract(raw):
    elf = ELFFile(BytesIO(raw))
    require(elf.elfclass == 64 and elf.little_endian and elf["e_machine"] == "EM_X86_64"
            and elf["e_type"] in ("ET_EXEC", "ET_DYN"), "expected a linked x86-64 Linux ELF")
    loads = list(elf.iter_segments("PT_LOAD"))
    for p in loads:
        require(p["p_vaddr"] % 4096 == p["p_offset"] % 4096 and
                p["p_filesz"] <= p["p_memsz"] and p["p_offset"] + p["p_filesz"] <= len(raw)
                and p["p_vaddr"] + p["p_memsz"] <= 2**64, "invalid load segment")
    check_relocations(elf, loads)

    # Use unwind information even for stripped executables. A defined symbol,
    # when present, must independently agree on the entry and exact extent.
    eh = elf.get_section_by_name(".eh_frame")
    require(eh is not None, "missing unwind extents")
    entries = elf.get_dwarf_info().EH_CFI_entries()
    candidates = []
    for fde in entries:
        if not isinstance(fde, FDE):
            continue
        addr, size = fde["initial_location"], fde["address_range"]
        if size == 1158:
            region = mapped(raw, loads, addr, size, 5)
            if region.data.startswith(INITIAL_LOAD):
                candidates.append(region)
    require(len(candidates) == 1, "expected one candidate permutation with complete unwind extent")
    code = candidates[0]
    symtab = elf.get_section_by_name(".symtab")
    if symtab is not None:
        functions = [sym for sym in symtab.iter_symbols() if SYMBOL.fullmatch(sym.name)]
        require(len(functions) == 1 and functions[0]["st_info"]["type"] == "STT_FUNC" and
                (functions[0]["st_value"], functions[0]["st_size"]) == (code.address, len(code.data)),
                "ELF symbol and unwind extent disagree")
    require(code.data.count(LEA) == 1, "expected one counter initializer and RIP-relative LEA")
    off = code.data.index(LEA) + len(LEA)
    disp = int.from_bytes(code.data[off:off+4], "little", signed=True)
    table = mapped(raw, loads, code.address + off + 4 + disp, 192, 4)
    return code, table


def literal(data):
    return "[\n  " + ",\n  ".join(", ".join(f"0x{v:02x}" for v in data[i:i+24])
                                  for i in range(0, len(data), 24)) + "\n]"


def certificate(digest, code, table):
    return f"""-- SHA-256 of the entire linked ELF: {digest}
import Keccakasm.LinkedTrace
open slhdsa.KeccakAsm.Binary Spec.Keccak
set_option maxRecDepth 131072
set_option maxHeartbeats 0
namespace slhdsa.KeccakAsm.Release

def entry : Nat := {code.address}
def tableAddress : Nat := {table.address}
def textBytes : Bytes := {literal(code.data)}
def tableBytes : Bytes := {literal(table.data)}

private theorem checkedBytes : reachableTable entry tableAddress ∧
    textBytes = imageCode rows ops entry tableAddress ∧ tableBytes = roundTable := by decide

theorem artifact_permutation_fips (regs : Fin 8 → Registers) (input : Fin 8 → State)
    (shape : ∀ i, (input i).size = 25) :
    (fun i => runImage entry tableAddress textBytes tableBytes (regs i) (input i)) =
      fun i => some (permute (input i)) :=
  image_fips checkedBytes.1 checkedBytes.2.1 checkedBytes.2.2 regs input shape

theorem artifact_trace_fips (regs : Registers) (input : State) (shape : input.size = 25) :
    observedImage entry tableAddress textBytes tableBytes regs input = some (permute input, accessTrace) :=
  image_trace_fips checkedBytes.1 checkedBytes.2.1 checkedBytes.2.2 regs input shape

#print axioms artifact_permutation_fips
#print axioms artifact_trace_fips
end slhdsa.KeccakAsm.Release
"""


def verify(args):
    raw = args.elf.read_bytes()
    code, table = extract(raw)
    digest = hashlib.sha256(raw).hexdigest()
    program = certificate(digest, code, table)
    env = dict(os.environ)
    env["PATH"] = str(Path.home()/".elan/bin") + os.pathsep + env["PATH"]
    subprocess.run(["lake", "build", "Keccakasm.LinkedTrace"], cwd=ROOT/"lean-hw", env=env, check=True)
    with tempfile.TemporaryDirectory() as tmp:
        proof = Path(tmp)/"Artifact.lean"
        proof.write_text(program)
        p = subprocess.run(["lake", "env", "lean", proof], cwd=ROOT/"lean-hw", env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if p.returncode:
            raise ValueError("linked image certificate failed:\n" + p.stdout)
        for name in ("artifact_permutation_fips", "artifact_trace_fips"):
            reports = re.findall(r"^'slhdsa\.KeccakAsm\.Release\." + name + r"' depends on axioms: \[([^\]]*)\]", p.stdout, re.M)
            require(len(reports) == 1 and {a.strip() for a in reports[0].split(",")} <=
                    {"propext", "Classical.choice", "Quot.sound"}, f"unexpected axiom report for {name}")
    if args.save_certificate:
        args.save_certificate.write_text(program)
    return dict(elf_sha256=digest, entry=hex(code.address), function_bytes=len(code.data),
                function_sha256=hashlib.sha256(code.data).hexdigest(),
                table_address=hex(table.address), table_bytes=len(table.data),
                table_sha256=hashlib.sha256(table.data).hexdigest(),
                theorems=["artifact_permutation_fips", "artifact_trace_fips"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    parser.add_argument("--save-certificate", type=Path)
    print(json.dumps(verify(parser.parse_args()), indent=2))
