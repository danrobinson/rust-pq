#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# dependencies = ["pyelftools==0.32"]
# ///
"""Check a matching linked ELF and reject mutations of its instructions and constants."""
import argparse
from pathlib import Path
import runpy
import tempfile
from types import SimpleNamespace


def main(elf):
    gate = runpy.run_path(str(Path(__file__).with_name("check-keccak-elf.py")))
    gate["verify"](SimpleNamespace(elf=elf, save_certificate=None))
    original = elf.read_bytes()
    code, table = gate["extract"](original)

    def locate(opcode, relative):
        pattern = bytes.fromhex(opcode)
        assert code.data.count(pattern) == 1
        return code.offset + code.data.index(pattern) + relative

    edits = {
        "ternary truth table": locate("62 23 d5 40 25 d6 96", 6),
        "loop back edge": locate("0f 85 ec fc ff ff", 2),
        "round-table pointer": locate("31 c9 48 8d 05", 5),
        "round constant": table.offset,
    }
    with tempfile.TemporaryDirectory() as scratch:
        for label, offset in edits.items():
            changed = bytearray(original)
            changed[offset] ^= 1
            path = Path(scratch)/"mutated.elf"
            path.write_bytes(changed)
            try:
                gate["verify"](SimpleNamespace(elf=path, save_certificate=None))
            except ValueError as error:
                if "Tactic `decide` proved that the proposition" not in str(error) or "is false" not in str(error):
                    raise
                print(f"Lean rejected modified {label}", flush=True)
            else:
                raise RuntimeError(f"accepted modified {label}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("elf", type=Path)
    main(parser.parse_args().elf)
