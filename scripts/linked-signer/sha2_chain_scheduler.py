# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Replay complete Apple SHA256 chain scheduler induction for valid WOTS arrays."""

import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
from pathlib import Path
import struct
import sys
import tempfile

sys.dont_write_bytecode = True
from driver import Image, require
from sha2_chain_refill import verify as verify_edges
from sha2_chain_episode import verify as verify_window


def windows(path, n, lanes):
    image = Image(path.read_bytes())
    verify_window(path, image, n, lanes, 1, fors=True)
    for rounds in range(1, 16):
        verify_window(path, image, n, lanes, rounds)


def mutation_tests(path):
    data = path.read_bytes()
    image = Image(data)
    pc, words = image.function(b"4hash12chain_blocksKj10_EB4_", b"6slhdsa")
    tests = [
        (
            0x1A8,
            0x91000508,
            0x91000908,
            "refill context",
            lambda p, i: verify_edges(p, i, 16),
        ),
        (
            0x1930,
            0x390055CF,
            0x390055DF,
            "SHA chain writeback",
            lambda p, i: verify_window(p, i, 16, 2, 2),
        ),
        (
            0x1984,
            0xAD000A01,
            0xAD000A00,
            "packed survivor record",
            lambda p, i: verify_window(p, i, 16, 2, 2),
        ),
        # Drop a high address-counter bit. All WOTS round counters fit four bits.
        (
            0x1920,
            0x53107DF0,
            0x53117DF0,
            "SHA chain writeback",
            lambda p, i: verify_window(p, i, 16, 2, 1, fors=True),
        ),
    ]
    with tempfile.TemporaryDirectory() as tmp:
        exe = Path(tmp) / "altered"
        for offset, old, new, witness, replay in tests:
            require(words[offset // 4] == old, "scheduler mutation anchor")
            altered = bytearray(data)
            struct.pack_into("<I", altered, pc - image.base + offset, new)
            exe.write_bytes(altered)
            try:
                replay(exe, Image(altered))
            except ValueError as exc:
                require(witness in str(exc), f"wrong scheduler mutation failure: {exc}")
            else:
                raise AssertionError("accepted a mutated native scheduler")
    print("Rejected four linked scheduler mutations", flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("binary", type=Path)
    p.add_argument("--workers", type=int, default=3)
    p.add_argument("--self-test", action="store_true")
    a = p.parse_args()
    data = a.binary.read_bytes()
    image = Image(data)
    if a.self_test:
        mutation_tests(a.binary)
    for n in (16, 24, 32):
        verify_edges(a.binary, image, n, fors=True)
        verify_edges(a.binary, image, n)
    with ProcessPoolExecutor(max_workers=a.workers) as pool:
        futures = [
            pool.submit(windows, a.binary, n, lanes)
            for lanes in (4, 3, 2, 1)
            for n in (16, 24, 32)
        ]
        for future in futures:
            future.result()
    print(
        "All 180 WOTS windows and 12 one-round FORS windows agree with sequential SHA-256 compression."
    )
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
