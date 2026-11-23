"""Extract the shared SHAKE pure framing function and resolve its allocator/memcpy call targets."""

import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from image import Image
from pure_sign import memcpy_address, symbol


def certificate(image, path):
    entry, words = image.function(b"12with_context", b"6slhdsa5shake3slh")
    grow = symbol(image, b"5alloc7raw_vec", b"6RawVechE8grow_oneB7_")
    reserve = symbol(image, b"7reserve21do_reserve_and_handle", b"6slhdsa")
    copy = memcpy_address(image, path)
    lines = [
        "import Spec.ArmPureFrame",
        "namespace LinkedApplePureFrame",
        "open Spec.ArmPureFrame",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 65536",
        f"def image : Image := ⟨0x{entry:x},#[",
        ",\n".join(
            ",".join(hex(w) for w in words[i : i + 8]) for i in range(0, len(words), 8)
        ),
        f"],0x{grow:x},0x{reserve:x},0x{copy:x}⟩",
        "theorem checked (b : Choices) : run image b = some (expected b) := by",
        "  rcases b with ⟨g,c,m,ec,em⟩",
        "  cases g <;> cases c <;> cases m <;> cases ec <;> cases em <;> decide +kernel",
        "theorem framed {b pieces} (h : run image b = some pieces) (m ctx : Spec.Bytes)",
        "    (hc : b.emptyC = decide (ctx = [])) (hm : b.emptyM = decide (m = [])) :",
        "    pieces.flatMap (bytes m ctx) = Spec.withContext m ctx := of_run (checked b) h m ctx hc hm",
    ]
    for tag, i, flip, profile in [
        ("wrongDomain", 17, 22 ^ 31, 0),
        ("wrongContextByte", 26, 22 ^ 20, 0),
        ("wrongContextCopyLength", 38, (22 ^ 20) << 16, 0),
        ("wrongMessageSource", 50, (21 ^ 23) << 16, 0),
        ("wrongGrowthBranch", 22, 1 ^ 8, 1),
        ("wrongReserveLength", 73, (20 ^ 22) << 16, 4),
    ]:
        lines += [
            f"theorem {tag} : run {{image with words := image.words.set! {i} {hex(words[i] ^ flip)}}} (choices {profile}) ≠",
            f"    some (expected (choices {profile})) := by decide +kernel",
        ]
    return "\n".join(lines + ["#print axioms framed", "end LinkedApplePureFrame", ""])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    path = parser.parse_args().binary
    print(certificate(Image(path.read_bytes()), path), end="")
