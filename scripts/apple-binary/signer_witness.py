"""Extract complete internal signer words, parameter rows, and callee identities."""

import argparse
import hashlib
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
from image import Image, require, sign_extend

CONTROLS = {
    "shake_128s": [
        ("wrongSecretBlock", 0x910043E1, 0x910003E1),
        ("wrongDigestByteOrder", 0xAA0B21CB, 0xAA0B1DCB),
        ("wrongAddressType", 0xD2C00068, 0xD2C00088),
        ("wrongHashCoordinates", 0x9AC9257A, 0x9AC9257B),
        ("wrongResultLength", 0xF9000A88, 0xF9000A97),
    ],
    "sha2_128s": [
        ("wrongPrfKey", 0x910043E0, 0x910003E0),
        ("wrongDigestByteOrder", 0xAA0B21CB, 0xAA0B1DCB),
        ("wrongCompressionRound", 0x5E034002, 0x5E035002),
        ("wrongTreeRegister", 0x9AC92578, 0x9AC9257A),
        ("wrongResultLength", 0xF9000A88, 0xF9000A97),
    ],
    "sha2_192s": [
        ("wrongWideAddressSlot", 0xA9392BB9, 0xA93A2BB9),
        ("wrongSeedContextInput", 0x910103E0, 0x910003E0),
    ],
}


def certificate(image, binary, *, family="shake"):
    require(family in ("sha2", "shake"), "unknown signer family")
    sha2 = family == "sha2"
    ns = "LinkedSha2InternalSigner" if sha2 else "LinkedInternalSigner"
    local = "Sha2." if sha2 else ""
    lines = [
        "import Spec.ArmSha2InternalSigner"
        if sha2
        else "import Spec.ArmInternalSigner",
        "namespace " + ns,
        "open Spec.ArmInternalSigner",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        "-- Mach-O SHA-256 " + hashlib.sha256(image.data).hexdigest(),
    ]
    stubs = subprocess.check_output(
        ["xcrun", "llvm-objdump", "--macho", "--indirect-symbols", binary], text=True
    )
    stub_addr, size, _ = image.sections[b"__stubs"]
    (memcpy,) = [
        int(m, 16)
        for m in re.findall(r"^(0x[0-9a-f]+)\s+\d+\s+_memcpy$", stubs, re.MULTILINE)
        if stub_addr <= int(m, 16) < stub_addr + size
    ]

    def symbol(fragment, suffix):
        (addr,) = {
            addr
            for name, addr in image.symbols
            if fragment in name and name.endswith(suffix)
        }
        return addr

    def table(ws):
        return (
            "#["
            + ",\n ".join(
                ", ".join(f"0x{x:08x}" for x in ws[j : j + 8])
                for j in range(0, len(ws), 8)
            )
            + "]"
        )

    for n in (16, 24, 32):
        suffix = f"Kj{n:x}_EB{4 if sha2 else 6}_".encode()
        crate = b"6slhdsa" if sha2 else b"6slhdsa5shake"
        pc, body = image.function(b"3slh17slh_sign_internal" + suffix, crate)
        (coords,) = [
            pc + 4 * i
            for i, w in enumerate(body)
            if w == (0x1B092969 if sha2 else 0x1B182729)
        ]
        hooks = {
            "copy": memcpy,
            "free": symbol(b"___rust_dealloc", b"___rust_dealloc"),
            "reserve": symbol(
                b"11RawVecInnerpE7reserve21do_reserve_and_handle", b"6slhdsa"
            ),
        }
        seed = ".shake"
        names = [("hmsg", b"4hash5h_msg"), ("ht", b"2ht7ht_sign")]
        if sha2:
            names += [
                ("prf", b"4hash7prf_msg"),
                ("fors", b"4fors9fors_sign"),
                ("recover", b"4fors16fors_pk_from_sig"),
            ]
            if n == 16:
                start = body.index(0x6E200800)
                end = body.index(0x6F00E402)
                iv = list(struct.unpack("<8I", image.read(b"__const", 0x1000D5F30, 32)))
                rounds = list(
                    struct.unpack("<64I", image.read(b"__const", 0x1000DC470, 256))
                )
                seed = f".inlined 0x{pc + 4 * start:x} {list(body[start:end])} {iv} {rounds}"
            else:
                hooks["seed"] = image.function(b"4hash8seed_ctx" + suffix, crate)[0]
                seed = f".external 0x{hooks['seed']:x}"
        else:
            hooks.update(
                absorb=symbol(b"8shake256", b"6Sponge6absorb"),
                finish=symbol(b"8shake256", b"6Sponge6finish"),
                digits=symbol(b"6slhdsa4util", b"7base_2b"),
            )
            names = [
                ("hmsg", b"4hash5h_msg"),
                ("fors", b"10fors_batch4sign"),
                ("recover", b"10fors_batch7recover"),
                ("ht", b"2ht7ht_sign"),
            ]
        for label, name in names:
            hooks[label] = image.function(name + suffix, crate)[0]
        require(
            len(set(hooks.values())) == len(hooks), "expected distinct linked callees"
        )
        lines.append(f"def words{n} : Array Nat := {table(body)}")
        for var in "sf":
            p = f"{family}_{n * 8}{var}"
            entry, ws = image.function(
                f"{len(p)}{p}17slh_sign_internal".encode(), b"6slhdsa4sets"
            )
            (j,) = [i for i, w in enumerate(ws) if w & 0x9F00001F == 0x90000000]
            w = ws[j]
            param = (
                ((entry + 4 * j) // 4096)
                + sign_extend((w >> 5 & 0x7FFFF) * 4 + (w >> 29 & 3), 21)
            ) * 4096 + (ws[j + 1] >> 10 & 4095)
            record = list(image.read(b"__const", param, 36))
            calls = "[" + ",".join(f"(0x{a:x},.{k})" for k, a in hooks.items()) + "]"
            lines.append(
                f"def {p} : Image := ⟨⟨Spec.{p}.n, Spec.{p}.d, Spec.{p}.hp, "
                f"0x{entry:x}, 0, 0x{param:x}, {record}, false, {seed}⟩, "
                f"Spec.{p}, 0x{pc:x}, {table(ws)}, words{n}, 0x{coords:x}, {calls}⟩"
            )
            lines.append(
                f"theorem {p}_checked : ∀ profile : Fin 4, run {p} profile = some {local}expected := by\n"
                "  intro profile; fin_cases profile <;> decide +kernel"
            )
            lines.append(
                f"def {p}_trace {{msg key random out}} (profile : Fin 4) "
                f"(h : run {p} profile = some out) (v : {local}Callees Spec.{p} msg key random) := "
                f"{local}trace h ({p}_checked profile) (by decide) v"
            )
            lines.append(
                f"theorem {p}_eq {{msg key random out}} (profile : Fin 4) "
                f"(h : run {p} profile = some out) (v : {local}Callees Spec.{p} msg key random) : "
                f"{local}materialize v out = Spec.slhSignInternal Spec.{p} msg key random := "
                + (
                    f"({p}_trace profile h v).eq_spec rfl"
                    if sha2
                    else f"LinkedArm.Signer.supported_internal_eq (by decide) ({p}_trace profile h v)"
                )
            )
            for control, old, new in CONTROLS.get(p, ()):
                (j,) = [j for j, w in enumerate(body) if w == old]
                lines.append(
                    f"theorem {control} : run {{ {p} with bodyWords := words{n}.set! {j} "
                    f"0x{new:08x} }} 0 ≠ some {local}expected := by decide +kernel"
                )
    lines += [
        f"#print axioms {family}_128s_trace",
        f"#print axioms {family}_256f_trace",
        f"#print axioms {family}_256f_eq",
        "end " + ns,
    ]
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--family", choices=["sha2", "shake"], default="shake")
    args = parser.parse_args()
    data = args.binary.read_bytes()
    with tempfile.TemporaryDirectory() as folder:
        snapshot = Path(folder) / "linked"
        snapshot.write_bytes(data)
        sys.stdout.write(certificate(Image(data), snapshot, family=args.family))
