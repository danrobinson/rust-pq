#!/usr/bin/env python3
"""Verify supported SHAKE and SHA-2 routines in a linked Apple arm64 release executable."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import subprocess
import tempfile

from bulk import decode as decode_bulk, mutation_tests as bulk_mutation_tests
from entries import certificate as entry_certificate
from hypertree import verify as verify_hypertree
from image import Image, require
from permute import decode
from reject import certificate as rejection_certificate
from pure_wrapper_witness import certificate as pure_wrapper_certificate
from pure_frame_witness import certificate as pure_frame_certificate
from sha2_verify_witness import gate as sha2_verify_length, body as sha2_verify_body
from keygen_witness import certificate as keygen_certificate
from signer_witness import certificate as signer_certificate
from segmented_frame_witness import certificate as segmented_frame_certificate
from verify_length_witness import certificate as verify_length_certificate
from verify_body_witness import certificate as verify_body_certificate
from pure_sign import (
    verify as pure_sign_certificate,
    mutation_tests as pure_sign_mutations,
)
from sha2 import verify as verify_sha2
from single import verify

ROOT = Path(__file__).resolve().parents[2]


def expected(i):
    """Unfolding hint for Lean. 'change' checks this against Spec.Keccak.roundAt."""
    rotations = [
        0,
        1,
        62,
        28,
        27,
        36,
        44,
        6,
        55,
        20,
        3,
        10,
        43,
        25,
        39,
        41,
        45,
        15,
        21,
        8,
        18,
        2,
        61,
        56,
        14,
    ]

    def parity(x):
        return "(" + " ^^^ ".join(f"a[{x + 5 * y}]!" for y in range(5)) + ")"

    def rho(j):
        x, y = j % 5, j // 5
        src = (x + 3 * y) % 5 + 5 * x
        col = src % 5
        return (
            f"(a[{src}]! ^^^ ({parity((col + 4) % 5)} ^^^ "
            f"{parity((col + 1) % 5)}.rotateLeft 1)).rotateLeft {rotations[src]}"
        )

    row = i // 5 * 5
    result = (
        f"{rho(i)} ^^^ ((~~~({rho(row + (i + 1) % 5)})) &&& ({rho(row + (i + 2) % 5)}))"
    )
    return result + (" ^^^ rc" if i == 0 else "")


def certificate(words, table, instructions, layout, *, bulk=False):
    namespace = "LinkedArmBulk" if bulk else "LinkedArm"
    machine = "Spec.ArmSha3Binary.runBulk" if bulk else "Spec.ArmSha3Binary.run"
    lines = [
        "import Spec.ShakeWords",
        "import Spec.ArmSha3Binary",
        "import Mathlib.Tactic.IntervalCases",
        f"namespace {namespace}",
        "open Spec.Keccak",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 800000",
    ]
    for i, expr in enumerate(words):
        lines += [
            f"def word{i} (a : State) (rc : Lane) : Lane := {expr}",
            f"theorem cell{i} (a : State) (rc : Lane) : word{i} a rc = (round a rc)[{i}]! := by",
            f"  rw [roundAt _ _ _ (by decide)]",
            f"  change word{i} a rc = {expected(i)}",
            f"  unfold word{i}",
            "  ac_rfl",
        ]
    lines += [
        "def linkedRound (a : State) (rc : Lane) : State := #["
        + ", ".join(f"word{i} a rc" for i in range(25))
        + "]",
        "theorem round_eq (a : State) (rc : Lane) : linkedRound a rc = round a rc := by",
        "  apply ext25",
        "  · rfl",
        "  · simp only [round, Id.run, pure, Array.size_ofFn]",
        "  · intro i hi",
        "    interval_cases i",
    ]
    lines += [f"    · exact cell{i} a rc" for i in range(25)]
    lines += [
        f"def instructions : List Nat := {instructions}",
        f"def registers : List Nat := {layout}",
        "theorem decoded_eq (a : State) (rc : Lane) (s : Spec.ArmSha3Binary.Registers) :",
        f"    {machine} instructions registers a rc s = some (round a rc) := by",
        "  rw [← round_eq]",
        "  rfl",
        "#print axioms decoded_eq",
        "def linkedConstants : Array Lane := #[" + ",".join(map(str, table)) + "]",
        "def machineRound (scratch : Lane → Spec.ArmSha3Binary.Registers) (a : State) (rc : Lane) :=",
        f"  ({machine} instructions registers a rc (scratch rc)).getD #[]",
        "theorem permutation_eq (a : State) (scratch : Lane → Spec.ArmSha3Binary.Registers) :",
        "    linkedConstants.foldl (machineRound scratch) a = permute a := by",
        "  have h : machineRound scratch = round := by",
        "    funext a rc",
        "    simp only [machineRound, decoded_eq, Option.getD_some]",
        "  rw [h]",
        "  rfl",
        "#print axioms permutation_eq",
    ]
    if bulk:
        lines.insert(0, "import Spec.ArmRateBlocks")
        lines += [
            "theorem blocks_eq (scratch : Lane → Spec.ArmSha3Binary.Registers) (a : State)",
            "    (size : a.size = 25) (words : List Spec.Bytes) (width : ∀ w ∈ words, w.length = 8) :",
            "    let out := words.foldl (ArmRateBlocks.word (fun s => linkedConstants.foldl (machineRound scratch) s)) (a,0)",
            "    (out.1, 8*out.2) = words.flatten.foldl feed (a,0) :=",
            "  ArmRateBlocks.foldWords _ (fun s => permutation_eq s scratch) words width a size 0 (by decide)",
            "#print axioms blocks_eq",
        ]
    lines.append(f"end {namespace}")
    return "\n".join(lines) + "\n"


def check(image, scratch, env, export=None):
    address, words, table, instructions, layout = decode(image)
    verify(image, address)
    path = scratch / "LinkedArm.lean"
    digest = hashlib.sha256(image.data).hexdigest()
    path.write_text(
        f"/- Generated from Mach-O SHA-256 {digest}. -/\n"
        + certificate(words, table, instructions, layout)
    )
    result = subprocess.run(
        ["lake", "env", "lean", path],
        cwd=ROOT / "lean",
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if result.returncode:
        if "error:" not in result.stdout:
            raise RuntimeError(result.stdout)
        raise ValueError(
            "\n".join(line for line in result.stdout.splitlines() if "error:" in line)[
                :3500
            ]
        )
    report = re.search(
        r"'LinkedArm.permutation_eq' (?:does not depend on any axioms|depends on axioms: \[([^\]]+)\])",
        result.stdout,
    )
    require(report is not None, "missing kernel audit")
    if report[1]:
        require(
            set(report[1].split(", ")) <= {"propext", "Quot.sound", "Classical.choice"},
            "unexpected axiom",
        )

    if export is not None:
        export.write_bytes(path.read_bytes())


def mutation_tests(image, scratch, env):
    pc, words = image.function(b"4sha37permute")
    wrap, wrapper = image.function(b"parallel6single")

    def mutate(addr, mask, stage):
        raw = bytearray(image.data)
        addr -= image.base
        struct.pack_into("<I", raw, addr, struct.unpack_from("<I", raw, addr)[0] ^ mask)
        try:
            check(Image(raw), scratch, env)
        except ValueError as err:
            require(stage in str(err), f"mutation rejected for the wrong reason: {err}")
        else:
            raise AssertionError("mutated binary passed")

    rotate = next(i for i, w in enumerate(words) if w & 0xFFE00000 == 0xCE800000)
    mutate(
        pc + 4 * rotate, 1 << 10, "error:"
    )  # Keep the instruction valid, change the rotation.
    branch = next(i for i, w in enumerate(words) if w & 0xFF00001F == 0x54000001)
    mutate(pc + 4 * branch, 1 << 5, "round backedge")
    call = next(i for i, w in enumerate(wrapper) if w & 0xFC000000 == 0x94000000)
    mutate(wrap + 4 * call, 1, "wrong callee")
    # Mutate the table fetched by the encoded ADRP/ADD (validated independently by decode).
    _, _, table, _, _ = decode(image)
    needle = struct.pack("<24Q", *table)
    base, size, offset = image.sections[b"__const"]
    loc = image.data.index(needle, offset, offset + size)
    require(
        image.data.count(needle, offset, offset + size) == 1,
        "ambiguous test constant table",
    )
    mutate(base + loc - offset, 1, "error:")
    # Toggle SHA256H to SHA256H2. Both decode, only the original register flow proves.
    (digest_symbol,) = [
        n
        for n, a in image.symbols
        if n.endswith(b"4sha26sha25611compress256")
        and struct.unpack("<I", image.read(b"__text", a, 4))[0] & 0xFFC003E0
        == 0xAD400000
    ]
    sha_pc, body = image.function(digest_symbol, b"4sha2")
    index = next(i for i, w in enumerate(body) if w & 0xFFE0FC00 == 0x5E004000)
    bad = bytearray(image.data)
    bad[sha_pc - image.base + 4 * index + 1] ^= 0x10
    path = scratch / "wrong-sha256-round"
    path.write_bytes(bad)
    try:
        verify_sha2(Image(bad), path, 256)
    except ValueError as err:
        require(
            "register program differs" in str(err),
            f"unexpected SHA-2 mutation failure: {err}",
        )
    else:
        raise AssertionError("changed SHA-256 instruction passed")
    # Change a keygen wrapper's public-key buffer length while preserving a valid MOV.
    kg, body = image.function(b"10shake_128s6keygen", b"6slhdsa4sets")
    (j,) = [i for i, w in enumerate(body) if w == 0x52800406]
    bad = bytearray(image.data)
    bad[kg - image.base + 4 * j] ^= 0x20
    try:
        entry_certificate(Image(bad))
    except ValueError as err:
        require(
            "incorrect forwarded public arguments" in str(err),
            f"unexpected keygen mutation failure: {err}",
        )
    else:
        raise AssertionError("wrong keygen buffer size passed")
    # Change the top-layer guard from unsigned >= to >. This must add one recovery.
    ht, body = image.function(b"7ht_signKj10_EB6_", b"6slhdsa5shake2ht")
    (guard,) = [i for i, w in enumerate(body) if w & 0xFF00001F == 0x54000002]
    bad = bytearray(image.data)
    off = ht - image.base + 4 * guard
    bad[off] ^= 2 ^ 8
    path = scratch / "wrong-last-layer"
    path.write_bytes(bad)
    try:
        verify_hypertree(Image(bad), path)
    except ValueError as err:
        require(
            "incorrect XMSS call schedule" in str(err),
            f"unexpected mutation failure: {err}",
        )
    else:
        raise AssertionError("extra root recovery passed")


def release_consumer():
    output = subprocess.check_output(
        [
            "cargo",
            "test",
            "--release",
            "--locked",
            "--features",
            "platform-sha2",
            "--test",
            "acvp",
            "--no-run",
            "--message-format=json",
        ],
        cwd=ROOT / "rust",
        text=True,
    )
    messages = (json.loads(line) for line in output.splitlines())
    paths = [
        Path(m["executable"])
        for m in messages
        if m.get("executable") and m["target"]["name"] == "acvp"
    ]
    require(len(paths) == 1, "expected one linked ACVP consumer")
    return paths[0]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "binary",
        type=Path,
        nargs="?",
        help="linked Mach-O (default: build the release ACVP consumer)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="reject seventeen independent binary mutations",
    )
    parser.add_argument(
        "--certificate", type=Path, help="save the checked Lean certificate"
    )
    args = parser.parse_args()
    artifact = args.binary or release_consumer()
    require(
        args.certificate is None or artifact.resolve() != args.certificate.resolve(),
        "certificate would overwrite the executable",
    )
    data = artifact.read_bytes()
    image = Image(data)
    env = dict(
        os.environ,
        PATH=str(Path.home() / ".elan/bin") + os.pathsep + os.environ["PATH"],
    )
    subprocess.run(
        [
            "lake",
            "build",
            "Spec.ShakeWords",
            "Spec.ArmSha3Binary",
            "Spec.ArmSignReject",
            "Spec.ArmKeygen",
            "Spec.ArmInternalSigner",
            "Spec.ArmSha2InternalSigner",
            "Spec.ArmSegmentedFrame",
            "Spec.ArmVerifyLength",
            "Spec.ArmVerifyBody",
            "Spec.ArmRateBlocks",
            "Spec.SlhDsa",
        ],
        cwd=ROOT / "lean",
        env=env,
        check=True,
    )
    subprocess.run(
        ["lake", "build", "Rcarmcode.Proof", "Rcarmcode.Proof512"],
        cwd=ROOT / "lean-hw",
        env=env,
        check=True,
    )
    names = [
        "slhdsa.RcArmCode.execute_is_fips",
        "slhdsa.RcArmCode.S512.execute_is_fips",
    ]
    audit = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=ROOT / "lean-hw",
        env=env,
        input="import Rcarmcode.Proof\nimport Rcarmcode.Proof512\n"
        + "".join(f"#print axioms {n}\n" for n in names),
        text=True,
        stdout=subprocess.PIPE,
        check=True,
    )
    for name in names:
        require(
            f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            in audit.stdout,
            "unexpected SHA-2 axiom audit",
        )
    with tempfile.TemporaryDirectory() as folder:
        snapshot = Path(folder) / "release-image"
        snapshot.write_bytes(data)
        subprocess.run(
            ["lake", "env", "lean", "--stdin"],
            cwd=ROOT / "lean",
            env=env,
            input=entry_certificate(image)
            + pure_sign_certificate(image, snapshot).removeprefix(
                "import Spec.SlhDsa\n"
            ),
            text=True,
            check=True,
        )
        witnesses = {
            "AppleSignRejectWitness": rejection_certificate(image),
            "AppleKeygenWitness": keygen_certificate(image),
            "AppleVerifyLengthWitness": verify_length_certificate(image),
            "AppleVerifyBodyWitness": verify_body_certificate(image),
            "AppleSha2VerifyLengthWitness": sha2_verify_length(image),
            "AppleSha2VerifyWitness": sha2_verify_body(image),
            "AppleSegmentedFrameWitness": segmented_frame_certificate(image, snapshot),
            "ApplePureFrameWitness": pure_frame_certificate(image, snapshot),
            "ApplePureWrapperWitness": pure_wrapper_certificate(image),
            "AppleInternalSignerWitness": signer_certificate(image, snapshot, family="shake"),
            "AppleSha2InternalSignerWitness": signer_certificate(image, snapshot, family="sha2"),
        }
        # Session theorems import the checked-in words. Bind those imports to
        # the supplied image before using Lake's compiled proof artifacts.
        modules = []
        for name, witness in witnesses.items():
            if witness == (ROOT / "lean" / "Spec" / f"{name}.lean").read_text():
                modules.append(f"Spec.{name}")
            else:
                # Independently validate newly linked images without attributing
                # the checked-in image's composition theorem to the new build.
                print(f"{name} differs from checked-in image. Replaying new witness.", flush=True)
                subprocess.run(
                    ["lake", "env", "lean", "--stdin"], cwd=ROOT / "lean",
                    env=env, input=witness, text=True, check=True,
                )
        if modules:
            subprocess.run(["lake", "build", *modules], cwd=ROOT / "lean", env=env, check=True)
        if len(modules) == len(witnesses):
            print("All checked-in session witnesses match the supplied image.", flush=True)
        bulk_audit = subprocess.run(
            ["lake", "env", "lean", "--stdin"],
            cwd=ROOT / "lean",
            env=env,
            input=certificate(*decode_bulk(image), bulk=True),
            text=True,
            stdout=subprocess.PIPE,
            check=True,
        )
        for name in ("decoded_eq", "permutation_eq", "blocks_eq"):
            require(
                f"'LinkedArmBulk.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                in bulk_audit.stdout,
                "unexpected bulk Keccak axiom audit",
            )
        for bits in (256, 512):
            verify_sha2(image, snapshot, bits)
        verify_hypertree(image, snapshot)
        check(image, Path(folder), env, args.certificate)
        if args.self_test:
            mutation_tests(image, Path(folder), env)
            pure_sign_mutations(image, Path(folder))
            bulk_mutation_tests(image)
    if args.self_test:
        print("Rejected seventeen mutations in the linked image")
    print("Verified twelve internal SHAKE and SHA-2 signers across four allocator profiles and twelve mutations")
    print("Verified 24 SHAKE and SHA-2 keygen replays and seven negative keygen controls")
    print("Verified 36 public signing rejection paths and four negative instruction controls")
    print(
        "Verified valid pure-sign framing, randomness and result forwarding for all twelve sets, including SHA-2 segmented dispatch"
    )
    print("Verified all 36 keygen, internal signing and verification entry stubs")
    print("Verified the linked Arm hardware SHA-256 and SHA-512 compression routines")
    print(
        "Verified Apple arm64 two-state Keccak-f[1600], single-state wrapper and whole-rate-block absorb kernel"
    )
    print(
        "Verified direct SHAKE hypertree signer call order for all six standard parameter sets"
    )
    print("Artifact SHA-256", hashlib.sha256(data).hexdigest())
