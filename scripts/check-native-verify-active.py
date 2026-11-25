#!/usr/bin/env python3
"""Compare the production partial-lane permutation dispatch with its checked host models."""
from pathlib import Path
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, decls, lean = shared["facade"], shared["decls"], shared["lean"]
module = "Cachepath.NativeVerify.Active"
root = "crate::shake256::parallel::permute_active"
cuts = ["crate::shake256::parallel::" + item for item in ("permute", "sha3::permute_active", "neon::permute_active")]
cuts += ["crate::sha512::hw::arm::available", "crate::sha256::x86::avx512_available"]


def check(target, scratch):
    raw = facade["extract"]("rust", target, "Active", scratch, [root], cuts)
    available, active = decls(raw / "Funs.lean", "slhdsa")
    apple = "apple" in target
    arm = "aarch64" in target
    width = 8 if apple or not arm else 3
    name = "Kldisp" if arm else "Kxdispatch"
    available = available.replace("shake256.parallel.available", "available")
    available = available.replace("sha256.x86.avx512_available", "GatherRust.sha256.x86.avx512_available")
    active = active.replace("shake256.parallel.available", "available")
    active = active.replace("def shake256.parallel.permute_active", "def active")
    if apple:
        active = active.replace("def active", "def active (sha3 : Bool)")
        active = active.replace("sha512.hw.arm.available", "ok sha3")
        for family, flag in (("sha3", "true"), ("neon", "false")):
            active = active.replace(f"shake256.parallel.{family}.permute_active words active",
                                    f"ok (AppleHybrid.packed ⟨min active.val 8,by omega⟩ {flag} words)")
        equation = "example (sha3 : Bool) : active sha3 = NativeVerify.appleActive sha3 := rfl"
    else:
        active = active.replace("shake256.parallel.permute words", name + ".machine.permute words")
        probe = name + "Rust.shake256.parallel.available"
        equation = f"example : active = NativeVerify.fullActive {name}.machine {probe} := rfl"
    header = f"import {module}\nopen Aeneas Aeneas.Std Result slhdsa\nnamespace Replay\nnoncomputable section"
    if f"Std.U64 {width}#usize" not in active:
        raise ValueError("unexpected target lane width")
    facade["run"](["lake", "env", "lean", "--stdin"], lean,
                  input="\n".join([header, available, active, equation, "end", "end Replay"]), text=True)
    print(f"{target}: identified the extracted dispatch by definitional equality", flush=True)


def check_words(target, scratch):
    roots = ["crate::shake::batch::seed_words", "crate::shake::batch::adrs_words",
             "crate::shake::fors_batch::word"]
    raw = facade["extract"]("rust", target, "Words", scratch, roots, [])
    base = (lean / "Shakebatch/Program.lean").read_text()
    program = (lean / "Cachepath/NativeVerify/WordsProgram.lean").read_text()
    for item in decls(raw / "Funs.lean", "slhdsa"):
        if item.startswith(("def shake.batch.word", "def shake.fors_batch.word")):
            if item.replace("shake.fors_batch.word", "shake.batch.word") not in base:
                raise ValueError(f"{target}: changed little-endian word load")
        else:
            item = item.replace("shake.batch.word", "ShakeBatch.shake.batch.word")
            for name in ("seed_words", "adrs_words"):
                item = item.replace("shake.batch." + name, name)
            item = item.replace("core.num.U32.swap_bytes", "ShakeBatch.core.num.U32.swap_bytes")
            item = item.replace("core.num.U64.swap_bytes", "swap64")
            if item not in program:
                raise ValueError(f"{target}: unmatched verifier word packing: {item}")
    print(f"{target}: matched seed and address packing and both byte loaders", flush=True)


if __name__ == "__main__":
    facade["run"](["lake", "build", module, "Cachepath.NativeVerify.Words"], lean)
    for target in facade["TARGETS"]:
        with tempfile.TemporaryDirectory() as tmp:
            check(target, Path(tmp))
            check_words(target, Path(tmp))
    facade["audit_theorems"](module, ["slhdsa.NativeVerify." + name for name in ("apple", "linux", "x86")])
    facade["audit_theorems"]("Cachepath.NativeVerify.Words", ["slhdsa.NativeVerify.seed_spec", "slhdsa.NativeVerify.address_spec"])
