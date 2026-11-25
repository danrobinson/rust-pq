#!/usr/bin/env python3
"""Check the live SHAKE WOTS signing/keygen helpers at both machine widths."""
from pathlib import Path
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-native-wots-recovery.py")))
facade, lean = shared["facade"], shared["lean"]
helpers = ["crate::shake::batch::" + name for name in ("fill_prf", "refill_short_inplace")]
program = lean / "Cachepath/NativeShakeWots/PackProgram.lean"


def representation(path):
    s = path.read_text()
    s = s[s.index("@[rust_loop_body]"):s.rindex("end slhdsa")]
    s = re.sub(r"/--[\s\S]*?-/", "", s)
    s = s.replace("shake.batch.", "").replace("MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter", "core.slice.Slice.iter_mut")
    return re.sub(r"\n\s*\n", "\n\n", s).strip()


def generic(three, eight):
    a, b = representation(three), representation(eight)
    if len(a) != len(b):
        raise ValueError("unexpected structural difference between SHAKE widths")
    out = []
    for i, (x, y) in enumerate(zip(a, b)):
        if x == y:
            out.append(x)
        elif (x, y) == ("3", "8") and a[i:].startswith("3#usize") and b[i:].startswith("8#usize"):
            out.append("machine.width")
        else:
            raise ValueError(f"unexpected width-specific operation at offset {i}")
    return "".join(out).replace("machine.width#usize", "machine.width")


model = lean / "Cachepath/NativeShakeWots/Program.lean"
callers = ["crate::shake::batch::" + op for op in ("sign", "keygen")]
cuts = shared["cuts"] + ["crate::shake::batch::extract_lane"]


def execution(package, width):
    # Aeneas occasionally wraps a declaration name across lines. Strip only
    # whitespace/comments and qualify the translated external primitives.
    body = (package / "Funs.lean").read_text()
    body = body[body.index("def shake.batch.keygen.closure_1.Insts"):body.rindex("end slhdsa")]
    types = (package / "Types.lean").read_text()
    types = types[types.index("@[reducible]"):types.rindex("end slhdsa")]
    text = re.sub(r"/--[\s\S]*?-/", "", types+"\n"+body)
    for old, new in (
        ("shake.batch.seed_words", "NativeVerify.seed_words"),
        ("shake.batch.adrs_words", "NativeVerify.adrs_words"),
        ("shake.batch.extract_lane", "NativeVerify.Wots.extract_lane"),
        ("shake.batch.sort_descending", "SORT_HELPER"),
        ("shake.batch.", ""),
        ("SORT_HELPER", "ShakeoptSort.shake.batch.sort_descending"),
        ("shake256.parallel.WIDTH", f"(ok {width}#usize : Result Usize)"),
        ("shake256.parallel.permute_active", "NativeVerify.Wots.Dispatch.permute"),
        ("shake256.Sponge.absorb", "stream.absorb"),
        ("shake256.Sponge", "stream.State"),
        ("shake.hash.start", "stream.start"), ("shake.hash.digest", "stream.digest"),
        ("MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter", "core.slice.Slice.iter_mut"),
        ("core.num.U32.swap_bytes", "ShakeBatch.core.num.U32.swap_bytes"),
    ):
        text = text.replace(old, new)
    expected = model.read_text().split("[stream : Stream]\n", 1)[1].split("\nend\n", 1)[0]
    return " ".join(text.split()), " ".join(expected.replace("machine.width",f"{width}#usize").split())


def main():
    facade["run"](["lake", "build", "Cachepath.NativeShakeWots.KeyEntry"], lean)
    facade["audit_theorems"]("Cachepath.NativeShakeWots.KeyEntry", ["slhdsa.NativeShakeWots." + thm for thm in
                             ("fill_layout", "refill_layout", "packed_fips", "chain_rounds", "prf_lanes", "keygen_spec")])
    with tempfile.TemporaryDirectory() as tmp:
        packages = []
        for i, target in enumerate(facade["TARGETS"]):
            d = Path(tmp) / target
            d.mkdir()
            pkg = facade["extract"]("rust", target, "Caller", d, callers, cuts)
            actual, expected = execution(pkg, 3 if i == 1 else 8)
            if actual != expected:
                raise ValueError(f"{target}: dynamic WOTS caller changed")
            if i in (1,2):
                packages.append(facade["extract"]("rust", target, "Pack", d, helpers, ["crate::shake256"]))
            print(f"{target}: matched complete native sign and keygen bodies", flush=True)
        expected = program.read_text().split("noncomputable section\n", 1)[1].split("\nend\n", 1)[0].strip()
        if expected != generic(*(p / "Funs.lean" for p in packages)):
            raise ValueError("extracted register helpers differ from the Lean program")
        cache = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
        d = Path(tmp) / "negative"
        d.mkdir()
        crate = cache["copy_rust_crate"](d)
        source = crate / "src/shake/batch.rs"
        text = source.read_text()
        # Change the WOTS keygen end step and the dynamic sign swap-remove
        # independently. Both modified function bodies must be rejected.
        for old, new in (("for step in 0..W - 1 {", "for step in 0..W - 2 {"),
                         ("lane_id[lane] = lane_id[active];", "lane_id[lane] = lane_id[0];")):
            if old not in text:
                raise ValueError("could not locate mutation")
            text = text.replace(old, new, 1)
        source.write_text(text)
        pkg = facade["extract"](crate, facade["TARGETS"][1], "Caller", d, callers, cuts)
        actual, expected = execution(pkg, 3)
        mark = "def sign.closure.Insts."
        a_key, a_sign = actual.split(mark, 1)
        e_key, e_sign = expected.split(mark, 1)
        if a_key == e_key or a_sign == e_sign:
            raise ValueError("keygen step-count or sign lane-owner mutation escaped detection")


if __name__ == "__main__":
    main()
