#!/usr/bin/env python3
"""Source-check the dynamic SHAKE verifier WOTS scheduling and lane extraction on every host."""
from pathlib import Path
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, lean, decls = shared["facade"], shared["lean"], shared["decls"]
program = lean / "Cachepath/NativeVerify/WotsProgram.lean"
roots = ["crate::shake::batch::recover", "crate::shake::batch::extract_lane"]
cuts = ["crate::shake::batch::" + f for f in ("seed_words", "adrs_words", "sort_descending", "word")]
cuts += ["crate::shake256", "crate::shake::hash", "crate::util::block"]


def normalize(item):
    return " ".join(item.split())


def models(width):
    text = program.read_text()
    for proof, source in (
        ("ok machine.width", "shake256.parallel.WIDTH"), ("machine.width", f"{width}#usize"),
        ("stream.State", "shake256.Sponge"), ("stream.start", "shake.hash.start"),
        ("stream.digest", "shake.hash.digest"), ("stream.absorb", "shake256.Sponge.absorb"),
        ("NativeVerify.", "shake.batch."), ("ShakeBatch.shake.batch.word", "shake.batch.word"),
        ("ShakeoptSort.shake.batch.", "shake.batch."), ("Dispatch.permute", "shake256.parallel.permute_active"),
        ("core.slice.Slice.iter_mut", "MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter"),
    ):
        text = text.replace(proof, source)
    text = re.sub(r"(?<![\w.])((?:recover|extract_lane)[\w.]*)", r"shake.batch.\1", text)
    return {m[1]: normalize(m[0]) for m in re.finditer(
        r"^def (shake\.batch\.[\w.]+)\b[\s\S]*?(?=\n\s*\n|\nend\b|\Z)", text, re.M)}


def validate(package, target):
    expected = models(3 if target == "aarch64-unknown-linux-gnu" else 8)
    known = set(decls(lean.parent / "lean/Slhdsa/Funs.lean", "slhdsa"))
    for item in decls(package / "Funs.lean", "slhdsa"):
        if item in known:
            continue
        match = re.search(r"\bdef (shake\.batch\.[\w.]+)", item)
        if not match or normalize(item[item.index("def "):]) != expected.pop(match[1], None):
            raise ValueError(f"{target}: unmatched dynamic WOTS declaration: {item}")
    if expected:
        raise ValueError(f"{target}: missing native WOTS declarations: {sorted(expected)}")
    template = (package / "FunsExternal_Template.lean").read_text()
    externals = set(re.findall(r"^axiom ([\w.]+)", template, re.M))
    cutpoints = {"core.num.U32.swap_bytes", "MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter",
                 "shake.batch.word", "shake.batch.seed_words", "shake.batch.adrs_words", "shake.batch.sort_descending",
                 "util.block", "shake256.Sponge.absorb", "shake256.parallel.permute_active", "shake256.parallel.WIDTH",
                 "shake.hash.digest", "shake.hash.start"}
    if externals != cutpoints:
        raise ValueError(f"{target}: unexpected WOTS cutpoint difference: {externals ^ cutpoints}")
    print(f"{target}: matched every WOTS recovery and lane extraction loop", flush=True)


if __name__ == "__main__":
    for target in facade["TARGETS"]:
        with tempfile.TemporaryDirectory() as tmp:
            validate(facade["extract"]("rust", target, "Wots", Path(tmp), roots, cuts), target)
    facade["run"](["lake", "build", "Cachepath.NativeVerify.WotsOutput",
                   "Cachepath.NativeVerify.WotsPrepare", "Cachepath.NativeVerify.WotsInit",
                   "Cachepath.NativeVerify.WotsCompact"], lean)
