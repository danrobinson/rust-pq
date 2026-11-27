#!/usr/bin/env python3
"""Bind the complete Aeneas width-eight fused XMSS caller to Apple and x86 Rust."""
from pathlib import Path
import re
import runpy
import tempfile

wots = runpy.run_path(str(Path(__file__).with_name("check-native-shake-signing.py")))
facade, lean = wots["facade"], wots["lean"]
roots = ["crate::shake::batch::xmss_sign_batch"]
cuts = wots["cuts"] + ["crate::shake::batch::" + n for n in (
    "sign", "xmss_subtree_fallback", "xmss_subtree", "pair_active", "fill_prf", "refill_short_inplace")]
names = {
    "shake.batch.xmss_sign_batch": "xmss_sign_batch",
    "shake.batch.read_active": "NativeVerify.ActiveHash.read_active",
    "shake.batch.seed_words": "NativeVerify.seed_words",
    "shake.batch.adrs_words": "NativeVerify.adrs_words",
    "shake.batch.extract_lane": "NativeVerify.Wots.extract_lane",
    "shake.batch.pair_active": "(NativeVerify.ActiveHash.pair_active kernel.active)",
    "shake.batch.fill_prf": "NativeShakeWots.fill_prf",
    "shake.batch.refill_short_inplace": "NativeShakeWots.refill_short_inplace",
    "shake.batch.xmss_subtree_fallback": "kernel.fallback",
    "shake.batch.xmss_subtree": "kernel.subtree",
    "shake.batch.sign": "kernel.narrowSign",
    "shake256.parallel.WIDTH": "(ok 8#usize : Result Usize)",
    "shake256.parallel.permute": "kernel.permute",
    "core.num.U32.swap_bytes": "ShakeBatch.core.num.U32.swap_bytes",
}


def check_model(pkg):
    types = (pkg / "Types.lean").read_text()
    body = (pkg / "Funs.lean").read_text()
    raw = types[types.index("@[reducible]"):types.rindex("end slhdsa")] + "\n" + body[
        body.index("def\n  shake.batch.xmss_sign_batch.closure_2.Insts"):body.rindex("end slhdsa")]
    raw = re.sub(r"/--[\s\S]*?-/", "", raw)
    for old, new in names.items():
        raw = raw.replace(old, new)
    model = (lean / "Fused/Program.lean").read_text()
    model = model[model.index("@[reducible]"):model.rindex("end slhdsa.Fused")]
    if raw.split() != model.split():
        raise ValueError("complete width-eight fused XMSS body differs from the checked Aeneas program")


def main():
    facade["run"](["lake", "build", "Fused.Entry"], lean)
    facade["audit_theorems"]("Fused.Entry", ["slhdsa.Fused.raw_eq", "slhdsa.Fused.sign_spec"])
    with tempfile.TemporaryDirectory() as tmp:
        for target in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu"):
            dst = Path(tmp) / target
            dst.mkdir()
            package = facade["extract"]("rust", target, "Exact", dst, roots, cuts)
            check_model(package)
            body = package / "Funs.lean"
            text = body.read_text()
            if text.count("if i4 = d") != 1:
                raise ValueError("expected one digit capture comparison")
            body.write_text(text.replace("if i4 = d", "if step = d"))
            try:
                check_model(package)
            except ValueError:
                continue
            raise ValueError("accepted a changed capture in the extracted fused caller")
    print("Matched both complete width-eight fused XMSS bodies and rejected shifted captures.")


if __name__ == "__main__":
    main()
