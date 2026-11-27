#!/usr/bin/env python3
"""Match batch verification callbacks and all named caller parameters on three targets."""
from pathlib import Path
import os
import re
import runpy
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
facade = common["facade"]
root = common["ROOT"]
lean = root / "lean-hw"
shapes = ("128s", "128f", "192s", "192f", "256s", "256f")
targets = ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu")


def tokens(source):
    return re.findall(r"\w+|[^\w\s]", source)


read_decls = runpy.run_path(str(Path(__file__).with_name("check-cache-mutation.py")))["decls"]


def decls(file, namespace="CacheopsRust"):
    return [" ".join(d[d.index("def "):].split()) if d.startswith("@[") and "def " in d
            else " ".join(re.sub(r"^@\[[^]]+\]\s*", "", d).split()) for d in read_decls(file, namespace)]


def check(pkg):
    calls = decls(pkg / "Funs.lean")
    model = (lean / "Parallel/BatchItem.lean").read_text()
    item_type = model.split("structure Item where", 1)[1].split("instance", 1)[0]
    if not any(tokens(d) == tokens("structure batch_api.VerifyItem where " + item_type) for d in decls(pkg / "Types.lean")):
        raise ValueError("verification item layout changed")
    expected = model.split("Result Bool := do", 1)[1].split("def verdict", 1)[0]
    for family in ("sha2", "shake"):
        for tag in ("", "all_"):
            generic = "batch_api.verify_batch_" + tag + family
            closure = generic + ".closure.Insts.CoreOpsFunctionFnTupleShared1VerifyItemBool"
            (callback,) = (d for d in calls if d.startswith("def " + closure + ".call "))
            body = callback.split(":= do", 1)[1]
            callee = ("shake." if family == "shake" else "") + "api.verify"
            if tokens(body) != tokens(expected.replace("Suite.verify family", callee)):
                raise ValueError(f"incorrect key check or verifier arguments in {generic}")
            (caller,) = (d for d in calls if d.startswith("def " + generic + " "))
            worker = "batch_api.verify_batch_" + tag + "with"
            if tokens(caller.split(":= do")[1]) != tokens(f"{worker} ({closure} N) items p"):
                raise ValueError(f"incorrect scheduler or closure in {generic}")
            if not any(tokens("call := " + closure + ".call }") == tokens(d)[-len(tokens("call := " + closure + ".call }")):]
                       for d in calls if d.startswith("def " + closure + " ")):
                raise ValueError(f"incorrect Fn.call instance in {generic}")
            for shape in shapes:
                set_name = family + "_" + shape
                entry = "batch_api.verify_" + tag + set_name
                (named,) = (d for d in calls if d.startswith("def " + entry + " "))
                argument = f"sets.{set_name}.params.PARAMS"
                if tokens(named.split(":= do")[1]) != tokens(f"{generic} {int(shape[:3])//8}#usize {argument} items"):
                    raise ValueError(f"incorrect width or parameter at {entry}")
                if not any(d == f"def {argument} : params.Params := params.SHA2_{shape.upper()}" for d in calls):
                    raise ValueError(f"incorrect parameter value at {entry}")
    constants = set(decls(root / "lean/Slhdsa/Funs.lean", "slhdsa"))
    if any(d not in constants for d in calls if d.startswith("def params.SHA2_")):
        raise ValueError("parameter fields changed")


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    starts = ["crate::batch_api::verify_" + tag + family + "_" + shape for tag in ("", "all_")
              for family in ("sha2", "shake") for shape in shapes]
    cuts = ["crate::batch_api::verify_batch_with", "crate::batch_api::verify_batch_all_with",
            "crate::api::verify", "crate::shake::api::verify"]
    with tempfile.TemporaryDirectory() as tmp:
        for target in targets:
            pkg = common["extract_target"](target, Path(tmp)/target, starts, cuts, features="parallel,platform-sha2")
            check(pkg)
            file = pkg / "Funs.lean"
            code = file.read_text()
            file.write_text(code.replace("tupled_args.sig tupled_args.ctx", "tupled_args.msg tupled_args.ctx", 1))
            try:
                check(pkg)
            except ValueError:
                pass
            else:
                raise ValueError("accepted a verifier called with the message as signature")
    module = "Parallel.BatchItem"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](module, ["slhdsa.ParallelBatchItem." + n for n in ("item_spec", "each", "all")])
    print("Matched all 24 batch verification entry points and four item callbacks on all three targets.")


if __name__ == "__main__":
    main()
