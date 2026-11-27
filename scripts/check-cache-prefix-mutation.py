#!/usr/bin/env python3
"""Ensure the SHAKE cached signing theorem rejects putting PK.seed in the R field."""

import os
from pathlib import Path
import runpy
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
proof = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
ROOT, LEAN = proof["ROOT"], proof["LEAN"]


def main():
    os.environ["PATH"] = os.pathsep.join(
        [str(Path.home() / ".elan/bin"), str(Path.home() / ".cargo/bin"), os.environ["PATH"]]
    )
    # First check the positive proof, including all dependencies used below.
    subprocess.run(["lake", "build", "Cachepath.ShakeClosed"], cwd=LEAN, check=True)
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        crate = proof["copy_rust_crate"](folder)

        cache = crate / "src/cache.rs"
        source = cache.read_text()
        start = source.index("pub(super) fn sign_from_digest", source.index("mod shake_ops {"))
        end = source.index("fn sign_parallel", start)
        signer = source[start:end]
        correct = "sig.extend_from_slice(r);"
        if signer.count(correct) != 1:
            raise ValueError("expected one SHAKE serial signature prefix")
        cache.write_text(source[:start] + signer.replace(correct, "sig.extend_from_slice(pk_seed);") + source[end:])
        generated = proof["extract_target"]("aarch64-apple-darwin", folder, crate=crate)
        if (generated / "Funs.lean").read_bytes() == (LEAN / "Cacheops/Funs.lean").read_bytes():
            raise ValueError("mutating the signer did not change the extracted program")

        lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN, text=True).strip()
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(folder), lean_path]))

        def compile_module(src, dst):
            subprocess.run(["lean", "--root", folder, "-o", dst, src], env=env, cwd=LEAN, check=True)

        for module in ("TypesExternal", "FunsExternal"):
            shutil.copyfile(LEAN / "Cacheops" / (module + ".lean"), generated / (module + ".lean"))
        for module in ("TypesExternal", "Types", "FunsExternal", "Funs"):
            compile_module(generated / (module + ".lean"), generated / (module + ".olean"))

        # Rebuild each dependent proof in isolation against the mutated translation.
        proofs = folder / "Cachepath"
        shutil.copytree(LEAN / ".lake/build/lib/lean/Cachepath", proofs)
        for module in ("EndToEnd", "ShakeXmss", "ShakeScalarProgram", "ShakeScalar", "ShakeNode", "ShakeEndToEnd"):
            shutil.copyfile(LEAN / "Cachepath" / (module + ".lean"), proofs / (module + ".lean"))
            if module != "ShakeEndToEnd":
                compile_module(proofs / (module + ".lean"), proofs / (module + ".olean"))
        result = subprocess.run(["lean", "--root", folder, proofs / "ShakeEndToEnd.lean"],
                                env=env, cwd=LEAN, capture_output=True, text=True)
        diagnostics = result.stdout + result.stderr
        if not result.returncode or "bytes ↑pk_seed = bytes ↑r" not in diagnostics:
            raise ValueError("expected a failed equality between PK.seed and R\n" + diagnostics)
        # Check the single-root scalar extraction against the original, unmutated theorem
        # dependencies in a fresh module directory. Only the executable being compared changes.
        full = proof["extract_complete_signer"]("aarch64-apple-darwin", folder / "full", crate=crate)
        try:
            proof["check_complete_signer"](full, "mutated signer")
        except ValueError as exc:
            if "full signer cache.shake_ops.sign_from_digest differs" not in str(exc):
                raise
        else:
            raise ValueError("mutated scalar signer passed the full extraction check")
        linked = folder / "linked"
        bodies = proof["scalar_caller_program"](full)
        module = "ShakeClosedProgram"
        source = (LEAN / "Cachepath" / (module + ".lean")).read_text()
        for name, original in proof["linked_bodies"](source).items():
            source = source.replace(original, bodies[name])
        directory = linked / "Cachepath"
        shutil.copytree(LEAN / ".lake/build/lib/lean/Cachepath", directory)
        program = directory / (module + ".lean")
        program.write_text(source)
        full_env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(linked), lean_path]))
        subprocess.run(["lean", "--root", linked, "-o", directory / (module + ".olean"), program],
                       env=full_env, cwd=LEAN, check=True)
        result = subprocess.run(["lean", LEAN / "Cachepath/ShakeClosed.lean"],
                                env=full_env, cwd=LEAN, capture_output=True, text=True)
        diagnostics = result.stdout + result.stderr
        if not result.returncode or "error:" not in diagnostics or "extend_from_slice" not in diagnostics:
            raise ValueError("expected the complete scalar signature assembly equality to fail\n" + diagnostics)
        print("PK.seed/R mutation rejected by both the assembly proof and the fully linked scalar signer proof.")


if __name__ == "__main__":
    main()
