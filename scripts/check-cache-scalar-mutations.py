#!/usr/bin/env python3
"""Check that five independent changes to the SHAKE scalar cache callers break their Lean proofs."""
import os
from pathlib import Path
import re
import runpy
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
proof = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
LEAN = proof["LEAN"]
MUTATIONS = (
    ("wots_pk_gen_portable", "W - 1,", "W - 2,", "keygen_loop"),
    ("wots_sign", "let digits = wots_digits(msg);", "let digits = wots_digits(sk);", "wots_sign_eq"),
    ("wots_pk_from_sig", "W - 1,", "W - 2,", "wots_pk_from_sig_loop"),
    ("fors_sign", "let s = (idx >> j) ^ 1;", "let s = (idx >> j) ^ 0;", "fors_path"),
    ("fors_pk_from_sig", "offset + 1, p.a", "offset + 2, p.a", "fors_pk_from_sig_loop"),
)


def mutate(crate):
    path = crate / "src/cache.rs"
    source = path.read_text()
    module = source.index("mod shake_ops {")
    for name, old, new, _ in MUTATIONS:
        start = source.index(f"\n    fn {name}<", module)
        end = source.index("\n    }", start)
        body = source[start:end]
        if body.count(old) != 1:
            raise ValueError(f"expected one mutation site in shake_ops::{name}")
        source = source[:start] + body.replace(old, new) + source[end:]
    path.write_text(source)


def failed_theorems(source, output):
    names = set()
    lines = source.read_text().splitlines()
    for line in re.findall(r"ShakeScalar\.lean:(\d+):\d+: error:", output):
        for previous in reversed(lines[:int(line)]):
            match = re.match(r"(?:private )?theorem (\w+)", previous)
            if match:
                names.add(match[1])
                break
    return names


def main():
    subprocess.run(["lake", "build", "Cachepath.ShakeScalar"], cwd=LEAN, check=True)
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        crate = proof["copy_rust_crate"](folder)
        mutate(crate)
        package = proof["extract_scalar_callers"]("aarch64-apple-darwin", folder / "scalar", crate=crate)
        try:
            proof["check_scalar_callers"](package)
        except ValueError as exc:
            if "program differs" not in str(exc):
                raise
        else:
            raise ValueError("mutated production extraction matched the verified program")

        # Compile the changed bodies with precisely the same type and primitive bindings.
        modules = folder / "Cachepath"
        shutil.copytree(LEAN / ".lake/build/lib/lean/Cachepath", modules)
        lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN, text=True).strip()
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(folder), lean_path]))
        original = (LEAN / "Cachepath/ShakeScalarProgram.lean").read_text()
        bindings = original[:original.index("@[rust_loop_body]")]
        bodies = proof["scalar_caller_program"](package)
        program = modules / "ShakeScalarProgram.lean"
        program.write_text(bindings + "\n\n".join(bodies.values()) + "\n\nend slhdsa.CacheScalar\n")
        subprocess.run(["lean", "--root", folder, "-o", modules / "ShakeScalarProgram.olean", program],
                       env=env, cwd=LEAN, check=True)

        source = LEAN / "Cachepath/ShakeScalar.lean"
        result = subprocess.run(["lean", source], env=env, cwd=LEAN, capture_output=True, text=True)
        diagnostics = result.stdout + result.stderr
        rejected = failed_theorems(source, diagnostics)
        expected = {theorem for _, _, _, theorem in MUTATIONS}
        if not result.returncode or not expected.issubset(rejected):
            raise ValueError(f"expected failures in {sorted(expected)}, found {sorted(rejected)}\n{diagnostics}")
        print(f"Regenerated SHAKE scalar cache mutations rejected in {', '.join(sorted(expected))}.")


if __name__ == "__main__":
    main()
