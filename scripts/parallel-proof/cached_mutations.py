"""Negative controls for production cached signing. Mutate temporary source only."""

import subprocess
import tempfile
from pathlib import Path

from build import SRC
from signer import probe_source


def change(cache, family, target, before, after):
    header = {"sha2": "mod sha2_ops {", "shake": "mod shake_ops {", "shared": ""}[family]
    start = cache.index(target, cache.index(header))
    start = cache.index(before, start)
    return cache[:start] + cache[start:].replace(before, after, 1)


def main():
    original = (SRC / "cache.rs").read_text()
    # The runner checks both compilation and the specific runtime failure.
    cases = [
        ("SHA2 ticket stride", "sha2", "fn sign_parallel", "next.fetch_add(1", "next.fetch_add(2", "cached worker ticket or join changed"),
        ("SHA2 sibling", "sha2", "fn sign_parallel", "(idx >> h) ^ 1", "(idx >> h) ^ 0", "cached symbolic signature differs"),
        ("SHA2 cached root", "sha2", "fn sign_parallel", "tree_root(d2_tree)", "tree_root(top_tree)", "cached symbolic signature differs"),
        ("SHAKE grouped lane", "shake", "fn sign_parallel", "set(vals[lane])", "set(vals[0])", "cached symbolic signature differs"),
        ("SHAKE scalar sibling", "shake", "fn sign_parallel", "(idx >> height) ^ 1", "(idx >> height) ^ 0", "cached symbolic signature differs"),
        ("SHAKE group recursion", "shake", "fn fors_nodes<", "i * 2 + 1", "i * 2 + 0", "grouped FORS recurrence"),
        ("SHAKE sponge layout", "shake", "fn pair<", "2 * N / 8 + 4", "N / 8 + 4", "SHAKE cached lane preimage or output bytes"),
        ("cache path offset", "shared", "fn append_auth_path", "(leaf >> h) ^ 1", "(leaf >> h) ^ 0", "cached auth-path byte offset"),
    ]
    with tempfile.TemporaryDirectory() as tmp:
        source, exe = Path(tmp, "mutant.rs"), Path(tmp, "mutant")
        for label, family, target, before, after, error in cases:
            cache = change(original, family, target, before, after)
            try:
                probe = probe_source(cache)
            except ValueError as rejected:
                if str(rejected) != error:
                    raise
            else:
                source.write_text(probe.replace("PROOF_WIDTH", "3"))
                subprocess.run(["rustc", "--cfg", "proof_simd", "--edition=2021", "-Awarnings", "-C", "overflow-checks=yes",
                                source, "-o", exe], check=True)
                result = subprocess.run([exe], capture_output=True, text=True, timeout=45)
                if result.returncode == 0 or error not in result.stderr:
                    raise AssertionError(f"{label}: expected {error!r}, got {result.stderr[:500]}")
            print(f"rejected {label}", flush=True)


if __name__ == "__main__":
    main()
