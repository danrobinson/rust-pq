#!/usr/bin/env python3
"""Check RustCrypto SHAKE256's rate block, padding, initial state and squeeze mapping."""
from pathlib import Path
import runpy
import subprocess
import tempfile

locked = runpy.run_path(str(Path(__file__).with_name("peer-lock.py")))
ROOT = locked["ROOT"]


def main():
    with tempfile.TemporaryDirectory(prefix="peer-shake-xof-") as d:
        p = Path(d)
        locked["unpack"](p, "sha3", "0.11.0")
        lib = p / "src/lib.rs"
        # The observer needs shared ghost state across the fn-pointer ABI.
        if lib.read_text().count("#![forbid(unsafe_code)]") != 1:
            raise ValueError("unexpected SHA3 crate attributes")
        lib.write_text(lib.read_text().replace("#![forbid(unsafe_code)]", "#![cfg_attr(not(kani), forbid(unsafe_code))]"))
        api = p / "src/block_api.rs"
        code = api.read_text()
        # The checked permutation is the only computational cut. Keep each
        # closure and its capture, argument and return values unchanged.
        entry = "self.keccak.with_f1600("
        if code.count(entry) != 4:
            raise ValueError("SHA3 permutation call graph changed")
        api.write_text(code.replace(entry, "peer_proof::select(") + '\n#[cfg(kani)] #[path="peer_proof.rs"] mod peer_proof;\n')
        (api.parent / "peer_proof.rs").write_bytes((ROOT / "scripts/peer-xof/core.rs").read_bytes())
        subprocess.run(["cargo", "kani", "--output-format", "terse"], cwd=p, check=True)


if __name__ == "__main__":
    main()
