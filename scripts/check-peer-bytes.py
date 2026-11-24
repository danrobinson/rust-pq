#!/usr/bin/env python3
"""Check FIPS address serialization and all concrete byte views used by the peer SHAKE suite."""
from pathlib import Path
import runpy
import subprocess
import tempfile

locked=runpy.run_path(str(Path(__file__).with_name("peer-lock.py")))

with tempfile.TemporaryDirectory(prefix="peer-shake-encoding-") as d:
    p=Path(d)
    locked["unpack"](p,"slh-dsa","0.2.0-rc.5")
    locked["common"]["append"](p / "src/address.rs", '#[cfg(kani)] #[path="encoding_proof.rs"] mod encoding_proof;')
    (p / "src/encoding_proof.rs").write_bytes((locked["ROOT"] / "scripts/peer-xof/bytes.rs").read_bytes())
    subprocess.run(["cargo","kani","--output-format","terse"],cwd=p,check=True)
