#!/usr/bin/env python3
"""Model-check the benchmark-locked RustCrypto WOTS+ implementation at all 12 concrete types."""
import argparse
import os
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

locked = runpy.run_path(str(Path(__file__).with_name("peer-lock.py")))
ROOT, common = locked["ROOT"], locked["common"]
SUITES = {family + "_" + str(bits) + mode: (ty + str(bits) + mode, bits // 8)
          for family, ty in (("sha2", "Sha2_"), ("shake", "Shake"))
          for bits in (128, 192, 256) for mode in ("s", "f")}


def prepare(path, name):
    locked["unpack"](path, "slh-dsa", "0.2.0-rc.5", add_dependency=("slhdsa", ROOT / "rust"))
    harness = (ROOT / "scripts/peer-wots/proof.rs").read_text()
    ty, n = SUITES[name]
    module = "proof_" + name
    # SHAKE's longest chain-harness helper inspects 32 address bytes. The
    # SHA-2 seeded constructor also initializes a complete SHA block.
    chain_unwind = 34 if name.startswith("shake_") else 150
    source = harness.replace("PEER_TYPE", ty).replace("PARAM_N", str(n))
    (path / "src" / (module + ".rs")).write_text(source.replace("CHAIN_UNWIND", str(chain_unwind)))
    common["append"](path / "src/wots.rs", f'#[cfg(kani)] #[path="{module}.rs"] pub(crate) mod {module};')
    # The three hash functions are the compositional cut. Intercept their concrete
    # impls because Kani cannot stub a trait declaration lacking a default body.
    family = name.split("_")[0]
    provider = path / "src/hashes" / (family + ".rs")
    hashes = provider.read_text()
    for fun, observer, args in (("f", "checked_f", "adrs, m"), ("t", "checked_t", "adrs, m"),
                                ("prf_sk", "checked_prf", "sk_seed, adrs")):
        pattern = r"(    fn " + fun + r"(?:<[^>]*>)?\([^{}]*?\) -> Array<u8, Self::N> \{)"
        cut = f"\n        #[cfg(kani)] return crate::wots::{module}::Observe::{observer}(self, {args});"
        hashes, matches = re.subn(pattern, lambda m: m[1]+cut, hashes)
        if matches != (1 if family == "shake" else 2):
            raise ValueError(f"unexpected {family} hash implementations for {fun}")
    provider.write_text(hashes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--set", choices=SUITES)
    parser.add_argument("--operation", choices=("chain", "keygen", "sign", "recover", "encoding"))
    args = parser.parse_args()
    env = os.environ.copy()
    env["RUSTFLAGS"] = (env.get("RUSTFLAGS", "") + ' --cfg sha2_backend="soft"').strip()
    command = ["cargo", "kani", "-Z", "stubbing", "--output-format", "terse"]
    if args.operation:
        command.extend(["--harness", "check_" + args.operation])
    for name in [args.set] if args.set else SUITES:
        with tempfile.TemporaryDirectory(prefix="peer-wots-"+name+"-") as d:
            p = Path(d)
            prepare(p, name)
            subprocess.run(command, cwd=p, env=env, check=True)


if __name__ == "__main__":
    main()
