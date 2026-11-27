#!/usr/bin/env python3
"""Differentially replay the five cache-private SHAKE leaves used by the assembly proof."""

import json
import os
import runpy
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE.parent / "rust/src"
body = runpy.run_path(str(HERE / "check-cache-build.py"))["body"]


def module(name, file):
    return f"#[path = {json.dumps(str(file))}] mod {name};\n"


def main():
    os.environ["PATH"] = (
        str(Path.home() / ".cargo/bin") + os.pathsep + os.environ["PATH"]
    )
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        shake256 = (SRC / "shake256.rs").read_text()
        # Broadcast the portable FIPS permutation lane by lane. Production
        # packing, lane selection, sponge code, and signature assembly run as written.
        shim = """
pub mod parallel {
    pub const WIDTH: usize = REPLAY_WIDTH;
    pub type States = [[u64; WIDTH]; 25];
    pub static ENABLED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
    pub fn available() -> bool { ENABLED.load(std::sync::atomic::Ordering::Relaxed) }
    pub fn permute(words: &mut States) {
        for lane in 0..WIDTH {
            let mut state = core::array::from_fn(|i| words[i][lane]);
            super::permute(&mut state);
            for i in 0..25 { words[i][lane] = state[i]; }
        }
    }
}
"""
        root = "extern crate alloc;\nmacro_rules! sha2_only { ($($tt:tt)*) => {} }\nmacro_rules! shake_only { ($($tt:tt)*) => {$($tt)*} }\n"
        for name in ("address", "params", "util", "xmss"):
            root += module(name, SRC / (name + ".rs"))
        for name in ("hash", "fors"):
            root += module(name, SRC / "shake" / (name + ".rs"))
        digits = body((SRC / "wots.rs").read_text(), "wots_digits")
        wots = (
            (SRC / "shake/wots.rs")
            .read_text()
            .replace(
                "use crate::wots::wots_digits;",
                "use crate::{util::base_2b, params::LG_W};",
            )
        )
        (folder / "wots.rs").write_text(wots + "\n" + digits)
        root += "mod wots; mod shake256;\n"
        cache = (SRC / "cache.rs").read_text().split("mod shake_ops {", 1)[1]
        private = cache[: cache.index("    fn fill_leaves_chunk")]
        root += "use address::{Adrs, FORS_TREE, TREE, WOTS_HASH}; use params::Params; use util::block;\n"
        root += (
            "mod cached {"
            + private
            + (HERE / "cache-proof/shake-leaves.rs").read_text()
            + "}\n"
        )
        root += 'fn main() { assert!(cfg!(any(all(target_arch="aarch64",target_endian="little"),all(target_arch="x86_64",target_feature="sse2"))));\n'
        for n in (16, 24, 32):
            for speed in ("S", "F"):
                root += f"cached::compare::<{n}>(&params::SHA2_{n * 8}{speed});\n"
        root += "}\n"
        (folder / "main.rs").write_text(root)
        for width in (3, 8):
            (folder / "shake256.rs").write_text(
                shake256 + shim.replace("REPLAY_WIDTH", str(width))
            )
            subprocess.run(
                [
                    "rustc",
                    "--edition=2021",
                    "-Awarnings",
                    "-O",
                    "-C",
                    "overflow-checks=yes",
                    "main.rs",
                ],
                cwd=folder,
                check=True,
            )
            subprocess.run([folder / "main"], check=True)
            print(
                f"Checked all six SHAKE sets with scalar and width-{width} cached primitives",
                flush=True,
            )


if __name__ == "__main__":
    main()
