#!/usr/bin/env python3
"""Run Aeneas on the full native SHAKE signing worker, leaving production Rust untouched."""

import argparse
import os
from pathlib import Path
import runpy
import subprocess
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
SIGN = "crate::shake::slh::parallel"
CUTS = [
    "crate::pool",
    "std::sync",
    "core::sync::atomic",
    "core::hint",
    "crate::util::base_2b",
    *("crate::shake::" + name for name in ("xmss", "wots", "fors", "hash", "batch")),
    SIGN + "::shake_fors_simd",
    SIGN + "::reduce_tree",
]


def lift_low_loop(path):
    rust = path.read_text()
    arm = rust.index("WorkKind::ForsTreeLow { tree: t, low_h } =>")
    start = rust.index("                    for j in 0..low_h {", arm)
    terminator = "\n                    }"
    end = rust.index(terminator, start) + len(terminator)
    loop = rust[start:end]
    call = "                    write_low_auth(sk,seed,fors_addr,t,a,idx,base,low_h,&fors_direct);"
    helper = """
fn write_low_auth<const N:usize>(sk:&[u8;N],seed:&Seed<N>,fors_addr:Adrs,t:u32,a:u32,
    idx:u32,base:usize,low_h:u32,fors_direct:&Vec<OnceLock<[u8;N]>>) {
"""
    path.write_text(
        rust[:start]
        + call
        + "\n" * loop.count("\n")
        + rust[end:]
        + helper
        + loop
        + "\n}\n"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--lift-low-loop",
        action="store_true",
        help="Move the scalar FORS low loop to a transparent helper in the temporary crate.",
    )
    args = parser.parse_args()
    os.environ["PATH"] = str(Path.home() / ".cargo/bin") + ":" + os.environ["PATH"]
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        crate = common["copy_rust_crate"](directory)
        if args.lift_low_loop:
            lift_low_loop(crate / "src/slh/parallel.rs")
        llbc = directory / "sign.llbc"
        subprocess.run(
            [
                common["CHARON"],
                "cargo",
                "--preset=aeneas",
                "--start-from",
                SIGN + "::sign",
                *(x for cut in CUTS for x in ("--opaque", cut)),
                "--include",
                "core::sync::atomic::Ordering",
                "--dest-file",
                llbc,
                "--",
                "--locked",
                "--features",
                "parallel,platform-sha2",
                "--target",
                "aarch64-apple-darwin",
            ],
            cwd=crate,
            check=True,
        )
        # Sequential traversal makes the first reported error independent of OCaml worker order.
        return subprocess.run(
            [
                common["AENEAS"],
                "-borrow-check",
                "-sequential",
                "-abort-on-error",
                "-no-progress-bar",
                llbc,
            ]
        ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
