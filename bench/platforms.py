#!/usr/bin/env python3
"""Benchmark the six parameter sets. On Linux use taskset -c 0 to pin the run."""
import argparse
import csv
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

CRATE = Path(__file__).resolve().parents[1] / "rust"


def build(features, flags):
    cmd = ["cargo", "bench", "--locked", "--bench", "platforms", "--no-run",
           "--message-format=json-render-diagnostics"]
    if features:
        cmd.extend(["--features", features])
    result = subprocess.run(cmd, cwd=CRATE, env={**os.environ, "RUSTFLAGS": flags},
                            stdout=subprocess.PIPE, text=True, check=True)
    for line in result.stdout.splitlines():
        artifact = json.loads(line)
        if artifact.get("executable") and artifact["target"]["name"] == "platforms":
            return artifact["executable"]
    raise RuntimeError("Cargo produced no platforms benchmark executable")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rounds", type=int, choices=range(1, 256), metavar="1..255", default=6)
    parser.add_argument("--native", action="store_true", help="also try host-specific code generation")
    parser.add_argument("--family", choices=("sha2", "shake", "all"), default="all")
    args = parser.parse_args()
    flags = os.environ.get("RUSTFLAGS", "")
    print(platform.platform(), subprocess.check_output(["rustc", "-vV"], text=True),
          f"RUSTFLAGS={flags!r}", file=sys.stderr)
    portable = build("", flags)
    accelerated = build("platform-sha2", flags)
    modes = [("portable", portable), ("platform", accelerated), ("rustcrypto", accelerated)]
    if args.native:
        modes.append(("native", build("platform-sha2", flags + " -C target-cpu=native")))
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(["message_bytes", "build", "set", "operation", "round", "ns_per_op"])
    for r in range(args.rounds + 1):  # Round zero warms every configuration.
        for length in (32, 1048576):
            for i in range(len(modes)):
                mode, exe = modes[(i + r) % len(modes)]
                cmd = [exe, str(r), str(length), args.family]
                if mode == "rustcrypto":
                    cmd.append("rustcrypto")
                sample = subprocess.check_output(cmd, cwd=CRATE, text=True)
                for row in csv.reader(sample.splitlines()):
                    writer.writerow([length, mode, *row])
                sys.stdout.flush()


if __name__ == "__main__":
    main()
