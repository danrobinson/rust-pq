#!/usr/bin/env python3
"""Replay the physical SHAKE signer publications on the eight-lane schedule."""
import os
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

here = Path(__file__).resolve().parent
shared = runpy.run_path(str(here / "check-parallel-sign-join.py"))
ticket = runpy.run_path(str(here / "check-parallel-wots-ticket.py"))
caller = runpy.run_path(str(here / "check-uncached-parallel-caller.py"))
facade, lean = shared["facade"], shared["lean"]
targets = ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu")


def expanded_worker(path, target):
    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    result = subprocess.check_output(["rustc", "--edition=2021", "--cfg", "proof_simd",
        "-Awarnings", "--target", target, "-Zunpretty=expanded", path], env=env, text=True)
    production = result.split("pub mod production {", 1)[1]
    match = re.search(r"^( +)pub\(crate\) fn sign<", production, re.M)
    if not match:
        raise ValueError("expanded parallel worker not found")
    end = production.index("\n" + match[1] + "}", match.end())
    return production[match.start():end]


def sources(folder):
    physical = shared["table"](shared["symbolic_slots"](folder, 8))
    if physical != (lean / "Parallel/SignJoinTable.lean").read_text():
        raise ValueError("compiled width-eight publications changed")
    path = folder / "observed.rs"
    apple, x86 = [expanded_worker(path, target) for target in targets]
    if apple != x86:
        raise ValueError("target expansions of the symbolic SHAKE worker differ")
    for target in targets:
        out = folder / target
        out.mkdir()
        caller["check"](target, out / "caller")
        if shared["program"](shared["extract"](out, target)) != shared["dest"].read_text():
            raise ValueError(f"{target} worker guard or post-join assembly differs")
        ticket_folder = out / "ticket"
        ticket_folder.mkdir()
        translated = ticket["program"](ticket["extract"](ticket_folder, target), wide=True)
        if translated.split() != (lean / "Parallel/WidthEightTicketProgram.lean").read_text().split():
            raise ValueError(f"{target} phase-two ticket, address or WOTS dispatch differs")
    print("Matched all 24 eight-lane physical publication runs, both target expansions, both extracted public callers and both post-join loops.", flush=True)


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    with tempfile.TemporaryDirectory() as tmp:
        sources(Path(tmp))
    audit_public()


def audit_public():
    module = "Parallel.WidthEightCoverage"
    facade["run"](["lake", "build", module], lean)
    roots = [f"Parallel{host}API.shake_{bits}{speed}.{op}" for host in ("Apple","X86")
        for bits in (128,192,256) for speed in ("s","f") for op in
        ("slh_sign_internal_spec","slh_sign_spec","sign_spec","sign_deterministic_spec","roundtrip")]
    roots += [f"{host}.slhdsa.WidthEight.ParallelSign.{path}_uses_worker"
              for host in ("ParallelApple","ParallelX86") for path in ("internal","context")]
    ticket_module = "Parallel.WidthEightTicketHosted"
    facade["run"](["lake","build",ticket_module], lean)
    facade["audit_theorems"](ticket_module, [f"{host}.slhdsa.WidthEight.Ticket.{op}"
        for host in ("TicketApple","TicketX86") for op in ("published","from_layers")])
    facade["audit_theorems"](module, roots + ["slhdsa.ParallelSignJoin.enabled_returns","slhdsa.ParallelSignJoin.uses_some"])
    print(f"Checked {len(roots)} hosted parallel signing theorems and the successful worker branch.", flush=True)


if __name__ == "__main__":
    main()
