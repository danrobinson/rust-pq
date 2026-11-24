"""Run in the disposable build directory. Write validated, per-round timings."""

import csv
import itertools
import os
import platform
import subprocess
import sys
import tempfile
from pathlib import Path

linux = platform.system() == "Linux"
x86 = platform.machine() == "x86_64"
peers = ["formal", "botan", "experiments"]
if Path("peer-opencl").is_file():
    peers += ["opencl"]
if x86:
    peers += ["fluhrer-1", "fluhrer-2"]
cached = sys.argv[1:] == ["--cached"]
if cached:
    peers = ["formal", "cached"]
sets = {
    f"{family}_{level}{size}"
    for family, level, size in itertools.product(
        ["sha2", "shake"], [128, 192, 256], "sf"
    )
}
ops = {"keygen", "public_key", "sign", "sign_hedged", "verify"}


def run(peer, round_id, length, folder):
    groups = (
        sets
        if peer not in {"experiments", "cached"}
        else {s for s in sets if "128" in s}
    )
    if peer == "opencl":
        groups = {"sha2_128s", "sha2_128f"}
    binary = peer.split("-")[0]
    args = [f"./peer-{binary}", str(round_id), str(length)]
    if peer == "formal":
        args.append("all")
    elif binary == "fluhrer":
        args.append(peer[-1])
    if linux:
        args = [
            "taskset",
            "-c",
            "0,1" if peer in {"fluhrer-2", "cached"} else "0",
            *args,
        ]
    folder.mkdir()
    output = subprocess.check_output(
        args, env=dict(os.environ, SLH_VECTORS=str(folder)), text=True
    )
    rows = list(csv.reader(output.splitlines()))
    expected = set(itertools.product(groups, ops))
    assert len(rows) == len(expected) and {(s, op) for s, op, _, _ in rows} == expected
    assert all(int(r) == round_id and float(ns) > 0 for _, _, r, ns in rows)
    assert {f.name for f in folder.iterdir()} == {
        s + "." + ext for s in groups for ext in ("pk", "sk", "sig", "hedged")
    }
    return [[peer, length, *row] for row in rows]


with open("cached.csv" if cached else "samples.csv", "w", newline="") as f:
    out = csv.writer(f)
    out.writerow(["provider", "bytes", "set", "operation", "round", "ns"])
    for round_id in range((4 if cached else len(peers)) + 1):
        for length in [32, 1048576]:
            # One warm-up, then rotate each provider through every position.
            start = max(0, round_id - 1) % len(peers)
            order = peers[start:] + peers[:start]
            with tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                rows = []
                for peer in order:
                    rows.extend(run(peer, round_id, length, root / peer))
                for peer in peers[1:]:
                    for item in (root / peer).iterdir():
                        if (
                            item.read_bytes()
                            != (root / "formal" / item.name).read_bytes()
                        ):
                            raise ValueError(
                                f"byte mismatch {peer} {item.name}, round {round_id}, length {length}"
                            )
                out.writerows(rows)
                f.flush()
                print(f"validated round {round_id}, {length} bytes", flush=True)
