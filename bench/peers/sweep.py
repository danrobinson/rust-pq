"""Run all providers on paired inputs and compare complete wire representations."""
import csv
import hashlib
import itertools
import os
from pathlib import Path
import platform
import subprocess
import tempfile

providers = ("library", "openssl", "rustcrypto")
sets = {f"{family}_{n}{variant}" for family in ("sha2", "shake")
        for n in (128, 192, 256) for variant in "sf"}
operations = {"keygen", "public_key", "sign", "sign_hedged", "verify"}
expected = set(itertools.product(sets, operations))
orders = [providers] + list(itertools.permutations(providers))
pin = ["taskset", "-c", "0"] if platform.system() == "Linux" else []
out = Path("out")
with (out / "samples.csv").open("w") as samples, (out / "checks.csv").open("w") as checks:
    raw = csv.writer(samples)
    raw.writerow(["provider", "bytes", "set", "operation", "round", "ns"])
    validated = csv.writer(checks)
    validated.writerow(["bytes", "round", "files_compared", "sha256"])
    for round_no, order in enumerate(orders):
        for length in (32, 1048576):
            reference = None
            for provider in order:
                command = (["./peer-openssl"] if provider == "openssl" else ["./peer-rust"])
                command += [str(round_no), str(length)]
                if provider != "openssl":
                    command += ["all"]
                if provider == "rustcrypto":
                    command += ["rustcrypto"]
                with tempfile.TemporaryDirectory() as tmp:
                    data = subprocess.check_output(pin + command, text=True,
                                                  env=dict(os.environ, SLH_VECTORS=tmp))
                    rows = list(csv.reader(data.splitlines()))
                    if len(rows) != len(expected) or {(s, op) for s, op, _, _ in rows} != expected:
                        raise ValueError("wrong benchmark rows")
                    for s, op, r, ns in rows:
                        if int(r) != round_no or float(ns) <= 0:
                            raise ValueError("invalid timing")
                        raw.writerow([provider, length, s, op, r, ns])
                    samples.flush()
                    vectors = {p.name: p.read_bytes() for p in Path(tmp).iterdir()}
                    if set(vectors) != {f"{s}.{ext}" for s in sets for ext in ("sk","pk","sig","hedged")}:
                        raise ValueError("missing interop output")
                    if reference is not None:
                        mismatch = [name for name in vectors if vectors[name] != reference[name]]
                        if mismatch:
                            raise ValueError(f"{provider} disagrees on {mismatch}")
                    else:
                        reference = vectors
                print(round_no, length, provider, flush=True)
            digest = hashlib.sha256(b"".join(reference[name] for name in sorted(reference))).hexdigest()
            validated.writerow([length, round_no, len(reference), digest])
            checks.flush()
