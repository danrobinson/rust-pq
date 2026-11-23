"""Measure DER encoders/decoders and raw key import under balanced provider order."""
import csv
import hashlib
import itertools
import os
from pathlib import Path
import platform
import subprocess
import tempfile

providers = ("library", "openssl", "rustcrypto")
ops = {"secret_key_from", "public_key_from", "pkcs8_encode", "pkcs8_decode", "spki_encode", "spki_decode"}
sets = {f"{family}_{bits}{v}" for family in ("sha2", "shake") for bits in (128,192,256) for v in "sf"}
expected = set(itertools.product(sets, ops))
pin = ["taskset", "-c", "0"] if platform.system() == "Linux" else []
out = Path("out")
with (out / "encoding-samples.csv").open("w") as samples, (out / "encoding-checks.csv").open("w") as checks:
    rows = csv.writer(samples)
    rows.writerow(["provider", "set", "operation", "round", "ns"])
    digests = csv.writer(checks)
    digests.writerow(["round", "files_compared", "sha256"])
    for r, order in enumerate([providers] + list(itertools.permutations(providers))):
        reference = None
        for provider in order:
            cmd = ["./codecs-openssl", str(r)] if provider == "openssl" else ["./codecs-rust", str(r), provider]
            with tempfile.TemporaryDirectory() as tmp:
                csvdata = subprocess.check_output(pin + cmd, env=dict(os.environ, SLH_VECTORS=tmp), text=True)
                data = list(csv.reader(csvdata.splitlines()))
                if len(data) != len(expected) or {(s, op) for s, op, _, _ in data} != expected:
                    raise ValueError("incorrect rows from " + provider)
                for s, op, round_no, ns in data:
                    if int(round_no) != r or float(ns) <= 0:
                        raise ValueError("invalid timing")
                    rows.writerow([provider, s, op, r, ns])
                vectors = {p.name: p.read_bytes() for p in Path(tmp).iterdir()}
                if set(vectors) != {f"{s}.{ext}" for s in sets for ext in ("p8", "spki")}:
                    raise ValueError("incomplete DER outputs")
                if reference is not None and vectors != reference:
                    raise ValueError(f"{provider} differs on {[k for k in vectors if reference[k] != vectors[k]]}")
                reference = vectors
        digest = hashlib.sha256(b"".join(reference[k] for k in sorted(reference))).hexdigest()
        digests.writerow([r, len(reference), digest])
        checks.flush()
        samples.flush()
