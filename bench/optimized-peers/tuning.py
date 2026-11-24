"""Time byte-checked baseline, tuned and peer drivers in a disposable directory."""

import csv
import os
import platform
import subprocess
import tempfile
from pathlib import Path

linux = platform.system() == "Linux"
providers = (
    ["old", "new1", "new", "fluhrer1", "fluhrer2"]
    if linux
    else ["old", "new", "opencl"]
)
with open("tuning.csv", "w", newline="") as f:
    out = csv.writer(f)
    out.writerow(["provider", "bytes", "set", "operation", "round", "ns"])
    for r in range(len(providers) + 1):
        start = max(0, r - 1)
        for length in (32, 1048576):
            with tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                rows = []
                for provider in providers[start:] + providers[:start]:
                    folder = root / provider
                    folder.mkdir()
                    cpus = "0,1" if provider in ("new", "fluhrer2") else "0"
                    cmd = ["taskset", "-c", cpus] if linux else []
                    if provider.startswith("fluhrer"):
                        args = ["./fluhrer", str(r), str(length), provider[-1]]
                    elif provider == "opencl":
                        args = ["./opencl", str(r), str(length)]
                    else:
                        binary = "new" if provider == "new1" else provider
                        args = ["./" + binary, str(r), str(length), "all"]
                    data = subprocess.check_output(
                        cmd + args,
                        text=True,
                        env=dict(os.environ, SLH_VECTORS=str(folder)),
                    )
                    sample = list(csv.reader(data.splitlines()))
                    count = 2 if provider == "opencl" else 12
                    assert (
                        len({(s, op) for s, op, _, _ in sample})
                        == len(sample)
                        == 5 * count
                    )
                    assert len(list(folder.iterdir())) == 4 * count
                    rows.extend([[provider, length, *x] for x in sample])
                for provider in providers[1:]:
                    for path in (root / provider).iterdir():
                        if path.read_bytes() != (root / "old" / path.name).read_bytes():
                            raise ValueError(f"{provider} {path.name} {r} {length}")
                out.writerows(rows)
                f.flush()
                print(f"validated {r} {length}", flush=True)
