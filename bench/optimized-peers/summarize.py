"""Summarize all seven validated sweeps; reject partial or duplicate results."""

import csv
import itertools
import statistics
import sys
from collections import defaultdict
from pathlib import Path

dest = Path(sys.argv[1])
hosts = {
    "apple": "Apple M5 Ultra",
    "c5": "Xeon 8275CL",
    "c5n": "Xeon 8124M",
    "c8i": "Xeon 6975P-C",
    "c8a": "EPYC 9R45",
    "c6g": "Graviton2",
    "c8g": "Graviton4",
}
ops = ["keygen", "public_key", "sign", "sign_hedged", "verify"]
sets = [
    f"{f}_{k}{z}"
    for f, k, z in itertools.product(["sha2", "shake"], [128, 192, 256], "sf")
]
summary = []
for host, label in hosts.items():
    for suffix, cached in [(".csv", False), ("-cached.csv", True)]:
        with (dest / "hosts" / (host + suffix)).open() as f:
            data = list(csv.DictReader(f))
        peers = ["formal", "botan", "experiments"]
        if host == "apple":
            peers.append("opencl")
        elif host not in {"c6g", "c8g"}:
            peers.extend(["fluhrer-1", "fluhrer-2"])
        rounds_count = len(peers)
        if cached:
            peers = ["formal", "cached"]
            rounds_count = 4
        values = {}
        for row in data:
            key = (
                row["provider"],
                row["set"],
                row["operation"],
                int(row["bytes"]),
                int(row["round"]),
            )
            if key in values:
                raise ValueError(f"duplicate {host} {key}")
            values[key] = float(row["ns"])
        expected = set()
        for peer in peers:
            for s, op, length in itertools.product(sets, ops, [32, 1048576]):
                if peer in {"experiments", "cached"} and "128" not in s:
                    continue
                if peer == "opencl" and s not in ["sha2_128s", "sha2_128f"]:
                    continue
                cell = (peer, s, op, length)
                rounds = range(1, rounds_count + 1)
                expected.update(cell + (r,) for r in range(rounds_count + 1))
                if peer == "formal":
                    continue
                formal = [values["formal", s, op, length, r] for r in rounds]
                other = [values[cell + (r,)] for r in rounds]
                ratios = [b / a for a, b in zip(formal, other)]
                summary.append(
                    {
                        "cpu": label,
                        "peer": peer,
                        "set": s,
                        "operation": op,
                        "message_bytes": length,
                        "rounds": rounds_count,
                        "formal_ns": statistics.median(formal),
                        "peer_ns": statistics.median(other),
                        "peer_over_formal": statistics.median(ratios),
                        "min_ratio": min(ratios),
                        "max_ratio": max(ratios),
                    }
                )
        if set(values) != expected:
            raise ValueError(f"incomplete or unexpected samples on {host}")

with (dest / "workloads.csv").open("w", newline="") as f:
    writer = csv.DictWriter(f, fieldnames=summary[0].keys())
    writer.writeheader()
    writer.writerows(summary)

groups = defaultdict(list)
for row in summary:
    groups[row["cpu"], row["peer"], row["operation"]].append(row["peer_over_formal"])
with (dest / "operations.csv").open("w", newline="") as f:
    writer = csv.writer(f)
    writer.writerow(
        [
            "cpu",
            "peer",
            "operation",
            "workloads",
            "formal_faster",
            "geomean_peer_over_formal",
        ]
    )
    for key, ratios in groups.items():
        writer.writerow(
            [
                *key,
                len(ratios),
                sum(r > 1 for r in ratios),
                statistics.geometric_mean(ratios),
            ]
        )
