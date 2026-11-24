"""Rebuild the comparisons for the workloads where the original benchmark lost."""

import csv
import itertools
import statistics
import sys
from pathlib import Path

destination = Path(sys.argv[1])
original = destination.parent / "optimized-competitors" / "workloads.csv"
machines = {
    "apple": "Apple M5 Ultra",
    "c5c": "Xeon 8275CL",
    "c5n": "Xeon 8124M",
    "c8i": "Xeon 6975P-C",
    "c8a": "EPYC 9R45",
}
sizes = (32, 1048576)
suites = [
    f"{family}_{level}{speed}"
    for family, level, speed in itertools.product(
        ("sha2", "shake"), (128, 192, 256), "sf"
    )
]
operations = ("keygen", "public_key", "sign", "sign_hedged", "verify")
with original.open() as f:
    prior = [r for r in csv.DictReader(f) if float(r["peer_over_formal"]) < 1]

result = []
for host, cpu in machines.items():
    apple = host == "apple"
    rounds = 3 if apple else 5
    providers = (
        ("old", "new", "opencl")
        if apple
        else ("old", "new", "new1", "fluhrer1", "fluhrer2")
    )
    data = {}
    with (destination / f"{host}.csv").open() as f:
        for r in csv.DictReader(f):
            key = (
                r["provider"],
                r["set"],
                r["operation"],
                int(r["bytes"]),
                int(r["round"]),
            )
            if key in data or float(r["ns"]) <= 0:
                raise ValueError(f"invalid row on {host}: {key}")
            data[key] = float(r["ns"])
    expected = {
        key
        for key in itertools.product(
            providers, suites, operations, sizes, range(rounds + 1)
        )
        if key[0] != "opencl" or key[1] in ("sha2_128s", "sha2_128f")
    }
    if set(data) != expected:
        raise ValueError(f"incomplete sweep on {host}")
    for row in prior:
        if row["cpu"] != cpu:
            continue
        peer = row["peer"].replace("-", "")
        new = "new1" if peer == "fluhrer1" else "new"
        cell = (row["set"], row["operation"], int(row["message_bytes"]))

        old_times, new_times, peer_times = [
            [data[(provider, *cell, i)] for i in range(1, rounds + 1)]
            for provider in ("old", new, peer)
        ]
        speedup = [a / b for a, b in zip(old_times, new_times)]
        margin = [a / b for a, b in zip(peer_times, new_times)]
        result.append(
            [
                cpu,
                *cell,
                row["peer"],
                new,
                rounds,
                *map(
                    statistics.median,
                    (old_times, new_times, peer_times, speedup, margin),
                ),
                min(margin),
                max(margin),
            ]
        )
if len(result) != len(prior):
    raise ValueError("missing original loss")
with (destination / "prior-losses.csv").open("w", newline="") as f:
    out = csv.writer(f)
    out.writerow(
        [
            "cpu",
            "set",
            "operation",
            "message_bytes",
            "peer",
            "candidate",
            "rounds",
            "old_ns",
            "new_ns",
            "peer_ns",
            "old_over_new",
            "peer_over_new",
            "min_peer_over_new",
            "max_peer_over_new",
        ]
    )
    out.writerows(result)
