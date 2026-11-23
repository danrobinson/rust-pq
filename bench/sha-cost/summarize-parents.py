#!/usr/bin/env python3
"""Recompute paired parent-driver timings and the reference costs for counted rounds."""
import csv
import gzip
import runpy
from collections import defaultdict
from pathlib import Path
from statistics import median

HERE = Path(__file__).resolve().parent
RESULTS = HERE.parent / "results"
OUT = RESULTS / "merged"
headroom = runpy.run_path(str(HERE / "summarize-headroom.py"))


def rows(name):
    with gzip.open(OUT / f"parent-driver-{name}.csv.gz", "rt") as f:
        yield from csv.DictReader(f)


def main():
    api = defaultdict(dict)
    for r in rows("samples"):
        key = tuple(r[k] for k in ("machine", "message_bytes", "set", "operation", "mode"))
        i = int(r["round"])
        assert i not in api[key]
        api[key][i] = int(r["ns"])
    assert all(set(v) == set(range(9)) for v in api.values())
    raw = defaultdict(dict)
    for r in rows("raw"):
        if int(r["round"]) and not r["kernel"].startswith("issue"):
            raw[r["machine"], int(r["bits"]), r["kernel"]][int(r["round"])] = float(r["ns"])
    assert all(set(v) == set(headroom["ROUNDS"]) for v in raw.values())
    with (HERE / "counts.csv").open() as f:
        counts = {(r["message_bytes"], r["set"], r["operation"], int(r["round"])):
                  (int(r["sha256_blocks"]), int(r["sha512_blocks"])) for r in csv.DictReader(f)}
    with (RESULTS / "headroom/rates.csv").open() as f:
        previous = {(r["machine"], int(r["algorithm"])): r for r in csv.DictReader(f)}
    with (OUT / "parent-driver-summary.csv").open("w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow("machine message_bytes set operation index_ns index_speedup counter_speedup active_speedup fresh_native_ratio previous_fastest_ratio previous_mixed_ratio".split())
        for machine in headroom["MACHINES"]:
            rates = []
            for bits in (256, 512):
                by_kernel = {k: median(v.values()) for (m, b, k), v in raw.items() if (m, b) == (machine, bits)}
                dedicated = [k for k in by_kernel if k.startswith(("x86", "arm"))]
                candidates = dedicated + [f"bulk{bits}"] if dedicated else list(by_kernel)
                rates.append(min(by_kernel[k] for k in candidates))
            for size in ("32", "1048576"):
                for param in headroom["PARAMS"]:
                    for op in ("keygen", "sign", "verify"):
                        work = (size, param, op)
                        key = (machine, *work)
                        old, new = api[key + ("current",)], api[key + ("index",)]
                        speedups = []
                        for mode in ("index", "counter", "active"):
                            if mode == "active" and machine not in headroom["X86"]:
                                speedups.append("")
                            else:
                                speedups.append(round(median(old[i] / api[key + (mode,)][i] for i in range(1, 9)), 6))
                        costs = defaultdict(list)
                        serial = headroom["serial_blocks"](*work)
                        for i in headroom["ROUNDS"]:
                            n = counts[work + (i,)]
                            fastest = mixed = 0
                            for j, bits in enumerate((256, 512)):
                                r = previous[machine, bits]
                                fastest += n[j] * float(r["fastest_ns"])
                                mixed += ((n[j] - serial[j]) * float(r["fastest_ns"]) +
                                          serial[j] * float(r["stream_ns"]))
                            costs["native"].append(new[i] / sum(a*b for a, b in zip(n, rates)))
                            costs["fastest"].append(new[i] / fastest)
                            costs["mixed"].append(new[i] / mixed)
                        w.writerow([*key, median(new[i] for i in range(1, 9)), *speedups,
                                    *(round(median(costs[k]), 6) for k in ("native", "fastest", "mixed"))])


if __name__ == "__main__":
    main()
