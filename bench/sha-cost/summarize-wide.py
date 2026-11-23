#!/usr/bin/env python3
"""Recompute the wide-x86 summary from its samples and the public API block counts."""
import csv
import gzip
from collections import defaultdict
from pathlib import Path
from statistics import median

HERE = Path(__file__).resolve().parent
RESULTS = HERE.parent / "results" / "wide-x86"
ROUNDS = range(1, 7)
MODES = ("base", "both", "native", "portable", "peer")


def raw_kernel(kernels, bits, prefer_dedicated):
    complete = [name for name in kernels if name[0] == bits and not name[1].startswith("issue")]
    dedicated = [name for name in complete if name[1].startswith("x86")]
    candidates = dedicated + [(bits, f"bulk{bits}")] if dedicated and prefer_dedicated else complete
    return min(candidates, key=lambda name: median(kernels[name].values()))


def main():
    with (HERE / "counts.csv").open() as source:
        counts = {(r["message_bytes"], r["set"], r["operation"], int(r["round"])):
                  (int(r["sha256_blocks"]), int(r["sha512_blocks"])) for r in csv.DictReader(source)}
    hosts = defaultdict(lambda: (defaultdict(dict), defaultdict(dict)))
    with gzip.open(RESULTS / "samples.csv.gz", "rt") as source:
        for r in csv.DictReader(source):
            i = int(r["round"])
            if r["phase"] != "final" or i == 0:
                continue
            kernels, times = hosts[r["machine"]]
            name = r["kernel_or_set"]
            if r["kind"] == "kernel":
                bits = int(r["sha_bits"])
                kernels[bits, name][i] = float(r["ns"])
            else:
                times[r["message_bytes"], name, r["operation"], r["build"]][i] = int(r["ns"])

    with (RESULTS / "summary.csv").open("w", newline="") as output:
        writer = csv.writer(output, lineterminator="\n")
        writer.writerow(("machine message_bytes set operation old_ns selected_ns native_ns portable_ns "
                         "peer_ns speedup_vs_old native_sha_cost_ns fastest_sha_cost_ns ratio_native_sha "
                         "ratio_fastest_sha ratio_fastest_min ratio_fastest_max").split())
        for host, (kernels, times) in hosts.items():
            for samples in (*kernels.values(), *times.values()):
                assert set(samples) == set(ROUNDS)
            choices = [[raw_kernel(kernels, bits, dedicated) for bits in (256, 512)]
                       for dedicated in (True, False)]
            for workload in dict.fromkeys(key[:3] for key in times):
                modes = [times[(*workload, mode)] for mode in MODES]
                old, selected = modes[:2]
                budgets = [[sum(n * kernels[k][i] for n, k in zip(counts[(*workload, i)], pair))
                            for i in ROUNDS] for pair in choices]
                ratios = [[selected[i] / cost for i, cost in zip(ROUNDS, costs)] for costs in budgets]
                metrics = [*(median(mode.values()) for mode in modes),
                           median(old[i] / selected[i] for i in ROUNDS), *map(median, budgets),
                           *map(median, ratios), min(ratios[1]), max(ratios[1])]
                writer.writerow([host, *workload, *(round(x, 5) for x in metrics)])


if __name__ == "__main__":
    main()
