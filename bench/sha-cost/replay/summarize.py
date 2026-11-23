"""Validate archived samples and calculate per-workload paired medians."""
import csv
import gzip
import itertools
from collections import defaultdict
from pathlib import Path
from statistics import median

OUT = Path(__file__).resolve().parents[2] / "results/hash-replay"
CPUS = ("apple", "c5", "c5n", "c8a", "c8i", "c6g", "c8g")
SETS = tuple("SHA2_" + shape for shape in ("128S","128F","192S","192F","256S","256F"))
OPS = ("keygen", "sign", "verify")
MODES = ("full_ns", "reuse_ns", "api_ns")


def main():
    data = defaultdict(dict)
    with gzip.open(OUT / "samples.csv.gz", "rt") as f:
        for r in csv.DictReader(f):
            k = r["cpu"], r["set"], int(r["bytes"]), r["operation"]
            i = int(r["round"])
            assert i not in data[k] and int(r["hash_batches"]) > 0
            data[k][i] = tuple(int(r[v]) for v in MODES)
            assert min(data[k][i]) > 0
    assert set(data) == set(itertools.product(CPUS, SETS, (32, 1048576), OPS))
    with (OUT / "summary.csv").open("w") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["cpu", "set", "bytes", "operation", *MODES, "full_over_reuse",
                    "full_over_reuse_min", "full_over_reuse_max", "api_over_reuse"])
        for k, rounds in sorted(data.items()):
            assert set(rounds) == set(range(7))
            measured = [rounds[i] for i in range(1, 7)]
            benefit = [full/reuse for full,reuse,_ in measured]
            api_ratio = [api/reuse for _,reuse,api in measured]
            w.writerow([*k, *map(median, zip(*measured)),
                        *(round(x, 6) for x in (median(benefit), min(benefit),
                                                max(benefit), median(api_ratio)))])


if __name__ == "__main__":
    main()
