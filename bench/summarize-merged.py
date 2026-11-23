"""Summarize paired latency on the merged twelve-set implementation."""
import csv
import gzip
from collections import defaultdict
from pathlib import Path
from statistics import median

OUT = Path(__file__).resolve().parent / "results" / "merged"


def summarize(name, baseline, candidate, hosts):
    samples = defaultdict(dict)
    with gzip.open(OUT / f"{name}.csv.gz", "rt") as f:
        for host, mode, length, parameter, operation, rnd, ns in csv.reader(f):
            key = (host, int(length), parameter, operation, mode)
            if int(rnd) in samples[key]:
                raise ValueError(f"Duplicate sample for {key}, round {rnd}")
            samples[key][int(rnd)] = int(ns)
    keys = list(dict.fromkeys(k[:-1] for k in samples))
    assert {k[0] for k in keys} == set(hosts) and len(keys) == len(hosts) * 36
    with (OUT / f"{name}-summary.csv").open("w") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow("cpu bytes set operation before_ns after_ns speedup min_speedup max_speedup".split())
        for key in keys:
            old, new = (samples[(*key, mode)] for mode in (baseline, candidate))
            assert old.keys() == new.keys() == set(range(7))
            ratios = [old[i] / new[i] for i in range(1, 7)]
            writer.writerow([*key, median(old[i] for i in range(1, 7)),
                             median(new[i] for i in range(1, 7)), round(median(ratios), 5),
                             round(min(ratios), 5), round(max(ratios), 5)])


if __name__ == "__main__":
    summarize("shake", "before", "current", ("apple", "c5", "c8i", "c8a", "c6g", "c8g"))
    summarize("wide-refactor", "current", "refined", ("c5", "c8i", "c8a"))
    summarize("avx2", "current", "refined", ("c5",))
    summarize("arm-pair", "current", "refined", ("apple",))
    summarize("sha-ni", "current", "refined", ("c8a", "c8i"))
