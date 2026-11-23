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


def leaf_sha_ratios():
    with gzip.open(OUT / "leaf-raw.csv.gz", "rt") as f:
        rates = {(host, int(rnd), kernel): float(ns) for host, rnd, kernel, ns in csv.reader(f)}
    with (OUT.parents[1] / "sha-cost/counts.csv").open() as f:
        counts = {(r["message_bytes"], r["set"], r["operation"], int(r["round"])):
                  (int(r["sha256_blocks"]), int(r["sha512_blocks"])) for r in csv.DictReader(f)}
    results = defaultdict(dict)
    with gzip.open(OUT / "leaves.csv.gz", "rt") as f:
        for host, mode, size, name, op, rnd, ns in csv.reader(f):
            i = int(rnd)
            if mode != "shared" or i == 0:
                continue
            n256, n512 = counts[size, name.removeprefix("sha2_"), op, i]
            cost = n256 * rates[host, i, "rust256_16"] + n512 * rates[host, i, "rust512_8"]
            results[host, size, name, op][i] = int(ns) / cost
    assert len(results) == 108 and all(set(v) == set(range(1, 7)) for v in results.values())
    with (OUT / "leaf-sha-summary.csv").open("w") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow("cpu bytes set operation ratio min_ratio max_ratio".split())
        for key, samples in results.items():
            vals = samples.values()
            w.writerow([*key, *(round(fn(vals), 6) for fn in (median, min, max))])


if __name__ == "__main__":
    summarize("shake", "before", "current", ("apple", "c5", "c8i", "c8a", "c6g", "c8g"))
    summarize("wide-refactor", "current", "refined", ("c5", "c8i", "c8a"))
    summarize("avx2", "current", "refined", ("c5",))
    summarize("arm-pair", "current", "refined", ("apple",))
    summarize("sha-ni", "current", "refined", ("c8a", "c8i"))
    summarize("group-stores", "current", "stores", ("c5", "c8a", "c8i"))
    summarize("transpose-stores", "current", "transpose", ("c5", "c8a", "c8i"))
    summarize("leaves", "current", "shared", ("c5", "c8a", "c8i"))
    leaf_sha_ratios()
