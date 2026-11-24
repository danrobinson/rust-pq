"""Produce latency and paired speedup summaries from the recorded samples."""
import argparse
import csv
import gzip
import itertools
import math
from collections import defaultdict
from pathlib import Path
from statistics import median

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("folder", nargs="?", type=Path,
                    default=Path(__file__).resolve().parents[1] / "results" / "peers",
                    help="directory containing samples.csv.gz and encoding-samples.csv.gz")
folder = parser.parse_args().folder
providers = ("library", "openssl", "rustcrypto")
platforms = ("apple", "c5", "c5n", "c8a", "c8i", "c6g", "c8g")
sets = [f"{family}_{n}{v}" for family in ("sha2", "shake") for n in (128, 192, 256) for v in "sf"]


def summarize(prefix, axes):
    groups = defaultdict(dict)
    with gzip.open(folder / (prefix + "samples.csv.gz"), "rt") as source:
        for row in csv.DictReader(source):
            group = tuple(row[a] for a in axes)
            pair = row["provider"], int(row["round"])
            if pair in groups[group]:
                raise ValueError(f"duplicate sample {group} {pair}")
            groups[group][pair] = float(row["ns"])
    if set(groups) != set(itertools.product(*axes.values())):
        raise ValueError("incomplete platform/workload matrix")
    aggregates = defaultdict(list)
    with (folder / (prefix + "workloads.csv")).open("w") as file:
        table = csv.writer(file, lineterminator="\n")
        columns = list(axes) + [p + "_median_ns" for p in providers]
        columns += [p + "_over_library_" + s for p in providers[1:] for s in ("median", "min", "max")]
        table.writerow(columns)
        for group, data in sorted(groups.items()):
            cpu, param, op = group[0], group[-2], group[-1]
            wanted = set(itertools.product(providers, range(7)))
            if set(data) != wanted:
                raise ValueError(f"incomplete rounds {group}")
            result = list(group)
            for p in providers:
                result.append(median(data[p, r] for r in range(1, 7)))
            for peer in providers[1:]:
                ratios = [data[peer, r] / data["library", r] for r in range(1, 7)]
                result += [round(f(ratios), 6) for f in (median, min, max)]
                aggregates[cpu, param.split("_")[0], op, peer].append(median(ratios))
            table.writerow(result)
    with (folder / (prefix + "aggregate.csv")).open("w") as file:
        table = csv.writer(file, lineterminator="\n")
        table.writerow(["cpu", "family", "operation", "provider", "workloads", "geomean_peer_over_library"])
        for group, ratios in sorted(aggregates.items()):
            mean = math.exp(sum(map(math.log, ratios)) / len(ratios))
            table.writerow([*group, len(ratios), round(mean, 6)])


summarize("", {
    "cpu": platforms,
    "bytes": ("32", "1048576"),
    "set": sets,
    "operation": ("keygen", "public_key", "sign", "sign_hedged", "verify"),
})
summarize("encoding-", {
    "cpu": platforms,
    "set": sets,
    "operation": ("secret_key_from", "public_key_from", "pkcs8_encode", "pkcs8_decode", "spki_encode", "spki_decode"),
})
