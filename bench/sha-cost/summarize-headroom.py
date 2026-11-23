#!/usr/bin/env python3
"""Summarize the six paired API rounds and the measured SHA references."""
import csv
import gzip
from collections import defaultdict
from pathlib import Path
from statistics import median

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "results" / "headroom"
ROUNDS = range(1, 7)
MACHINES = ("c5", "c8a", "c8i", "c6g", "c8g", "apple")
X86 = {"c5", "c8a", "c8i"}
# Digest width, number of hypertree layers, XMSS subtree height and FORS trees (FIPS 205).
PARAMS = {"128s": (16, 7, 9, 14), "128f": (16, 22, 3, 33), "192s": (24, 7, 9, 17),
          "192f": (24, 22, 3, 33), "256s": (32, 8, 8, 22), "256f": (32, 17, 4, 35)}


def serial_blocks(size, parameter, op):
    n, d, hp, k = PARAMS[parameter]
    b = 64 if n == 16 else 128
    padding = 9 if n == 16 else 17
    message = max(0, (int(size) - 128) // b)
    count = {"keygen": 0, "sign": 2 * message, "verify": message}[op]
    if op == "verify":
        wots = (22 + (2 * n + 3) * n + padding + b - 1) // b
        fors = (22 + k * n + padding + b - 1) // b
        count += d * (wots + hp) + fors
    return [count, 0] if n == 16 else [0, count]


def main():
    with (HERE / "counts.csv").open() as f:
        counts = {(r["message_bytes"], r["set"], r["operation"], int(r["round"])):
                  [int(r["sha256_blocks"]), int(r["sha512_blocks"])] for r in csv.DictReader(f)}
    api = defaultdict(dict)
    raw = defaultdict(dict)
    with gzip.open(OUT / "samples.csv.gz", "rt") as f:
        for r in csv.DictReader(f):
            i = int(r["round"])
            if i == 0:
                continue
            h, phase, name = r["machine"], r["phase"], r["kernel_or_set"]
            if r["kind"] == "raw":
                raw[h, phase, int(r["algorithm"]), name][i] = float(r["ns"])
            else:
                api[h, phase, r["mode"], r["message_bytes"], name, r["operation"]][i] = int(r["ns"])
    assert all(set(v) == set(ROUNDS) for v in (*api.values(), *raw.values()))
    workloads = [(size, parameter, op) for size in ("32", "1048576") for parameter in PARAMS
                 for op in ("keygen", "sign", "verify")]
    required = {(h, "final", mode, *work) for h in MACHINES
                for mode in ("both", "final", "tuned") for work in workloads}
    required.update((h, "paired", "final", *work) for h in X86 for work in workloads)
    if set(api) != required:
        raise ValueError(f"API matrix mismatch: missing {required - set(api)}, extra {set(api) - required}")
    with (OUT / "summary.csv").open("w", newline="") as f, (OUT / "rates.csv").open("w", newline="") as rf:
        w, rates = csv.writer(f, lineterminator="\n"), csv.writer(rf, lineterminator="\n")
        w.writerow(("machine message_bytes set operation before_ns final_ns tuned_ns speedup speedup_min "
                    "speedup_max tuned_speedup dedicated_ratio fastest_ratio mixed_ratio c_paired_ratio "
                    "rust_paired_ratio").split())
        rates.writerow("machine algorithm dedicated_kernel dedicated_ns fastest_kernel fastest_ns stream_ns".split())
        for h in MACHINES:
            dedicated, fastest, c_best, streaming = [], [], [], []
            for bits in [256, 512]:
                eligible = {key: median(samples.values()) for key, samples in raw.items()
                            if key[0] == h and key[2] == bits and not key[3].startswith("issue")}
                c = {key: t for key, t in eligible.items() if key[1] == "final"}
                native = [k for k in c if k[3].startswith(("x86", "arm"))]
                stream = (h, "final", bits, f"bulk{bits}")
                fk = min(eligible, key=eligible.get)
                dk = min(native + [stream], key=c.get) if native else fk
                dedicated.append(dk)
                fastest.append(eligible[fk])
                c_best.append(min(c, key=c.get))
                streaming.append(c[stream])
                rates.writerow([h, bits, dk[-1], round(eligible[dk], 6), fk[-1], round(eligible[fk], 6), round(c[stream], 6)])
            for size, p, op in workloads:
                old, final, tuned = [api[h, "final", m, size, p, op] for m in ("both", "final", "tuned")]
                speed, native, d_ratio, fast_ratio, mixed_ratio, c_ratio, rust_ratio = ([] for _ in range(7))
                serial = serial_blocks(size, p, op)
                for i in ROUNDS:
                    n = counts[size, p, op, i]
                    assert all(a <= b for a, b in zip(serial, n))
                    speed.append(old[i] / final[i])
                    native.append(final[i] / tuned[i])
                    d_ratio.append(final[i] / sum(x * median(raw[k].values()) for x, k in zip(n, dedicated)))
                    fast_cost = sum(x * r for x, r in zip(n, fastest))
                    fast_ratio.append(final[i] / fast_cost)
                    mixed = fast_cost + sum(x * (b - a) for x, b, a in zip(serial, streaming, fastest))
                    mixed_ratio.append(final[i] / mixed)
                    c_ratio.append(final[i] / sum(x * raw[k][i] for x, k in zip(n, c_best)))
                    sk = h, "paired", "final", size, p, op
                    if sk in api:
                        cost = sum(x * raw[h, "paired", bits, name][i]
                                   for x, bits, name in zip(n, (256, 512), ("rust256_16", "rust512_8")))
                        rust_ratio.append(api[sk][i] / cost)
                out = [median(v.values()) for v in (old, final, tuned)]
                out += [median(speed), min(speed), max(speed), median(native), median(d_ratio),
                        median(fast_ratio), median(mixed_ratio), median(c_ratio)]
                w.writerow([h, size, p, op, *(round(x, 5) for x in out),
                            round(median(rust_ratio), 5) if rust_ratio else ""])


if __name__ == "__main__":
    main()
