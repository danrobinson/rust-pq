"""Summarise criterion output under results/<stamp>/ into Markdown tables.

For every (config, benchmark, implementation): per-iteration times of every
criterion sample from every round are pooled; we report the pooled median,
the per-round medians (spread across rounds), and the ratio of the pooled
median to the verified crate's pooled median in the same configuration.
"""
import json
import os
import re
import statistics
import sys

out = sys.argv[1]


def samples(path):
    with open(path) as f:
        s = json.load(f)
    return [t / i for t, i in zip(s["times"], s["iters"])]


def collect(prefix):
    """{config: {group: {impl: [[round samples], ...]}}}"""
    data = {}
    for d in sorted(os.listdir(out)):
        m = re.fullmatch(prefix + r"([a-z]+)-r(\d+)", d)
        if not m:
            continue
        cfg = m.group(1)
        root = os.path.join(out, d)
        for group in sorted(os.listdir(root)):
            gdir = os.path.join(root, group)
            if not os.path.isdir(gdir) or group == "report":
                continue
            for imp in sorted(os.listdir(gdir)):
                p = os.path.join(gdir, imp, "new", "sample.json")
                if os.path.exists(p):
                    data.setdefault(cfg, {}).setdefault(group, {}).setdefault(imp, []).append(samples(p))
    return data


def fmt(ns):
    if ns >= 1e9:
        return f"{ns / 1e9:.3f} s"
    if ns >= 1e6:
        return f"{ns / 1e6:.2f} ms"
    if ns >= 1e3:
        return f"{ns / 1e3:.2f} µs"
    return f"{ns:.1f} ns"


ORDER = ["verified", "verified+hw-sha2", "verified-before", "variant-A", "variant-B", "variant-C", "variant-D", "rustcrypto-slh-dsa", "fips205", "openssl", "slhdsa-c", "pqclean-r3"]
GROUPS = ["keygen", "sign_32B", "sign_1MiB", "verify_32B", "verify_1MiB"]


def table(data, cfg, groups, order, anchor="verified"):
    print(f"\n### config `{cfg}`\n")
    print("| implementation | " + " | ".join(groups) + " |")
    print("|---|" + "---|" * len(groups))
    imps = sorted({i for g in groups for i in data[cfg].get(g, {})}, key=lambda x: order.index(x) if x in order else 99)
    for imp in imps:
        cells = []
        for g in groups:
            runs = data[cfg].get(g, {}).get(imp)
            if not runs:
                cells.append("–")
                continue
            pooled = statistics.median([x for r in runs for x in r])
            per_round = [statistics.median(r) for r in runs]
            spread = f"±{50 * (max(per_round) - min(per_round)) / pooled:.1f}%"
            ratio = ""
            a = data[cfg].get(g, {}).get(anchor)
            if a and imp != anchor:
                ar = statistics.median([x for r in a for x in r])
                ratio = f" **{ar / pooled:.1f}×**" if ar >= pooled else f" **{ar / pooled:.2f}×**"
            cells.append(f"{fmt(pooled)}{ratio} <sub>{spread}</sub>")
        print(f"| {imp} | " + " | ".join(cells) + " |")


sig = collect("")
n_rounds = max(len(r) for c in sig.values() for g in c.values() for r in g.values())
print("## Signature operations")
print(f"\nMedian time per operation over all samples of all {n_rounds} rounds; **bold** = speed-up over the verified crate")
print("in the same build configuration (>1 = faster than verified); ±x% = half the range of the per-round medians.")
for cfg in ["default", "soft", "tuned", "asm", "hw"]:
    if cfg in sig:
        # In `hw` the verified crate is built with its hw-sha2 feature and is the anchor there.
        table(sig, cfg, [g for g in GROUPS if any(g in sig[c] for c in sig)], ORDER,
              anchor="verified+hw-sha2" if cfg == "hw" else "verified")

# verified crate, tuned vs default
if "default" in sig and "tuned" in sig:
    print("\n### tuned / default, same implementation\n")
    print("| implementation | " + " | ".join(GROUPS) + " |")
    print("|---|" + "---|" * len(GROUPS))
    for imp in ORDER:
        cells = []
        for g in GROUPS:
            d = sig["default"].get(g, {}).get(imp)
            t = sig["tuned"].get(g, {}).get(imp)
            if d and t:
                dm = statistics.median([x for r in d for x in r])
                tm = statistics.median([x for r in t for x in r])
                cells.append(f"{dm / tm:.2f}×")
            else:
                cells.append("–")
        if any(c != "–" for c in cells):
            print(f"| {imp} | " + " | ".join(cells) + " |")

sha = collect("sha-")
if sha:
    print("\n## SHA-256 one-shot (median per call; MB/s in parentheses)")
    for cfg in sha:
        groups = sorted(sha[cfg], key=lambda g: int(re.search(r"_(\d+)B", g).group(1)))
        print(f"\n### config `{cfg}`\n")
        print("| implementation | " + " | ".join(groups) + " |")
        print("|---|" + "---|" * len(groups))
        imps = sorted({i for g in groups for i in sha[cfg][g]})
        for imp in imps:
            cells = []
            for g in groups:
                runs = sha[cfg][g].get(imp)
                n = int(re.search(r"_(\d+)B", g).group(1))
                pooled = statistics.median([x for r in runs for x in r])
                cells.append(f"{fmt(pooled)} ({n / pooled * 1e3:.0f} MB/s)")
            print(f"| {imp} | " + " | ".join(cells) + " |")
