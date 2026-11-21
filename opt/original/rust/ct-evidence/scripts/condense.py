#!/usr/bin/env python3
"""Condense a dudect output table (out/dudect_*.md) to the columns quoted in RESULTS.md."""
import sys
def rows(path):
    for line in open(path):
        if line.startswith('| ') and not line.startswith('| function'):
            yield [x.strip() for x in line.strip().strip('|').split('|')]
def condense(path):
    out = ["| function | calls/meas. | n (class 0 / 1) | median class 0 (ns/call) | trimmed mean diff (ns) | rel. | t | max abs t | null abs t (cls 1 / cls 0) | > 4.5? |", "|---|---|---|---|---|---|---|---|---|---|"]
    for c in rows(path):
        flag = "**yes**" if ("t > 4.5" in c[13] or "leak detected (" in c[13]) else "no"
        out.append(f"| {c[0]} | {c[2]} | {c[3]} / {c[4]} | {c[5]} | {c[7]} | {c[8]} | {c[9]} | {c[10]} | {c[11]} / {c[12]} | {flag} |")
    return "\n".join(out)
if __name__ == "__main__":
    for p in sys.argv[1:]:
        print(condense(p)); print()
