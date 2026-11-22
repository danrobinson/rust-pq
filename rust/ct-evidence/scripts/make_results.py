#!/usr/bin/env python3
"""Fill scripts/RESULTS.template.md from the raw outputs in out/<variant>/ -> RESULTS.md.

Placeholders are `{{KEY}}` and, per build of the crate, `{{default:KEY}}` /
`{{hw-sha2:KEY}}`. Every number quoted in RESULTS.md is computed here from
the raw files, and the outcomes the template's prose states (all secret-varied
rows identical, all controls detected, all pinned comparisons identical) are
asserted: if a raw file says otherwise this script stops instead of writing a
RESULTS.md that contradicts it. A raw file that does not exist yields the text
"(not run)".
"""
import os, re, sys
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.dirname(here)
VARIANTS = ["default", "hw-sha2"]
ENTRIES = ["internal", "internal-checked", "slh", "slh-checked", "api", "api-checked", "api-det", "api-det-checked"]
NOT_RUN = "(not run)"

def rd(v, name):
    p = os.path.join(root, "out", v, name)
    return open(p).read() if os.path.exists(p) else None

def cells(line):
    return [c.strip() for c in line.strip().strip("|").split("|")]

def table(text):
    """Rows (as cell lists) of the first markdown table in text, without header and rule."""
    lines = [l for l in text.splitlines() if l.startswith("|")]
    return [cells(l) for l in lines[2:]]

def num(x):
    return float(re.match(r"[-+]?[0-9.]+", x).group(0))

def rng(vals, fmt="{:.3g}"):
    lo, hi = fmt.format(min(vals)), fmt.format(max(vals))
    return lo if lo == hi else lo + " to " + hi

R = {}
checks = []
noise = ["| build | run | 1-min load average before / after | rows | rows with max abs t > 4.5 | largest max abs t | largest within-class null abs t | positive controls: max abs t |", "|---|---|---|---|---|---|---|---|"]

def need(cond, msg):
    checks.append((bool(cond), msg))

# ------------------------------------------------------------------ per build
for v in VARIANTS:
    K = lambda k: f"{v}:{k}"
    b = rd(v, "build.txt")
    R[K("BUILD")] = "```\n" + b.strip() + "\n```" if b else NOT_RUN
    if b:
        R[K("DATE")] = re.search(r"^date: (\S+)", b, re.M).group(1)

    # --- emulator check
    h = rd(v, "hwcheck.md")
    if h:
        R[K("HWCHECK")] = "\n".join(l for l in h.splitlines() if l.startswith("|") or l.startswith("SHA-256 instructions present")).replace("\nSHA-256", "\n\nSHA-256")
        rows = table(h)
        need("overall: AS EXPECTED" in h and all(r[6] == "yes" for r in rows), f"{v}: hwcheck")
        sha = [sum(int(x) for x in r[2:6]) for r in rows]
        need(all(s > 0 for s in sha) if v == "hw-sha2" else all(s == 0 for s in sha), f"{v}: SHA-256 instruction counts")
        R[K("HWCHECK_ROWS")] = str(len(rows))
    else:
        R[K("HWCHECK")] = NOT_RUN; R[K("HWCHECK_ROWS")] = "0"

    # --- component traces
    tc = rd(v, "trace_components.md")
    if tc:
        rows = table(tc)
        kind = lambda r: "leaky" if r[0].startswith("CONTROL leaky") else "pubctl" if (r[0].startswith("CONTROL") or r[11].startswith("PASS (control")) else "info" if r[11].startswith("info") else "equal"
        eq = [r for r in rows if kind(r) == "equal"]
        leaky = [r for r in rows if kind(r) == "leaky"]
        pubc = [r for r in rows if kind(r) == "pubctl"]
        info = [r for r in rows if kind(r) == "info"]
        need(all(r[11] == "PASS (all identical)" for r in eq), f"{v}: a secret-varied component row is not identical")
        need(all(r[11].startswith("PASS (control") for r in leaky + pubc), f"{v}: a control was not detected")
        need(all(r[10] == "yes" for r in rows), f"{v}: emulated output differs from native output")
        need("overall: ALL ROWS AS EXPECTED" in tc, f"{v}: component overall line")
        vs = [r for r in eq if r[0].endswith("_pk_from_sig")]
        sec = [r for r in eq if r not in vs]
        R[K("COMP")] = tc.strip()
        R[K("COMP_SEC_ROWS")] = str(len(sec))
        R[K("COMP_SEC_PAIRS")] = str(sum(int(r[3]) for r in sec))
        R[K("COMP_SEC_CFGS")] = str(sum(int(r[2]) for r in sec))
        R[K("COMP_VS_ROWS")] = str(len(vs))
        R[K("COMP_VS_PAIRS")] = str(sum(int(r[3]) for r in vs))
        R[K("COMP_LEAKY")] = f"{len(leaky)} controls, {sum(int(r[3]) for r in leaky)} pairs, {sum(int(r[5]) for r in leaky)} differing"
        R[K("COMP_PUBCTL")] = f"{len(pubc)} controls, {sum(int(r[3]) for r in pubc)} pairs, {sum(int(r[5]) for r in pubc)} differing"
        R[K("COMP_PUBCTL_ALL")] = "yes" if all(int(r[4]) == 0 for r in pubc) else "no"
        R[K("COMP_INFO")] = "; ".join(f"`{r[0]}`: {r[11].replace('info: ', '')} ({r[3]} pairs)" for r in info) or "none"
        R[K("COMP_INSN_MAX")] = f"{max(int(r[6]) for r in rows):.2e}"
    else:
        for k in ("COMP", "COMP_SEC_ROWS", "COMP_SEC_PAIRS", "COMP_SEC_CFGS", "COMP_VS_ROWS", "COMP_VS_PAIRS", "COMP_LEAKY", "COMP_PUBCTL", "COMP_PUBCTL_ALL", "COMP_INFO", "COMP_INSN_MAX"):
            R[K(k)] = NOT_RUN

    # --- pinned whole-signature traces
    summ = ["| entry point | compared | public configs | values recorded and pinned | pairs (A, B) | pinned: identical | unpinned controls differing | insns/run | events/run | verdict |", "|---|---|---|---|---|---|---|---|---|---|"]
    tot_pairs = tot_cfg = 0
    for e in ENTRIES:
        t = rd(v, f"trace_sign_{e}.md")
        if not t:
            R[K(f"SIGN_{e}")] = NOT_RUN
            continue
        rows = table(t)
        if not rows:
            need(False, f"{v}: pinned signing {e}: output incomplete")
            R[K(f"SIGN_{e}")] = NOT_RUN
            continue
        name = re.search(r"^### `([^`]+)`: declassification-pinned trace comparison \(([^)]+)\)", t, re.M)
        need("overall: ALL CONFIGURATIONS PASS" in t and all(r[9] == "PASS" for r in rows), f"{v}: pinned signing {e}")
        need(not any(l.startswith("- config") for l in t.splitlines()), f"{v}: pinned signing {e} has log lines")
        pinned = sorted({int(r[2]) for r in rows})
        need(pinned == ([16] if "checked" in e else [9]), f"{v}: {e} pinned {pinned}")
        pairs = sum(int(r[3]) for r in rows); ident = sum(int(r[4]) for r in rows)
        need(pairs == ident and all(int(r[5]) == 0 for r in rows), f"{v}: {e} pinned traces differ")
        ctl = [r[6].split("/") for r in rows]
        need(all(a == b for a, b in ctl), f"{v}: {e} unpinned control")
        summ.append(f"| `{name.group(1)}` | {name.group(2)} | {len(rows)} | {pinned[0]} | {pairs} | {ident} | {sum(int(a) for a, _ in ctl)}/{sum(int(b) for _, b in ctl)} | {rng([int(r[7]) for r in rows], '{:.3e}')} | {rng([int(r[8]) for r in rows], '{:.3e}')} | PASS |")
        R[K(f"SIGN_{e}")] = "\n".join(l for l in t.splitlines() if l.startswith("|") or l.startswith("- config"))
        R[K(f"SIGN_{e}_CFGS")] = str(len(rows)); R[K(f"SIGN_{e}_PAIRS")] = str(pairs)
        R[K(f"SIGN_{e}_INSN")] = f"{max(int(r[7]) for r in rows):.2e}"; R[K(f"SIGN_{e}_EV")] = f"{max(int(r[8]) for r in rows):.2e}"
        tot_pairs += pairs; tot_cfg += len(rows)
    R[K("SIGN_SUMMARY")] = "\n".join(summ) if len(summ) > 2 else NOT_RUN
    R[K("SIGN_TOTAL_PAIRS")] = str(tot_pairs); R[K("SIGN_TOTAL_CFGS")] = str(tot_cfg)
    for e in ENTRIES:
        for k in ("_CFGS", "_PAIRS", "_INSN", "_EV"):
            R.setdefault(K(f"SIGN_{e}{k}"), NOT_RUN)

    # --- profiles
    for e in ("internal", "internal-checked"):
        t = rd(v, f"trace_sign_profile_{e}.md")
        R[K(f"PROFILE_{e}")] = "\n".join(l for l in t.splitlines() if l.startswith("- ")) if t else NOT_RUN
        if t:
            need("failed runs: 0" in t and "equal to the native one: yes" in t, f"{v}: profile {e}")
            m = re.search(r"instruction counts: (\d+) \(min (\d+), max (\d+), spread (\d+)\)", t)
            R[K(f"PROFILE_{e}_SPREAD")] = f"{m.group(4)} out of {int(m.group(2)):.2e}"
            R[K(f"PROFILE_{e}_RUNS")] = re.search(r"^- runs: (\d+)", t, re.M).group(1)
        else:
            R[K(f"PROFILE_{e}_SPREAD")] = R[K(f"PROFILE_{e}_RUNS")] = NOT_RUN

    # --- static facts
    d = rd(v, "disasm.md")
    if d:
        R[K("DISASM")] = re.sub(r"^## ", "#### ", re.sub(r"^### ", "##### ", d, flags=re.M), flags=re.M).strip()
        line = [l for l in d.splitlines() if "functions identical" in l][0].strip()
        R[K("RLIB_COMPARE")] = line
        need(", 0 different, 0 present in only one" in line and "0 code ranges left unnamed" in line, f"{v}: rlib comparison")
        need("constant data: same numeric constants and tables" in d, f"{v}: constant data comparison")
        tot = [cells(l) for l in d.splitlines() if l.startswith("| **total")][0]
        nfun = re.search(r"(\d+) functions", tot[0]).group(1)
        R[K("STATIC_TOTAL")] = f"{nfun} functions, {tot[1]} instructions: {tot[2]} conditional branches, {tot[3]} indirect branches, {tot[4]} integer divisions, {tot[5]} crypto-extension instructions"
        need(tot[3] == "0" and tot[4] == "0", f"{v}: indirect branch or division present")
        need("Calls of `memcmp`/`bcmp` from slhdsa code: 0." in d, f"{v}: memcmp call")
        need((int(tot[5]) > 0) == (v == "hw-sha2"), f"{v}: crypto-extension instruction count")
    else:
        R[K("DISASM")] = R[K("RLIB_COMPARE")] = R[K("STATIC_TOTAL")] = NOT_RUN

    # --- timing (optional)
    def dud(name):
        t = rd(v, name)
        if not t:
            return None, None, None
        hdr = [l for l in t.splitlines() if l.startswith("slhdsa build:")]
        load = [l.strip() for l in t.splitlines() if "load average" in l]
        rows = [cells(l) for l in t.splitlines() if l.startswith("| ") and not l.startswith("| function")]
        return rows, (hdr[0] if hdr else ""), load
    def condensed(rows):
        out = ["| function | calls/meas. | n (class 0 / 1) | median class 0 (ns/call) | trimmed mean diff (ns) | rel. | t | max abs t | null abs t (cls 1 / cls 0) | std err of mean diff (ns) | > 4.5? |", "|---|---|---|---|---|---|---|---|---|---|---|"]
        for c in rows:
            flag = "**yes**" if num(c[10]) > 4.5 else "no"
            out.append(f"| {c[0]} | {c[2]} | {c[3]} / {c[4]} | {c[5]} | {c[7]} | {c[8]} | {c[9]} | {c[10]} | {c[11]} / {c[12]} | {c[14]} | {flag} |")
        return "\n".join(out)
    def loads(load):
        f = lambda l: re.search(r"load averages?: ([0-9.]+)", l).group(1)
        return f"1-minute load average {f(load[0])} before, {f(load[-1])} after" if load else ""
    LABEL = {"NULLB": "random vs random (null), before", "FR": "fixed (pseudo-random) vs random", "FZ": "fixed (all-zero) vs random", "DIT": "fixed (pseudo-random) vs random, DIT = 1", "NULLA": "random vs random (null), after",
             "SAME": "fixed vs random, same preparation path", "SAMEDIT": "fixed vs random, same preparation path, DIT = 1", "ZF": "fixed all-zero vs fixed pseudo-random"}
    FILES = (("NULLB", "dudect_null_before.md"), ("FR", "dudect_components_fixed_random.md"), ("FZ", "dudect_components_fixed_zero.md"), ("DIT", "dudect_components_fixed_random_DIT.md"), ("NULLA", "dudect_null_after.md"),
             ("SAME", "dudect_components_sameprep.md"), ("SAMEDIT", "dudect_components_sameprep_DIT.md"), ("ZF", "dudect_components_zero_vs_fixed.md"))
    lavg = lambda l: re.search(r"load averages?: ([0-9.]+)", l).group(1)
    for key, fn in FILES:
        rows, hdr, load = dud(fn)
        if not rows or not load or len(load) < 2:      # absent, or still being written
            for k in ("", "_HDR", "_FLAGGED", "_NFLAG", "_MAX", "_NULLMAX", "_CTL", "_NROWS"):
                R[K(f"DUDECT_{key}{k}")] = NOT_RUN
            continue
        ctl = [r for r in rows if r[0].startswith("CONTROL")]
        fn_rows = [r for r in rows if not r[0].startswith("CONTROL")]
        flagged = [r for r in fn_rows if num(r[10]) > 4.5]
        R[K(f"DUDECT_{key}")] = condensed(rows)
        R[K(f"DUDECT_{key}_HDR")] = "`" + hdr + "`; " + loads(load)
        R[K(f"DUDECT_{key}_NROWS")] = str(len(fn_rows))
        R[K(f"DUDECT_{key}_FLAGGED")] = ("none" if not flagged else ", ".join(f"`{r[0].split(' (')[0]}` ({num(r[10]):.1f})" for r in flagged))
        R[K(f"DUDECT_{key}_NFLAG")] = str(len(flagged))
        if key.startswith("NULL"):
            need(not flagged and not [r for r in ctl if num(r[10]) > 4.5], f"{v}: a row of a null run exceeds 4.5 (noise floor)")
        R[K(f"DUDECT_{key}_MAX")] = f"{max(num(r[10]) for r in fn_rows):.2f}"
        R[K(f"DUDECT_{key}_NULLMAX")] = f"{max(max(num(r[11]), num(r[12])) for r in rows):.2f}"
        R[K(f"DUDECT_{key}_CTL")] = ", ".join(f"{num(r[10]):.0f}" for r in ctl) if ctl else "none"
        isnull = key.startswith("NULL")
        allrows = rows if isnull else fn_rows       # in the null design the leaky controls are ordinary rows
        noise.append(f"| {v} | {LABEL[key]} | {lavg(load[0])} / {lavg(load[-1])} | {len(allrows)} | {sum(1 for r in allrows if num(r[10]) > 4.5)} | {max(num(r[10]) for r in allrows):.2f} | {max(max(num(r[11]), num(r[12])) for r in rows):.2f} | {'-' if isnull else ', '.join(f'{num(r[10]):.0f}' for r in ctl)} |")
        if key in ("FR", "FZ", "DIT", "SAME", "SAMEDIT"):
            need(all(num(r[10]) > 4.5 for r in ctl) and len(ctl) == 2, f"{v}: dudect {key} positive controls")
    # one line per function, the five runs side by side
    runs = {key: dud(fn)[0] for key, fn in FILES}
    R[K("DUDECT_MATRIX")] = NOT_RUN
    if all(runs[k_] for k_ in ("NULLB", "FR", "FZ", "DIT", "NULLA")):
        get = lambda key, name: next((r for r in (runs[key] or []) if r[0] == name), None)
        mark = lambda r: "-" if r is None else (f"**{num(r[10]):.1f}**" if num(r[10]) > 4.5 else f"{num(r[10]):.1f}")
        out = ["| function | n per class | median, DIT = 0 / 1 (ns/call) | std err (ns) | A: null before | B: fixed vs random | C: zero vs random | D: fixed vs random, DIT = 1 | E: null after | F: as B, same preparation | G: as D, same preparation | H: zero vs fixed |", "|---|---|---|---|---|---|---|---|---|---|---|---|"]
        for r in runs["FR"]:
            n_ = r[0]
            di = get("DIT", n_)
            out.append(f"| {n_} | {(int(r[3]) + int(r[4])) // 2} | {r[5]} / {di[5] if di else '-'} | {r[14]} | {mark(get('NULLB', n_))} | {mark(r)} | {mark(get('FZ', n_))} | {mark(di)} | {mark(get('NULLA', n_))} | {mark(get('SAME', n_))} | {mark(get('SAMEDIT', n_))} | {mark(get('ZF', n_))} |")
        R[K("DUDECT_MATRIX")] = "\n".join(out)
        fnr = lambda key: [r for r in runs[key] if not r[0].startswith("CONTROL")]
        slow = [num(get("DIT", r[0])[5]) / num(r[5]) for r in fnr("FR") if get("DIT", r[0]) and num(r[5]) > 100]
        R[K("DIT_COST")] = f"{100 * (min(slow) - 1):.0f}% to {100 * (max(slow) - 1):.0f}%"
        res = [100 * num(r[14]) / num(r[5]) for r in fnr("DIT")]
        R[K("DIT_RES")] = f"{min(res):.3f}% to {max(res):.3f}%"
    else:
        R[K("DIT_COST")] = R[K("DIT_RES")] = NOT_RUN
    srows = []
    for e in ("internal", "internal-checked"):
        for d_ in ("key", "addrnd"):
            rows, hdr, load = dud(f"dudect_sign_{d_}_{e}.md")
            if rows and load and len(load) >= 2:
                srows += rows
                noise.append(f"| {v} | whole signing: {rows[0][0]} | {lavg(load[0])} / {lavg(load[-1])} | 1 | {sum(1 for r in rows if num(r[10]) > 4.5)} | {num(rows[0][10]):.2f} | {max(num(rows[0][11]), num(rows[0][12])):.2f} | - |")
    R[K("DUDECT_SIGN")] = condensed(srows) if srows else NOT_RUN
    R[K("DUDECT_SIGN_RES")] = "; ".join(f"`{r[0]}`: standard error of the difference of class means {num(r[14]) / 1e6:.3f} ms = {100 * num(r[14]) / num(r[5]):.3f}% of the {num(r[5]) / 1e6:.1f} ms signing time" for r in srows) if srows else NOT_RUN
    R[K("DUDECT_SIGN_MAX")] = f"{max(num(r[10]) for r in srows):.2f}" if srows else NOT_RUN
    # --- class-design diagnostics: one column per run, one line per function
    def diag(fname, key):
        t = rd(v, fname)
        R[K(key)] = R[K(key + "_EFFECT")] = R[K(key + "_LOAD")] = R[K(key + "_NRUNS")] = NOT_RUN
        if not t:
            return
        secs = []
        for l in t.splitlines():
            if l.startswith("## "):
                secs.append([l[3:], []])
            elif l.startswith("| ") and not l.startswith("| function") and secs:
                secs[-1][1].append(cells(l))
        secs = [x for x in secs if x[1]]
        if not secs:
            return
        def tag(title):
            m = re.search(r"seed (\d+)", title)
            return title.split(":")[0] + (f" (seed {m.group(1)})" if m else "")
        fns = []
        for _, rows in secs:
            fns += [r[0] for r in rows if r[0] not in fns]
        out = ["| function | " + " | ".join(tag(x[0]) for x in secs) + " |", "|---|" + "---|" * len(secs)]
        for f_ in fns:
            line = []
            for _, rows in secs:
                r = [r for r in rows if r[0] == f_]
                x = num(r[0][10]) if r else None
                line.append("-" if x is None else (f"**{x:.1f}**" if x > 4.5 else f"{x:.1f}"))
            out.append(f"| {f_} | " + " | ".join(line) + " |")
        R[K(key)] = "\n".join(out)
        R[K(key + "_NRUNS")] = str(len(secs))
        # the fixed-vs-random effect per call and per measurement, at 1 x and 8 x calls per measurement
        pick = lambda k_: next((rows for title, rows in secs if title.startswith(k_ + ":")), None)
        fr, fr8 = pick("FR"), pick("FR/x8")
        if fr and fr8:
            out = ["| function | calls/meas. | trimmed mean diff (ns/call) | = ns per measurement | calls/meas., 8 x | trimmed mean diff (ns/call) | = ns per measurement | max abs t, 1 x / 8 x |", "|---|---|---|---|---|---|---|---|"]
            for f_ in fns:
                a = [r for r in fr if r[0] == f_]; b = [r for r in fr8 if r[0] == f_]
                if a and b:
                    a, b = a[0], b[0]
                    out.append(f"| {f_} | {a[2]} | {a[7]} | {num(a[7]) * int(a[2]):+.1f} | {b[2]} | {b[7]} | {num(b[7]) * int(b[2]):+.1f} | {num(a[10]):.1f} / {num(b[10]):.1f} |")
            R[K(key + "_EFFECT")] = "\n".join(out)
        la = [l for l in t.splitlines() if "load average" in l]
        R[K(key + "_LOAD")] = f"1-minute load average between {min(float(lavg(l)) for l in la):.2f} and {max(float(lavg(l)) for l in la):.2f} over the {len(secs)} runs"
        # details of one design, for the text: (function -> row)
        return {tag(title): {r[0]: r for r in rows} for title, rows in secs}
    D_ = diag("dudect_diag.md", "DIAG")
    DC_ = diag("dudect_diag_chain.md", "DIAGC")

# statements of the template about the timing results
HIGH = ("wots_pk_gen", "wots_sign", "xmss_node", "xmss_sign", "fors_sign", "fors_pk_gen", "slh_keygen_internal")
for v_ in VARIANTS:
    for key_ in ("FR", "FZ", "DIT", "SAME", "SAMEDIT", "ZF"):
        fl = R.get(f"{v_}:DUDECT_{key_}_FLAGGED", NOT_RUN)
        if fl not in (NOT_RUN, "none"):
            names = re.findall(r"`([^`]+)`", fl)
            bad_ = [n for n in names if n.startswith(HIGH) or (n.startswith("fors_node/z=") and n != "fors_node/z=0")]
            need(not bad_, f"{v_}: {key_}: a row above the hash level exceeds 4.5: {bad_}")
    if R.get(f"{v_}:DUDECT_SAMEDIT_NFLAG", NOT_RUN) != NOT_RUN:
        need(R[f"{v_}:DUDECT_SAMEDIT_NFLAG"] == "0", f"{v_}: a row of the same-preparation DIT = 1 run exceeds 4.5")
    if R.get(f"{v_}:DUDECT_SIGN_MAX", NOT_RUN) != NOT_RUN:
        need(float(R[f"{v_}:DUDECT_SIGN_MAX"]) <= 4.5, f"{v_}: a whole-signing timing row exceeds 4.5")
R["DUDECT_NOISE"] = "\n".join(noise) if len(noise) > 2 else NOT_RUN

# ------------------------------------------------------------------ write
bad = [m for ok, m in checks if not ok]
draft = len(sys.argv) == 3 and sys.argv[1] == "--draft"
if bad and draft:
    print("draft: checks that fail on the raw outputs so far:", bad)
elif bad:
    print("RESULTS.md NOT written; the raw outputs contradict the template's statements:")
    for m in bad:
        print("  -", m)
    sys.exit(1)
tpl = open(os.path.join(here, "RESULTS.template.md")).read()
for k, val in R.items():
    tpl = tpl.replace("{{" + k + "}}", val)
left = sorted(set(re.findall(r"\{\{[A-Za-z_0-9:\-]+\}\}", tpl)))
if draft:
    # work in progress: write wherever asked, and say which placeholders are still open
    open(sys.argv[2], "w").write(tpl)
    print(f"draft written to {sys.argv[2]}; unfilled placeholders: {left}")
    sys.exit(0)
assert not left, left
open(os.path.join(root, "RESULTS.md"), "w").write(tpl)
print(f"wrote RESULTS.md ({len(checks)} checks on the raw outputs passed)")
