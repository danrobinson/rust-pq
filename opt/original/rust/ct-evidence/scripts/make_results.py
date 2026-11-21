#!/usr/bin/env python3
"""Fill scripts/RESULTS.template.md from the raw outputs in out/ -> RESULTS.md."""
import os, re, sys
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.dirname(here)
sys.path.insert(0, here)
import condense

def rd(name):
    return open(os.path.join(root, "out", name)).read()

def table_lines(text):
    return [l for l in text.splitlines() if l.startswith("|")]

def f(x):
    return float(re.match(r"[-+]?[0-9.]+", x).group(0))

R = {}
# --- disasm
dis = rd("disasm.md")
R["RLIB_COMPARE"] = "**" + [l for l in dis.splitlines() if "functions identical" in l][0].strip() + "**"
R["DISASM"] = re.sub(r"^## ", "#### ", re.sub(r"^### ", "##### ", dis, flags=re.M), flags=re.M).strip()

# --- component traces
tc = rd("trace_components.md")
rows = [[c.strip() for c in l.strip().strip("|").split("|")] for l in table_lines(tc)[2:]]
eq_rows = [r for r in rows if not r[0].startswith("CONTROL")]
sec_rows = [r for r in eq_rows if "PUBLIC" not in r[0]]
leaky = [r for r in rows if r[0].startswith("CONTROL leaky")]
pubc = [r for r in rows if r[0].startswith("CONTROL") and "PUBLIC" in r[0]]
R["T2_PAIRS"] = str(sum(int(r[3]) for r in leaky))
R["T2_DIFF"] = str(sum(int(r[5]) for r in leaky))
R["T3_PAIRS"] = str(sum(int(r[3]) for r in pubc))
R["T3_DIFF"] = str(sum(int(r[5]) for r in pubc))
assert all(r[11] == "PASS (all identical)" for r in eq_rows), "unexpected component result"
assert all(r[11].startswith("PASS (control") for r in rows if r[0].startswith("CONTROL")), "control not detected"
R["N_COMPONENT_ROWS"] = str(len(sec_rows))
R["N_COMPONENT_PAIRS"] = str(sum(int(r[3]) for r in sec_rows))
R["TRACE_COMPONENTS"] = tc.strip()

def sign_block(name):
    t = rd(name)
    return "\n".join(l for l in t.splitlines() if l.startswith("|") or l.startswith("- config"))
R["TRACE_SIGN"] = sign_block("trace_sign.md")
R["TRACE_SIGN_CTX"] = sign_block("trace_sign_ctx.md")
R["TRACE_PROFILE"] = "\n".join(l for l in rd("trace_sign_profile.md").splitlines() if l.startswith("- "))

# --- dudect components
files = {"DUDECT_FR": "dudect_components_fixed_random.md", "DUDECT_FZ": "dudect_components_fixed_zero.md", "DUDECT_DIT": "dudect_components_fixed_random_DIT.md"}
nulls = []
def is_slh(name):
    return not (name.startswith("sha256") or name.startswith("hmac") or name.startswith("CONTROL"))
for key, fn in files.items():
    p = os.path.join(root, "out", fn)
    hdr = open(p).readline().strip()
    R[key] = "`" + hdr + "`\n\n" + condense.condense(p)
    rws = list(condense.rows(p))
    nulls += [f(r[11]) for r in rws] + [f(r[12]) for r in rws]
    slh = [r for r in rws if is_slh(r[0])]
    R["N_SLH_ROWS"] = str(len(slh))
    flagged = [r[0] + " (" + r[10] + ")" for r in slh if f(r[10]) > 4.5]
    R["FLAG_" + key.split("_")[1]] = ("**none** (largest " + f"{max(f(r[10]) for r in slh):.2f}" + ")") if not flagged else ", ".join("`" + x.split(" (")[0] + "` (" + x.split(" (", 1)[1] for x in flagged)
    print(fn, "SLH rows above 4.5:", flagged, "| sha/hmac rows above 4.5:", sum(1 for r in rws if not is_slh(r[0]) and not r[0].startswith("CONTROL") and f(r[10]) > 4.5))
R["NULL_RANGE"] = f"{min(nulls):.2f} to {max(nulls):.2f}"

# --- diagnostics
def sections(name):
    cur = None; out = []
    for l in rd(name).splitlines():
        if l.startswith("## "):
            cur = [l[3:], []]; out.append(cur)
        elif l.startswith("| ") and not l.startswith("| function") and cur is not None:
            cur[1].append([c.strip() for c in l.strip().strip("|").split("|")])
    return out
agg = {}
rr = []
for fname, dit in (("dudect_diag.md", "0"), ("dudect_diag_dit.md", "1")):
    for title, rws in sections(fname):
        design = ("random vs random (null)" if "random-random" in title else
                  "fixed A vs fixed B" if "fixed-fixed" in title else
                  "fixed (all-zero) vs random" if "all-zero" in title else "fixed (pseudo-random) vs random")
        for r in rws:
            fam = "sha256 (9 lengths)" if r[0].startswith("sha256") else "hmac_sha256 (4 shapes)" if r[0].startswith("hmac") else "thash (4 lengths)"
            agg.setdefault((fam, design, dit), []).append(r)
            if "null" in design:
                rr.append(f(r[10]))
R["RR_MAX"] = f"{max(rr):.2f}"
R["RR_ROWS"] = str(len(rr))
order_f = ["sha256 (9 lengths)", "hmac_sha256 (4 shapes)", "thash (4 lengths)"]
order_d = ["random vs random (null)", "fixed A vs fixed B", "fixed (pseudo-random) vs random", "fixed (all-zero) vs random"]
out = ["| function family | class design | DIT | rows (2 seeds) | rows with max abs t > 4.5 | largest max abs t | trimmed mean diff, range (relative) |", "|---|---|---|---|---|---|---|"]
for dit in ("0", "1"):
    for fam in order_f:
        for d in order_d:
            rws = agg.get((fam, d, dit))
            if not rws:
                continue
            rel = [f(r[8]) for r in rws]
            out.append(f"| {fam} | {d} | {dit} | {len(rws)} | {sum(1 for r in rws if f(r[10]) > 4.5)} | {max(f(r[10]) for r in rws):.2f} | {min(rel):+.4f}% to {max(rel):+.4f}% |")
R["DIAG_SUMMARY"] = "\n".join(out)
# thash rows across all runs
main = {key: {r[0]: f(r[10]) for r in condense.rows(os.path.join(root, "out", fn))} for key, fn in files.items()}
tt = ["| row | fixed = pseudo-random: main run, diag seeds 1001/1002 | fixed = all-zero: main run, diag seeds 1001/1002 | fixed = pseudo-random, DIT=1 |", "|---|---|---|---|"]
for name in ("thash/len=16", "thash/len=32", "thash/len=224", "thash/len=560"):
    dr = [f"{f(r[10]):.2f}" for r in agg[("thash (4 lengths)", "fixed (pseudo-random) vs random", "0")] if r[0] == name]
    dz = [f"{f(r[10]):.2f}" for r in agg[("thash (4 lengths)", "fixed (all-zero) vs random", "0")] if r[0] == name]
    b = lambda x: f"**{x}**" if float(x) > 4.5 else x
    tt.append(f"| {name} | " + ", ".join(b(x) for x in [f"{main['DUDECT_FR'][name]:.2f}"] + dr) + " | " + ", ".join(b(x) for x in [f"{main['DUDECT_FZ'][name]:.2f}"] + dz) + f" | {b(format(main['DUDECT_DIT'][name], '.2f'))} |")
R["THASH_TABLE"] = "\n".join(tt)
t224 = [f"{f(r[10]):.2f}" for r in condense.rows(os.path.join(root, "out", files["DUDECT_FZ"])) if r[0] == "thash/len=224"]
t224d = [f"{f(r[10]):.2f}" for (fam, d, dit), rws in agg.items() if d.startswith("fixed (all-zero)") and dit == "0" for r in rws if r[0] == "thash/len=224"]
R["THASH224"] = f"max |t| = {t224[0]} in the main all-zero run, {' and '.join(t224d)} in the two diagnostic runs"

# --- sign timing
srows = []
for fn in ("dudect_sign_key.md", "dudect_sign_addrnd.md"):
    p = os.path.join(root, "out", fn)
    srows += list(condense.rows(p))
snulls = [f(r[11]) for r in srows] + [f(r[12]) for r in srows]
R["SIGN_NULL"] = f"{max(snulls):.2f}"
# sensitivity reached: standard error of the uncropped mean difference relative to the call time
fz = [r for r in condense.rows(os.path.join(root, "out", files["DUDECT_DIT"])) if len(r) > 14]
short = [100 * f(r[14]) / f(r[5]) for r in fz if int(r[2]) > 1 and not r[0].startswith("CONTROL") and f(r[5]) > 100]
longr = [100 * f(r[14]) / f(r[5]) for r in fz if int(r[2]) == 1 and not r[0].startswith("CONTROL")]
R["SENS"] = f"{min(short):.3f}%-{max(short):.3f}% of the call time for the sub-10-microsecond functions and {min(longr):.3f}%-{max(longr):.3f}% for the longer ones (figures from the DIT=1 run, the one that printed this column), about 0.3% for whole signing"
ctl = [f(r[10]) for fn in files.values() for r in condense.rows(os.path.join(root, "out", fn)) if r[0].startswith("CONTROL")]
R["CTL_RANGE"] = f"{min(ctl):.0f} to {max(ctl):.0f}"
assert len(ctl) == 6 and min(ctl) > 4.5
R["DUDECT_SIGN"] = "\n".join([condense.condense(os.path.join(root, "out", "dudect_sign_key.md")),
                              "\n".join(condense.condense(os.path.join(root, "out", "dudect_sign_addrnd.md")).splitlines()[2:])])
res = []
for r in srows:
    se = f(r[14]); med = f(r[5])
    res.append(f"`{r[0]}`: standard error of the difference of class means {se/1e6:.2f} ms = {100*se/med:.3f}% of the {med/1e9:.2f} s signing time, so a mean shift below roughly {4.5*se/1e6:.1f} ms ({450*se/med:.2f}%) would not reach the threshold")
R["SIGN_RESOLUTION"] = "; ".join(res) + "."

tpl = open(os.path.join(here, "RESULTS.template.md")).read()
for k, v in R.items():
    tpl = tpl.replace("{{" + k + "}}", v)
left = re.findall(r"\{\{[A-Z_0-9]+\}\}", tpl)
assert not left, left
open(os.path.join(root, "RESULTS.md"), "w").write(tpl)
print("wrote RESULTS.md")
