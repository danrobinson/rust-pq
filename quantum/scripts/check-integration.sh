#!/usr/bin/env bash
# check-integration.sh — reproducible check of quantum/Integration/*.lean
#
# USAGE
#   cd quantum && scripts/check-integration.sh            # full check
#   SKIP_DEFAULT_BUILD=1 scripts/check-integration.sh     # skip step 1 (`lake build` of the default target)
#   ALLOW_MTIME_SKEW=1  scripts/check-integration.sh      # downgrade check (2d) below to a warning
#
# WHAT IT DOES
#   1. `lake build` in quantum/ (default target), then `lake build` of every `PQ.*` or `VCVio.*` module that
#      an Integration file imports (these are not all in the default target).
#   2. Checks the compiled modules of ../security that the Integration files import
#      (transitively), WITHOUT running lake in ../security.  For every such module it fails if
#        (a) its .olean or its lake .trace file is missing;
#        (b) the source file changed since the olean was built: Lake's text hash of the current
#            source differs from the hash recorded in the module's .trace;
#        (c) the olean on disk is not the one the trace describes (.olean.hash mismatch);
#        (d) the olean is older than the olean of a module it imports (it was compiled against
#            an older version of that import and has not been rebuilt yet).
#   3. Compiles every Integration/*.lean, in import order, with plain `lean` and
#        LEAN_PATH = (lake env of quantum) : security oleans : aeneas oleans : integration oleans
#      writing oleans to quantum/.lake/build/integration (so Integration files can import each
#      other).  Fails on any Lean error, any `sorry`, and any axiom in the `#print axioms` output
#      other than propext, Classical.choice, Quot.sound.
#   4. Prints every checked theorem with its axioms.
#
# EXIT STATUS  0 = everything passed;  non-zero = failure, with a line starting `FAIL:`.
# Nothing under ../security or ../.tools is written.

set -uo pipefail
export PATH="$HOME/.elan/bin:$PATH"

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
SEC="$(cd "$ROOT/../security" 2>/dev/null && pwd)" || { echo "FAIL: ../security not found"; exit 2; }
SECLIB="$SEC/.lake/build/lib/lean"
AENLIB="$ROOT/../.tools/aeneas/backends/lean/.lake/build/lib/lean"
OUT="$ROOT/.lake/build/integration"
cd "$ROOT"

fail() { echo; echo "FAIL: $*"; exit 1; }

[ -d "$SECLIB" ] || fail "no compiled security library at $SECLIB"
[ -d "$AENLIB" ] || fail "no compiled aeneas library at $AENLIB"
ls Integration/*.lean >/dev/null 2>&1 || fail "no Integration/*.lean files"

echo "== 1. build quantum/ =="
if [ "${SKIP_DEFAULT_BUILD:-0}" != "1" ]; then
  lake build 2>&1 | tail -3
  [ "${PIPESTATUS[0]}" -eq 0 ] || fail "lake build (default target of quantum/) failed"
else
  echo "(default target skipped: SKIP_DEFAULT_BUILD=1)"
fi
PROOF_MODULES=$(grep -Eh '^import (PQ|VCVio)\.' Integration/*.lean | awk '{print $2}' | sort -u | tr '\n' ' ')
if [ -n "$PROOF_MODULES" ]; then
  # shellcheck disable=SC2086
  lake build $PROOF_MODULES 2>&1 | tail -1
  [ "${PIPESTATUS[0]}" -eq 0 ] || fail "lake build of $PROOF_MODULES failed"
fi

echo "== 2. security oleans: present and up to date =="
python3 - "$ROOT" "$SEC" "$SECLIB" "$HERE/LakeTextHash.lean" <<'PY' || fail "security oleans missing or stale (see above); rebuild ../security (in ../security: lake build) and re-run"
import json, os, re, subprocess, sys, glob
root, sec, seclib, helper = sys.argv[1:5]
allow_skew = os.environ.get("ALLOW_MTIME_SKEW") == "1"
# library roots owned by ../security (from its lakefile)
roots = re.findall(r'\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"', open(os.path.join(sec, "lakefile.toml")).read())
imp_re = re.compile(r'^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.«»]+)', re.M)
def imports(path):
    return imp_re.findall(open(path, encoding="utf-8").read())
def owned(m): return m.split(".")[0] in roots
def base(m): return os.path.join(seclib, *m.split("."))
problems, info, seen, todo = [], {}, set(), []
for f in sorted(glob.glob(os.path.join(root, "Integration", "*.lean"))):
    todo += [m for m in imports(f) if owned(m)]
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.add(m)
    olean, trace = base(m) + ".olean", base(m) + ".trace"
    if not os.path.exists(olean):
        problems.append(f"MISSING: {m}: no olean ({olean})"); continue
    if not os.path.exists(trace):
        problems.append(f"MISSING: {m}: no lake trace ({trace})"); continue
    t = json.load(open(trace))
    src = [(p, h) for (p, h) in (x for x in t.get("inputs", []) if isinstance(x[1], str)) if p.endswith(".lean")]
    if not src:
        problems.append(f"MISSING: {m}: trace records no source file"); continue
    spath, shash = src[0]
    if not os.path.exists(spath):
        problems.append(f"MISSING: {m}: source {spath} no longer exists"); continue
    info[m] = dict(olean=olean, src=spath, hash=shash, out=t.get("outputs", {}))
    todo += [n for n in imports(spath) if owned(n)]
# (b) source hashes, computed by Lake's own function
paths = [v["src"] for v in info.values()]
cur = {}
for i in range(0, len(paths), 200):
    r = subprocess.run(["lean", "--run", helper] + paths[i:i+200], capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stdout, r.stderr); print("could not run the Lake text-hash helper"); sys.exit(1)
    for line in r.stdout.splitlines():
        h, p = line.split(" ", 1); cur[p] = h
for m, v in sorted(info.items()):
    if cur.get(v["src"]) != v["hash"]:
        problems.append(f"STALE: {m}: source changed since its olean was built "
                        f"({os.path.relpath(v['src'], sec)}: lake hash now {cur.get(v['src'])}, olean built from {v['hash']})")
    # (c) olean on disk is the one of the trace
    hf = v["olean"] + ".hash"
    o = v["out"].get("o")
    want = (o[0] if isinstance(o, list) and o else o or "").split(".")[0]
    if os.path.exists(hf) and want and open(hf).read().strip() != want:
        problems.append(f"STALE: {m}: olean on disk does not match its lake trace")
# (d) compiled after its imports
skew = []
for m, v in sorted(info.items()):
    for n in imports(v["src"]):
        if n in info and os.path.getmtime(v["olean"]) < os.path.getmtime(info[n]["olean"]):
            skew.append(f"STALE: {m}: olean is older than the olean of its import {n} (not rebuilt yet)")
if allow_skew:
    for s in skew: print("warning (ALLOW_MTIME_SKEW=1): " + s)
else:
    problems += skew
print(f"checked {len(seen)} modules of ../security ({len(info)} with source hash)")
if problems:
    for p in problems: print("  " + p)
    print(f"{len(problems)} problem(s)")
    sys.exit(1)
print("all present and up to date")
PY

echo "== 3. compile Integration/*.lean =="
mkdir -p "$OUT/Integration"
LP="$(lake env printenv LEAN_PATH):$SECLIB:$AENLIB:$OUT"
# import order among Integration files
ORDER=$(python3 - <<'PY'
import glob, os, re
files = {os.path.splitext(os.path.basename(f))[0]: f for f in glob.glob("Integration/*.lean")}
deps = {k: [m for m in re.findall(r'^import\s+Integration\.(\w+)', open(f).read(), re.M) if m in files] for k, f in files.items()}
done = []
def visit(k, stack=()):
    if k in done: return
    assert k not in stack, "import cycle among Integration files"
    for d in deps[k]: visit(d, stack + (k,))
    done.append(k)
for k in sorted(files): visit(k)
print(" ".join(done))
PY
) || fail "could not order the Integration files"
LOG="$OUT/check.log"; : > "$LOG"
for name in $ORDER; do
  echo "-- Integration/$name.lean"
  { echo "=== Integration/$name.lean"; } >> "$LOG"
  LEAN_PATH="$LP" lean -o "$OUT/Integration/$name.olean" "Integration/$name.lean" >> "$LOG" 2>&1
  rc=$?
  if [ $rc -ne 0 ]; then
    sed -n "/=== Integration\/$name.lean/,\$p" "$LOG" | head -40
    fail "Lean reported errors in Integration/$name.lean (exit $rc); full log: $LOG"
  fi
done
grep -n "error" "$LOG" | head -5 | grep -q . && { grep -n "error" "$LOG" | head -5; fail "Lean errors in the log $LOG"; }
grep -n "declaration uses .sorry." "$LOG" | head -5 | grep -q . && fail "a declaration uses sorry (see $LOG)"

echo "== 4. axioms =="
python3 - "$LOG" <<'PY' || fail "non-standard axioms (or no '#print axioms' output) — see above"
import re, sys
txt = open(sys.argv[1]).read()
ok = {"propext", "Classical.choice", "Quot.sound"}
bad = n = 0
cur = None
for part in re.split(r'^=== ', txt, flags=re.M):
    if not part.strip(): continue
    fname, body = part.split("\n", 1)
    print(fname)
    for name, axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", body, flags=re.S):
        axl = [a.strip() for a in axs.replace("\n", " ").split(",") if a.strip()]
        extra = [a for a in axl if a not in ok]
        n += 1; bad += bool(extra)
        print(f"  {'BAD ' if extra else 'ok  '} {name}: [{', '.join(axl)}]")
    for name in re.findall(r"'([^']+)' does not depend on any axioms", body):
        n += 1; print(f"  ok   {name}: []")
print(f"{n} theorems checked, {bad} with non-standard axioms")
sys.exit(1 if bad or n == 0 else 0)
PY

echo
echo "PASS: default target built, security oleans up to date, all Integration files compiled, only standard axioms."
