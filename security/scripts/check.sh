#!/bin/bash
# security check: generators, build, forbidden-token grep, axioms, headline list.
# Builds every default target (Link, Reduction, E2E, Ideal, MLink, MReduction, ME2E, MIdeal).
# Usage: scripts/check.sh [clean]   ("clean" removes this project's own .lake/build first)
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
SETS="128s 128f 192s 192f 256s 256f"
fail=0
out=$(mktemp -d)
[ "${1:-}" = clean ] && rm -rf .lake/build

echo "== 0. generators reproduce the checked-in per-set files (and their 128s textual checks pass) =="
# The templates of the ME2E generators are the single-set tree's statements (git commit 26aa3d8),
# read with `git show` from this repository.
export SLHDSA_REPO="$(cd .. && pwd)"
gen=$(mktemp -d)
mkdir -p "$gen/security" "$gen/cwd"
rsync -a --exclude=.lake ./ "$gen/security/"
( cd "$gen/security" && python3 -I ME2E/gen/gen.py > /dev/null && python3 -I scripts/gen_api_rom.py > /dev/null ) \
  || { echo "FAIL: a generator failed (128s textual check?)"; fail=1; }
( cd "$gen/cwd" && for g in gen gen_exp gen_res; do python3 -I "$gen/security/MReduction/gen/$g.py" > /dev/null || exit 1; done ) \
  || { echo "FAIL: an MReduction generator failed"; fail=1; }
gd=$(diff -rq --exclude=.lake . "$gen/security")
if [ -n "$gd" ]; then echo "FAIL: generated files differ:"; echo "$gd"; fail=1; else echo "identical"; fi
rm -rf "$gen"

echo "== 0b. MIdeal statements = the single-set Ideal/E2E statements under the renamings =="
python3 -I scripts/check_ideal128s.py || { echo "FAIL: MIdeal textual check"; fail=1; }

echo "== 0c. root files import every module of their directory; the generic libraries are Spec-free =="
python3 -I - <<'EOP' || fail=1
import os, re, sys
ok = True
imp = lambda f: re.findall(r"^\s*import\s+(\S+)", open(f).read(), re.M)
def mods(d):
    return sorted(os.path.relpath(os.path.join(r, f), ".")[:-5].replace("/", ".")
                  for r, _, fs in os.walk(d) for f in fs if f.endswith(".lean"))
for lib in ("Link", "Reduction", "E2E", "Ideal", "MLink", "MReduction", "ME2E", "MIdeal"):
    have, want = sorted(set(imp(lib + ".lean"))), mods(lib)
    missing = sorted(set(want) - set(have))
    if missing: print(f"FAIL: {lib}.lean does not import", missing); ok = False
    else: print(f"{lib}: {len(want)} modules, all imported by {lib}.lean")
# The generic libraries (Link, Reduction, E2E, Ideal) import nothing of Spec, Slhdsa or the M* libraries.
for lib in ("Link", "Reduction", "E2E", "Ideal"):
    for m in mods(lib):
        for i in imp(os.path.join(*m.split(".")) + ".lean"):
            if i.split(".")[0] in ("Spec", "Slhdsa", "MLink", "MReduction", "ME2E", "MIdeal"):
                print(f"FAIL: {m} imports {i}"); ok = False
# The SLH-DSA-SHA2-128s vocabulary in Link/ mentions no Spec (outside comments).
for f in sorted(os.listdir("Link")):
    t = re.sub(r"/-.*?-/", "", open(os.path.join("Link", f)).read(), flags=re.S)
    t = re.sub(r"--.*", "", t)
    if re.search(r"\bSpec\b|\bspA?\b", t): print(f"FAIL: Link/{f} mentions Spec / sp / spA"); ok = False
if ok: print("Link, Reduction, E2E, Ideal import none of Spec, Slhdsa, M*; Link/ mentions no Spec / sp / spA")
sys.exit(0 if ok else 1)
EOP

echo "== 1. build (all default targets) =="
start=$(date +%s)
lake build > "$out/build.log" 2>&1
rc=$?
tail -1 "$out/build.log"
echo "build time: $(( $(date +%s) - start )) s"
[ $rc -ne 0 ] && { echo "FAIL: build"; grep -n "error" "$out/build.log" | head -20; fail=1; }
grep -q "declaration uses .sorry." "$out/build.log" && { echo "FAIL: sorry warning in build log"; fail=1; }

echo "== 2. forbidden tokens outside comments (sorry / axiom / native_decide / bv_decide) =="
# strip block comments and line comments, then grep; '#print axioms' lines are allowed
bad=$(for f in $(find Link Reduction E2E Ideal MLink MReduction ME2E MIdeal -name '*.lean') \
    Link.lean Reduction.lean E2E.lean Ideal.lean MLink.lean MReduction.lean ME2E.lean MIdeal.lean; do
  perl -0pe 's{/-.*?-/}{ my $c=$&; $c =~ s/[^\n]//g; $c }gse; s/--.*$//mg' "$f" |
    grep -nE '\b(sorry|native_decide|bv_decide)\b|^\s*(private |protected |noncomputable )*axiom\b' |
    sed "s|^|$f:|"
done)
if [ -n "$bad" ]; then echo "FAIL:"; echo "$bad"; fail=1; else echo "none"; fi

echo "== 3. #print axioms (headline theorems) =="
cat > "$out/Ax.lean" <<'EOL'
import MLink
import MReduction
import ME2E
import MIdeal
open MLink MReduction
#print axioms MIdeal.sha2_128s.rust_ideal_security_closed_tight8
#print axioms MIdeal.sha2_128s.rust_ideal_security_closed_pure_tight8
#print axioms MIdeal.sha2_128s.api_ideal_security_closed_pure_tight8
#print axioms MIdeal.sha2_128s.pure_bytes_end_to_end
#print axioms MIdeal.sha2_128s.pureBytesAlg_realCF
#print axioms ShakeSecurity.Rust.keygen
#print axioms ShakeSecurity.Rust.signInternal
#print axioms ShakeSecurity.Rust.verifyInternal
#print axioms ShakeSecurity.Rust.signPure
#print axioms ShakeSecurity.Rust.verifyPure
#print axioms ShakeSecurity.slhdsa_shake_bytes_suf_cma_final
#print axioms ShakeSecurity.slhdsa_shake_bytes_euf_cma_final
#print axioms ShakeSecurity.slhdsa_shake_pure_bytes_suf_cma_final
#print axioms ShakeSecurity.slhdsa_shake_pure_bytes_euf_cma_final
#print axioms ShakeSecurity.oracle_conformance
#print axioms ShakeIdeal.SLHDSA.Security.shakeStrongAdvantage_le_securityBound_validatedParams
#print axioms ShakeIdeal.SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged_validatedParams
#print axioms ShakeIdeal.SLHDSA.Security.shakeAdvantage_le_securityBound_validatedParams
#print axioms ShakeIdeal.SLHDSA.Security.shakeAdvantage_le_securityBound_hedged_validatedParams
#print axioms MLink.sha512_eq
#print axioms MLink.hmacSha512_eq
#print axioms MLink.mgf1Sha512_eq
#print axioms MLink.mgf1Sha256_eq
#print axioms MLink.Hmsg_eq
#print axioms MLink.keygen_eq
#print axioms MLink.sign_eq
#print axioms MLink.slhSign_eq
#print axioms MLink.verify_eq
#print axioms MLink.slhVerify_eq
#print axioms MLink.security_sha2
#print axioms MLink.romScheme_map_romAnswer_sha2
#print axioms MReduction.structural
#print axioms MReduction.slhdsa_sha2_bytes_suf_cma_final
#print axioms MReduction.final_resources_final_sha2
#print axioms ME2E.seeds_split
#print axioms ME2E.sk_split
#print axioms ME2E.pure_bytes_rom_range
#print axioms ME2E.pure_bytes_rom_range_euf
#print axioms Ideal.tablePrimitives_real
#print axioms MIdeal.SkPrf.mixed_shape
#print axioms MIdeal.SkPrf.bound
#print axioms MIdeal.msg_prf_128f
#print axioms MIdeal.Hash128f.thashArityProblemT_eq_tcrProb
#print axioms MIdeal.Hash128f.tcrArityT_bound_multi
#print axioms MIdeal.Hash128f.wotsTcr_bound
#print axioms MIdeal.Hash128f.wotsPre_bound
#print axioms MIdeal.Hash128f.wotsUd_bound
#print axioms MIdeal.Hash128f.wotsUd_bound_ge
#print axioms MIdeal.Hmsg.hmsg_128f
#print axioms MIdeal.Hmsg.Fast128.itsr_bound
#print axioms MIdeal.Hmsg.hmsg_wide
#print axioms MIdeal.Hmsg.itsr_problem
#print axioms MIdeal.Hmsg.itsr_query_bound
#print axioms MIdeal.Sha512.thash_wide
#print axioms MIdeal.Sha512.collision_bound
#print axioms MIdeal.Sha512.ArityTcr.arity_bound
#print axioms MIdeal.Sha512.ArityTcr.mixed_bound
#print axioms MIdeal.SingletonHash.bound
#print axioms MIdeal.SingletonTcr.arityOne_bound
#print axioms MIdeal.SingletonTcr.wots_bound
#print axioms MIdeal.Sha512.readThash_eval
#print axioms MIdeal.Sha512.readThash_bound
#print axioms MIdeal.Sha512.thashBlocks_injective
#print axioms MIdeal.Sha512.readAddress_first
#print axioms MIdeal.Sha512.msg_prf_bound
#print axioms MIdeal.Fors.tcr_bound
#print axioms MIdeal.Fors.dspr_bound
#print axioms ME2E.pureRomScheme_instantiation
#print axioms ME2E.pure_security_sha2
#print axioms ME2E.pure_security_sha2_euf
#print axioms ME2E.pureBytesRomScheme_instantiation
#print axioms ME2E.pure_bytes_security_sha2
#print axioms ME2E.pure_bytes_security_sha2_euf
#print axioms ME2E.sha2_128s.rust_securityG
#print axioms ME2E.sha2_128s.rust_security_linearG
#print axioms ME2E.sha2_128s.rust_pure_securityG
#print axioms ME2E.sha2_128s.rust_pure_security_linearG
#print axioms ME2E.sha2_128s.rust_security_resourcesG
#print axioms ME2E.sha2_128s.api_pure_securityG
EOL
for s in $SETS; do
  for b in bytes_suf_cma_final bytes_euf_cma_final pure_bytes_suf_cma_final pure_bytes_euf_cma_final \
           bytes_suf_cma_linear pure_bytes_suf_cma_linear bytes_suf_cma_deterministic bytes_suf_cma_hedged; do
    echo "#print axioms MReduction.slhdsa_sha2_${s}_${b}" >> "$out/Ax.lean"; done
  echo "#print axioms MReduction.final_resources_final_${s}" >> "$out/Ax.lean"
  for t in rust_security rust_pure_security rust_security_linear rust_pure_security_linear \
           rust_security_deterministic rust_security_hedged rust_pure_security_deterministic \
           rust_pure_security_hedged rust_security_resources rust_pure_security_resources \
           api_keygen_eq api_sign_eq api_verify_eq api_sign_deterministic_eq api_pure_cores \
           api_pure_bytes_end_to_end pure_end_to_end api_pure_end_to_end \
           api_pure_security api_pure_security_linear \
           pure_rom_security api_pure_rom_security rust_pure_rom_security_bytes api_pure_rom_security_bytes; do
    echo "#print axioms ME2E.sha2_${s}.${t}" >> "$out/Ax.lean"; done
done
lake env lean "$out/Ax.lean" > "$out/axioms.raw" 2>&1 || { echo "FAIL: axiom file did not check"; grep error "$out/axioms.raw" | head; fail=1; }
awk -f scripts/axiom-lines.awk "$out/axioms.raw" > "$out/axioms.txt"
total=$(grep -c "depends on axioms\|does not depend" "$out/axioms.txt")
expected=$(grep -c "^#print axioms" "$out/Ax.lean")
badax=$(grep "depends on axioms" "$out/axioms.txt" | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" | grep -v "depends on axioms: \[propext, Quot.sound\]$")
echo "$total / $expected headline theorems reported"
[ "$total" -ne "$expected" ] && { echo "FAIL: missing headline theorems"; fail=1; }
if [ -n "$badax" ]; then echo "FAIL: unexpected axioms:"; echo "$badax"; fail=1; else echo "all within [propext, Classical.choice, Quot.sound]"; fi
cp "$out/axioms.txt" status/axioms.txt

echo "== 4. headline theorems per set =="
for s in $SETS; do
  echo "-- SLH-DSA-SHA2-$s: $(grep -c "sha2_${s}[._]" "$out/axioms.txt") checked, e.g."
  grep -o "'ME2E.sha2_${s}.\(rust\|api\|pure\)[a-z_]*'" "$out/axioms.txt" | tr '\n' ' '; echo
done

echo "-- ideal-compression theorems (closed signature bound for SHA2-128s): $(grep -c "'MIdeal\." "$out/axioms.txt") checked:"
grep -o "'MIdeal\.[A-Za-z0-9_.]*'" "$out/axioms.txt" | tr '\n' ' '; echo

if [ $fail -eq 0 ]; then echo "CHECK PASSED"; else echo "CHECK FAILED"; fi
exit $fail
