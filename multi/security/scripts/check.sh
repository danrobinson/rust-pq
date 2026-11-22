#!/bin/bash
# multi/security check: build, forbidden-token grep, shim fidelity, axioms, headline list.
# Usage: scripts/check.sh [clean]   ("clean" removes this project's own .lake/build first)
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
SETS="128s 128f 192s 192f 256s 256f"
fail=0
out=$(mktemp -d)
[ "${1:-}" = clean ] && rm -rf .lake/build

echo "== 0. generators reproduce the checked-in per-set files (and their 128s textual checks pass) =="
gen=$(mktemp -d)
mkdir -p "$gen/multi/security" "$gen/security"
rsync -a --exclude=.lake ./ "$gen/multi/security/"
cp -R ../../security/E2E "$gen/security/E2E"
( cd "$gen/multi/security" && python3 -I ME2E/gen/gen.py > /dev/null && python3 -I scripts/gen_api_rom.py > /dev/null ) \
  || { echo "FAIL: a generator failed (128s textual check?)"; fail=1; }
gd=$(diff -rq --exclude=.lake . "$gen/multi/security")
if [ -n "$gd" ]; then echo "FAIL: generated files differ:"; echo "$gd"; fail=1; else echo "identical"; fi
rm -rf "$gen"

echo "== 1. build (MLink MReduction ME2E) =="
start=$(date +%s)
# touch our own sources' build products so that #print axioms output is replayed in full
lake build MLink MReduction ME2E > "$out/build.log" 2>&1
rc=$?
tail -1 "$out/build.log"
echo "build time: $(( $(date +%s) - start )) s"
[ $rc -ne 0 ] && { echo "FAIL: build"; grep -n "error" "$out/build.log" | head -20; fail=1; }
grep -q "declaration uses .sorry." "$out/build.log" && { echo "FAIL: sorry warning in build log"; fail=1; }

echo "== 2. forbidden tokens outside comments (sorry / axiom / native_decide / bv_decide) =="
# strip block comments and line comments, then grep; '#print axioms' lines are allowed
bad=$(for f in MLink/*.lean MReduction/*.lean ME2E/*.lean ME2E/*/*.lean shim/*/*.lean MLink.lean MReduction.lean ME2E.lean \
    ../../security/E2E/GuardedRom.lean ../../security/E2E/CodedRom.lean; do
  perl -0pe 's{/-.*?-/}{ my $c=$&; $c =~ s/[^\n]//g; $c }gse; s/--.*$//mg' "$f" |
    grep -nE '\b(sorry|native_decide|bv_decide)\b|^\s*(private |protected |noncomputable )*axiom\b' |
    sed "s|^|$f:|"
done)
if [ -n "$bad" ]; then echo "FAIL:"; echo "$bad"; fail=1; else echo "none"; fi

echo "== 3. shim fidelity =="
d=$(diff ../../security/Reduction/PrfDomainNonVacuity.lean shim/Reduction/PrfDomainNonVacuity.lean | grep -c '^>')
r=$(diff ../../security/Reduction/PrfDomainNonVacuity.lean shim/Reduction/PrfDomainNonVacuity.lean | grep -c '^<')
echo "shim/Reduction/PrfDomainNonVacuity.lean vs security: $d lines added, $r removed (expected 0 added, 7 removed: prf_128s_spec)"
[ "$d" -ne 0 ] || [ "$r" -ne 7 ] && { echo "FAIL: shim differs unexpectedly"; fail=1; }

echo "== 4. #print axioms (our modules) =="
cat > "$out/Ax.lean" <<'EOL'
import MLink
import MReduction
import ME2E
open MLink MReduction
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
#print axioms ME2E.spec_slhSignChecked_eq
#print axioms ME2E.seeds_split
#print axioms ME2E.sk_split
#print axioms ME2E.pureRomScheme_instantiation
#print axioms ME2E.pure_security_sha2
#print axioms ME2E.pure_security_sha2_euf
#print axioms ME2E.pureBytesRomScheme_instantiation
#print axioms ME2E.pure_bytes_security_sha2
#print axioms ME2E.pure_bytes_security_sha2_euf
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
           api_sign_checked_eq_sign api_sign_deterministic_checked_eq api_keygen_checked_eq \
           keygen_internal_checked_eq api_checked_pure_cores \
           pure_rom_security api_pure_rom_security rust_pure_rom_security_bytes api_pure_rom_security_bytes; do
    echo "#print axioms ME2E.sha2_${s}.${t}" >> "$out/Ax.lean"; done
done
lake env lean "$out/Ax.lean" > "$out/axioms.txt" 2>&1 || { echo "FAIL: axiom file did not check"; grep error "$out/axioms.txt" | head; fail=1; }
total=$(grep -c "depends on axioms\|does not depend" "$out/axioms.txt")
expected=$(grep -c "^#print axioms" "$out/Ax.lean")
badax=$(grep "depends on axioms" "$out/axioms.txt" | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" | grep -v "depends on axioms: \[propext, Quot.sound\]$")
echo "$total / $expected headline theorems reported"
[ "$total" -ne "$expected" ] && { echo "FAIL: missing headline theorems"; fail=1; }
if [ -n "$badax" ]; then echo "FAIL: unexpected axioms:"; echo "$badax"; fail=1; else echo "all within [propext, Classical.choice, Quot.sound]"; fi
cp "$out/axioms.txt" status/axioms.txt

echo "== 5. headline theorems per set =="
for s in $SETS; do
  echo "-- SLH-DSA-SHA2-$s: $(grep -c "sha2_${s}[._]" "$out/axioms.txt") checked, e.g."
  grep -o "'ME2E.sha2_${s}.\(rust\|api\|pure\)[a-z_]*'" "$out/axioms.txt" | tr '\n' ' '; echo
done

if [ $fail -eq 0 ]; then echo "CHECK PASSED"; else echo "CHECK FAILED"; fi
exit $fail
