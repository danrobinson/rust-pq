#!/bin/bash
# security-hw check: the security theorems of ../security, compiled against the hw-sha2
# translation (../lean-hw). Build, lakefile in step with ../security's, forbidden tokens in every
# source the build compiled (links followed), axioms, headline list (= ../security's).
# Usage: scripts/check.sh [clean]   ("clean" removes this project's own .lake/build first)
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
SETS="128s 128f 192s 192f 256s 256f"
fail=0
out=$(mktemp -d)
[ "${1:-}" = clean ] && rm -rf .lake/build

echo "== 0. lakefile: same libraries as ../security, Slhdsa from ../lean-hw =="
# Every [[lean_lib]] of ../security has the same roots here; srcDir differs only by the move
# one directory over, except Slhdsa (../lean -> ../lean-hw) and the extra Arm library.
libs() { python3 -I - "$1" <<'EOP'
import sys, os, re, json
# the few lakefile.toml forms used here: [[section]], key = "string" / key = [ "a", "b" ]
base = os.path.dirname(os.path.abspath(sys.argv[1]))
libs, cur = [], None
for line in open(sys.argv[1]):
    line = line.strip()
    if line.startswith("[["):
        cur = {} if line == "[[lean_lib]]" else None
        if cur is not None: libs.append(cur)
        continue
    m = re.match(r'(\w+)\s*=\s*(.*)$', line)
    if cur is not None and m: cur[m.group(1)] = json.loads(m.group(2))
for l in libs:
    src = os.path.normpath(os.path.join(base, l.get("srcDir", ".")))
    print(l["name"], src, ",".join(l.get("roots", [l["name"]])))
EOP
}
libs ../security/lakefile.toml | sed "s|$(cd ../lean && pwd)\( \)|$(cd ../lean-hw && pwd)\1|; /^Spec /s|$(cd ../lean-hw && pwd)|$(cd ../lean && pwd)|" | sort > "$out/libs.expected"
libs lakefile.toml | grep -v '^Arm ' | sort > "$out/libs.here"
if diff "$out/libs.expected" "$out/libs.here" > "$out/libs.diff"; then
  echo "same ($(wc -l < "$out/libs.here" | tr -d ' ') libraries, plus Arm from $(libs lakefile.toml | awk '$1=="Arm"{print $2}'))"
else echo "FAIL: libraries differ from ../security's:"; cat "$out/libs.diff"; fail=1; fi

echo "== 1. build (all default targets) =="
start=$(date +%s)
lake build > "$out/build.log" 2>&1
rc=$?
tail -1 "$out/build.log"
echo "build time: $(( $(date +%s) - start )) s"
[ $rc -ne 0 ] && { echo "FAIL: build"; grep -n "error" "$out/build.log" | head -20; fail=1; }
grep -q "declaration uses .sorry." "$out/build.log" && { echo "FAIL: sorry warning in build log"; fail=1; }

echo "== 2. forbidden tokens outside comments, every compiled source (sorry / axiom / native_decide / bv_decide) =="
# Each module built in this package's .lake, mapped to its source through its library's srcDir,
# then the link resolved: so the scan covers what was compiled, wherever the file lives.
libs lakefile.toml > "$out/libs.all"
( cd .lake/build/lib/lean && find . -name '*.olean' | sed 's|^\./||; s|\.olean$||' ) | sort > "$out/mods"
: > "$out/srcs"; miss=0
while read -r m; do
  rel="${m}.lean"; top="${m%%/*}"; mod=$(echo "$m" | tr / .)
  found=""
  while read -r name src roots; do
    for r in ${roots//,/ }; do
      if [ "$mod" = "$r" ] || [ "${mod#"$r".}" != "$mod" ]; then
        [ -f "$src/$rel" ] && { found="$src/$rel"; break 2; }
      fi
    done
  done < "$out/libs.all"
  if [ -n "$found" ]; then python3 -I -c 'import os,sys; print(os.path.realpath(sys.argv[1]))' "$found" >> "$out/srcs"
  else echo "no source for module $mod"; miss=1; fi
done < "$out/mods"
[ $miss -ne 0 ] && { echo "FAIL: built module without a source"; fail=1; }
sort -u "$out/srcs" -o "$out/srcs"
echo "$(wc -l < "$out/mods" | tr -d ' ') modules, $(wc -l < "$out/srcs" | tr -d ' ') distinct source files after links, by directory:"
root=$(cd .. && pwd)
sed "s|^$root/||" "$out/srcs" | awk -F/ '{ print $1 }' | sort | uniq -c
bad=$(while read -r f; do
  perl -0pe 's{/-.*?-/}{ my $c=$&; $c =~ s/[^\n]//g; $c }gse; s/--.*$//mg' "$f" |
    grep -nE '\b(sorry|native_decide|bv_decide)\b|^\s*(private |protected |noncomputable )*axiom\b' |
    sed "s|^|$f:|"
done < "$out/srcs")
if [ -n "$bad" ]; then echo "FAIL:"; echo "$bad"; fail=1; else echo "none"; fi
for f in Slhdsa/Funs.lean Slhdsa/Proofs/ChainTop.lean Slhdsa/Proofs/Hw/Chain.lean Arm.lean; do
  grep -q "/lean-hw/$f$" "$out/srcs" || { echo "FAIL: $f of a lean-hw tree not among the compiled sources"; fail=1; }
done
grep -q "^$root/lean/Slhdsa/Funs.lean$" "$out/srcs" && { echo "FAIL: the portable translation was compiled"; fail=1; }

echo "== 3. #print axioms (the headlines of ../security, here over the hw-sha2 translation) =="
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
#print axioms MIdeal.PureCompression.suf_linear
#print axioms MIdeal.PureCompression.euf_linear
#print axioms MIdeal.PureCompression.suf_internal_linear
#print axioms MIdeal.PureCompression.euf_internal_linear
#print axioms MIdeal.Class128f.forge_at
#print axioms MIdeal.Class128f.forge_count
#print axioms MIdeal.Class128f.forge_fixed
#print axioms MIdeal.Class128f.class_term
#print axioms MIdeal.Wots128f.pre_term
#print axioms MIdeal.Wots128f.tcr_term
#print axioms MIdeal.Wots128f.ud_term
#print axioms MIdeal.Itsr128f.term
#print axioms MIdeal.Msg128f.term
#print axioms MIdeal.Secret128f.term
#print axioms MIdeal.Fors128f.tcr_term
#print axioms MIdeal.Fors128f.dspr_term
#print axioms MIdeal.Sha2_128f.suf
#print axioms MIdeal.Sha2_128f.euf
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
awk -f ../security/scripts/axiom-lines.awk "$out/axioms.raw" > "$out/axioms.txt"
# The environment these theorems live in is the hw-sha2 translation's: its chain kernel exists.
for top in ME2E MIdeal; do
  printf 'import %s\nexample : True := by\n  have := @slhdsa.sha256.hw.chain_all\n  trivial\n' "$top" > "$out/Hw.lean"
  if lake env lean "$out/Hw.lean" > "$out/hw.txt" 2>&1; then echo "slhdsa.sha256.hw.chain_all is in $top's environment (hw-sha2 translation)"
  else echo "FAIL: slhdsa.sha256.hw.chain_all not in $top's environment"; cat "$out/hw.txt" | head -5; fail=1; fi
done
cp "$out/axioms.txt" "$out/axioms.only"
total=$(grep -c "depends on axioms\|does not depend" "$out/axioms.only")
expected=$(grep -c "^#print axioms" "$out/Ax.lean")
badax=$(grep "depends on axioms" "$out/axioms.only" | grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" | grep -v "depends on axioms: \[propext, Quot.sound\]$")
echo "$total / $expected headline theorems reported"
[ "$total" -ne "$expected" ] && { echo "FAIL: missing headline theorems"; fail=1; }
if [ -n "$badax" ]; then echo "FAIL: unexpected axioms:"; echo "$badax"; fail=1; else echo "all within [propext, Classical.choice, Quot.sound]"; fi
if diff <(cut -d"'" -f2 ../security/status/axioms.txt | sort) <(cut -d"'" -f2 "$out/axioms.only" | sort) > /dev/null; then
  echo "same theorem names as ../security/status/axioms.txt (the portable build's record)"
else echo "FAIL: theorem names differ from ../security/status/axioms.txt"; fail=1; fi
mkdir -p status && cp "$out/axioms.only" status/axioms.txt

echo "== 4. headline theorems per set =="
for s in $SETS; do
  echo "-- SLH-DSA-SHA2-$s: $(grep -c "sha2_${s}[._]" "$out/axioms.only") checked, e.g."
  grep -o "'ME2E.sha2_${s}.\(rust\|api\|pure\)[a-z_]*'" "$out/axioms.only" | tr '\n' ' '; echo
done

echo "-- ideal-compression bound (SLH-DSA-SHA2-128s and SHA2-128f): $(grep -c "'MIdeal\." "$out/axioms.only") checked:"
grep -o "'MIdeal\.[A-Za-z0-9_.]*'" "$out/axioms.only" | tr '\n' ' '; echo

if [ $fail -eq 0 ]; then echo "CHECK PASSED"; else echo "CHECK FAILED"; fi
exit $fail
