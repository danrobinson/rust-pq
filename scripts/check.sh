#!/bin/sh
# Re-run every check of the repository except the quantum one
# (quantum/scripts/check-integration.sh): the Rust tests in every build (NIST
# ACVP vectors for all six sets, interoperability with RustCrypto, the
# interface tests, the hash kernels against the `sha2`
# crate), both re-extractions with Charon + Aeneas and their opaque/axiom
# checks, the refinement proofs of the default build (lean/Slhdsa/Proofs, the
# headline files Theorems, ApiTheorems, EncodingTheorems, Compat128 and AdapterTheorems) with a
# check that every headline theorem depends only on propext, Classical.choice
# and Quot.sound, the same proofs for the hw-sha2 build (lean-hw, over its
# instruction model, with the model's test on the recorded processor outputs
# and the same placeholder and axiom checks), the Lean specification against
# the NIST verification vectors, the constant-time proofs of both builds, the
# security theorems over both builds (security/, security-hw/), and the
# RustCrypto-style adapter (compat/).
#
#   scripts/check.sh          everything except the slow spec runs
#   scripts/check.sh full     also runs the spec on keygen and signing vectors
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"

(cd rust && cargo test --release)
(cd rust && cargo test --release --features hw-sha2)

# The default build: no opaque function, no axiom.
./scripts/extract.sh > /dev/null 2>&1 || { echo "extraction FAILED"; exit 1; }
if ls lean/Slhdsa | grep -q External; then
  echo "FOUND opaque/external declarations in the extraction"; exit 1
fi
if grep -nE "^(axiom|opaque|noncomputable opaque)|sorry" lean/Slhdsa/Funs.lean lean/Slhdsa/Types.lean; then
  echo "FOUND an axiom or opaque declaration in the extraction"; exit 1
fi
(cd lean && lake build Slhdsa Spec spectest)

# No sorry, axiom, native_decide or bv_decide anywhere in the Lean sources.
if grep -rnwE "sorry|admit|native_decide|bv_decide" lean/Slhdsa lean/Spec lean/Spec.lean lean/Slhdsa.lean \
   || grep -rnE "^[[:space:]]*(axiom|opaque) " lean/Slhdsa lean/Spec; then
  echo "FOUND sorry/axiom/native_decide/bv_decide in the proofs"; exit 1
fi

# Every `#print axioms` of the headline files reports the three standard axioms.
for f in Theorems ApiTheorems EncodingTheorems Compat128 AdapterTheorems; do
  n=$(grep -c "^#print axioms" "lean/Slhdsa/$f.lean")
  out=$(cd lean && lake env lean "Slhdsa/$f.lean" 2>&1)
  good=$(echo "$out" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
  if [ "$good" -ne "$n" ] || echo "$out" | grep -q "error"; then
    echo "$out" | grep -E "error|axioms" | head -20
    echo "axiom check FAILED for $f.lean ($good of $n)"; exit 1
  fi
  echo "$f.lean: $n theorems, each depends on axioms: [propext, Classical.choice, Quot.sound]"
done

# The hw-sha2 build: everything but the intrinsic wrappers of sha256::hw::arm and
# sha512::hw::arm, which are defined by the model in lean-hw (Arm.lean,
# Slhdsa/FunsExternal.lean).
out=$(./scripts/extract-hw.sh 2>&1) || { echo "$out"; echo "hw-sha2 extraction FAILED"; exit 1; }
echo "$out" | grep "declarations left"
if grep -nE "^(axiom|opaque|noncomputable opaque)|sorry" lean-hw/Slhdsa/Funs.lean lean-hw/Slhdsa/Types.lean; then
  echo "FOUND an axiom or opaque declaration in the hw-sha2 extraction"; exit 1
fi
# The proofs of the hw-sha2 build (lean-hw/Slhdsa): the same headline files as
# lean/ (linked), over this translation; the build-independent proof files
# linked from lean/Slhdsa/Proofs; this package's own CompressTop.lean,
# Compress512Top.lean, ChainTop.lean, Hw/*.lean (the SHA-256 wrappers, the
# single-block kernel, and the chain kernel generic in N) and Hw512/*.lean (the
# SHA-512 wrappers and kernel).
(cd lean-hw && lake build)

# The model of the wrappers on the cases recorded from a processor
# (vectors/arm-wrappers.txt).
(cd lean-hw && lake build Slhdsa.Proofs.Hw.Wrappers Slhdsa.Proofs.Hw512.Wrappers \
   && lake env lean --run ArmTest.lean ../vectors/arm-wrappers.txt)

# No sorry, axiom, native_decide or bv_decide in any Lean source the hw-sha2
# proofs compile, links followed (the generated translation, this package's
# files, the linked proof files, the wrapper model and Arm.lean).
# (`Arm.haveSha2` and `Arm.haveSha512` are `opaque` Booleans by design, see
# lean-hw/Arm.lean; they are constants, not axioms, and the axiom checks below
# would show one.)
hwsrc=$(find -L lean-hw/Slhdsa lean-hw/Slhdsa.lean lean-hw/ArmTest.lean -name '*.lean')
if grep -nwE "sorry|admit|native_decide|bv_decide" $hwsrc lean-hw/Arm.lean \
   || grep -nE "^[[:space:]]*(axiom|opaque) " $hwsrc \
   || grep -nE "^[[:space:]]*axiom " lean-hw/Arm.lean; then
  echo "FOUND sorry/axiom/native_decide/bv_decide in the hw-sha2 proofs"; exit 1
fi

# Every `#print axioms` of the headline files, compiled against the hw-sha2
# translation, reports the three standard axioms.
for f in Theorems ApiTheorems EncodingTheorems Compat128 AdapterTheorems; do
  n=$(grep -c "^#print axioms" "lean-hw/Slhdsa/$f.lean")
  out=$(cd lean-hw && lake env lean "Slhdsa/$f.lean" 2>&1)
  good=$(echo "$out" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
  if [ "$good" -ne "$n" ] || echo "$out" | grep -q "error"; then
    echo "$out" | grep -E "error|axioms" | head -20
    echo "hw-sha2 axiom check FAILED for $f.lean ($good of $n)"; exit 1
  fi
  echo "lean-hw $f.lean: $n theorems, each depends on axioms: [propext, Classical.choice, Quot.sound]"
done
# And the hardware-specific statements: the three top-level hand-offs, the
# kernels, and the guard theorems for a processor without the instructions.
hwthms="slhdsa.chain_blocks_spec slhdsa.compress_spec slhdsa.hw_chain_all_spec
  slhdsa.hw_compress_block_spec slhdsa.compress_block_undef slhdsa.chain_all_undef
  slhdsa.compress_block_no_spec slhdsa.chain_all_no_spec
  slhdsa.S512.compress_spec slhdsa.hw_compress512_spec slhdsa.hw_compress_block512_spec
  slhdsa.compress_block512_undef slhdsa.compress_block512_no_spec"
n=0
prog="import Slhdsa.Proofs.ChainTop
import Slhdsa.Proofs.CompressTop
import Slhdsa.Proofs.Compress512Top"
for t in $hwthms; do n=$((n + 1)); prog="$prog
#print axioms $t"; done
out=$(cd lean-hw && echo "$prog" | lake env lean --stdin 2>&1)
good=$(echo "$out" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
if [ "$good" -ne "$n" ] || echo "$out" | grep -q "error"; then
  echo "$out" | head -20
  echo "hw-sha2 axiom check FAILED for the kernel and guard theorems ($good of $n)"; exit 1
fi
echo "lean-hw kernel and guard theorems: $n, each depends on axioms: [propext, Classical.choice, Quot.sound]"
# `sha256::hw_active` and `sha512::hw_active` return the feature tests' answers (by `rfl`;
# they use a subset of the three standard axioms: [propext, Quot.sound]).
out=$(cd lean-hw && printf 'import Slhdsa.Proofs.Compress512Top\n#print axioms slhdsa.sha256_hw_active_eq\n#print axioms slhdsa.sha512_hw_active_eq\n' | lake env lean --stdin 2>&1)
[ "$(echo "$out" | grep -c "depends on axioms: \[propext, Quot.sound\]$")" -eq 2 ] || { echo "$out"; echo "hw_active check FAILED"; exit 1; }
echo "lean-hw hw_active theorems: 2, each depends on axioms: [propext, Quot.sound]"

mode=ver
[ "$1" = "full" ] && mode=all
for s in 128s 128f 192s 192f 256s 256f; do
  (cd lean && .lake/build/bin/spectest $s $mode) &
done
fail=0
for job in $(jobs -p); do wait "$job" || fail=1; done
[ "$fail" -eq 0 ] || { echo "spec test FAILED"; exit 1; }
# Constant time (portable build): regenerate the instrumented copy of the translation and the
# per-set headline files, then the checker, the erasure theorems and the headline statements.
./scripts/ct-gen.sh
python3 -I scripts/gen/ct_thms.py > /dev/null
(cd lean && lake build Ct)
if grep -RnwE "sorry|admit|native_decide|bv_decide" lean/Ct lean/Ct.lean \
   || grep -RnE "^[[:space:]]*(axiom|opaque) " lean/Ct lean/Ct.lean; then
  echo "FOUND sorry/axiom/native_decide/bv_decide in the constant-time proofs"; exit 1
fi
for f in Theorems Sets/Sha2_128s Sets/Sha2_128f Sets/Sha2_192s Sets/Sha2_192f Sets/Sha2_256s Sets/Sha2_256f; do
  n=$(grep -c "^#print axioms" "lean/Ct/$f.lean")
  out=$(cd lean && lake env lean "Ct/$f.lean" 2>&1)
  good=$(echo "$out" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
  if [ "$good" -ne "$n" ] || echo "$out" | grep -q "error"; then
    echo "$out" | grep -E "error|axioms" | head -20
    echo "axiom check FAILED for Ct/$f.lean ($good of $n)"; exit 1
  fi
  echo "Ct/$f.lean: $n theorems, each depends on axioms: [propext, Classical.choice, Quot.sound]"
done

# Constant time (hw-sha2 build): the same headline files over the hw translation.
./scripts/ct-gen.sh hw
(cd lean-hw && lake build Ct)
if grep -RnwE "sorry|admit|native_decide|bv_decide" lean-hw/Ct lean-hw/Ct.lean \
   || grep -RnE "^[[:space:]]*(axiom|opaque) " lean-hw/Ct lean-hw/Ct.lean; then
  echo "FOUND sorry/axiom/native_decide/bv_decide in the hw constant-time proofs"; exit 1
fi
for f in Theorems Sets/Sha2_128s Sets/Sha2_128f Sets/Sha2_192s Sets/Sha2_192f Sets/Sha2_256s Sets/Sha2_256f; do
  n=$(grep -c "^#print axioms" "lean-hw/Ct/$f.lean")
  out=$(cd lean-hw && lake env lean "Ct/$f.lean" 2>&1)
  good=$(echo "$out" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
  if [ "$good" -ne "$n" ] || echo "$out" | grep -q "error"; then
    echo "$out" | grep -E "error|axioms" | head -20
    echo "axiom check FAILED for lean-hw Ct/$f.lean ($good of $n)"; exit 1
  fi
  echo "lean-hw Ct/$f.lean: $n theorems, each depends on axioms: [propext, Classical.choice, Quot.sound]"
done

# Security link, both builds.
# (Each prints its last line; on failure, its last 40 lines, and the check stops.)
for d in security security-hw; do
  out=$(cd "$d" && scripts/check.sh 2>&1) || { echo "$out" | tail -40; echo "$d check FAILED"; exit 1; }
  echo "$d: $(echo "$out" | grep "headline theorems reported") $(echo "$out" | tail -1)"
done

# Adapter crate.
./scripts/check-compat-proof.sh
for feat in "" "--features hw-sha2"; do
  # shellcheck disable=SC2086
  out=$(cd compat && cargo test --release $feat 2>&1) || { echo "$out" | tail -40; echo "compat tests FAILED ($feat)"; exit 1; }
  echo "$out" | grep "test result"
done

echo "All checks passed."
