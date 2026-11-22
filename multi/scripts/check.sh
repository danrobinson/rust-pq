#!/bin/sh
# Re-run every check of the six-parameter-set tree: the Rust tests in every
# build (NIST ACVP vectors for all six sets, the cross-test against ../rust,
# interoperability with RustCrypto, the interface and checked-signer tests, the
# hash kernels against the `sha2` crate), both re-extractions with Charon +
# Aeneas and their opaque/axiom checks, the refinement proofs of the default
# build (lean/Slhdsa/Proofs, the headline files Theorems, ApiTheorems,
# EncodingTheorems and Compat128) with a check that every headline theorem
# depends only on propext, Classical.choice and Quot.sound, that the hw-sha2
# translation typechecks (it has no proofs yet, see STATUS.md), and the Lean
# specification against the NIST verification vectors.
#
#   scripts/check.sh          everything except the slow spec runs
#   scripts/check.sh full     also runs the spec on keygen and signing vectors
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"

(cd rust && cargo test --release)
(cd rust && cargo test --release --features hw-sha2)
# The experimental, unverified hardware SHA-512 (see STATUS.md).
(cd rust && cargo test --release --features hw-sha2,hw-sha512)

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
for f in Theorems ApiTheorems EncodingTheorems Compat128; do
  n=$(grep -c "^#print axioms" "lean/Slhdsa/$f.lean")
  out=$(cd lean && lake env lean "Slhdsa/$f.lean" 2>&1)
  good=$(echo "$out" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || true)
  if [ "$good" -ne "$n" ] || echo "$out" | grep -q "error"; then
    echo "$out" | grep -E "error|axioms" | head -20
    echo "axiom check FAILED for $f.lean ($good of $n)"; exit 1
  fi
  echo "$f.lean: $n theorems, each depends on axioms: [propext, Classical.choice, Quot.sound]"
done

# The hw-sha2 build: everything but the intrinsic wrappers of sha256::hw::arm,
# which are defined by ../lean-hw's model (linked from lean-hw/Slhdsa).
out=$(./scripts/extract-hw.sh 2>&1) || { echo "$out"; echo "hw-sha2 extraction FAILED"; exit 1; }
echo "$out" | grep "declarations left"
if grep -nE "^(axiom|opaque|noncomputable opaque)|sorry" lean-hw/Slhdsa/Funs.lean lean-hw/Slhdsa/Types.lean; then
  echo "FOUND an axiom or opaque declaration in the hw-sha2 extraction"; exit 1
fi
(cd lean-hw && lake build)

mode=ver
[ "$1" = "full" ] && mode=all
for s in 128s 128f 192s 192f 256s 256f; do
  (cd lean && .lake/build/bin/spectest $s $mode) &
done
fail=0
for job in $(jobs -p); do wait "$job" || fail=1; done
[ "$fail" -eq 0 ] || { echo "spec test FAILED"; exit 1; }
echo "All checks passed."
