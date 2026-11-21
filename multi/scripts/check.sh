#!/bin/sh
# Re-run every check for the six-parameter-set tree: Rust tests (NIST ACVP
# vectors for all six sets, cross-test against ../rust), re-extraction with
# Charon + Aeneas, the Lean proofs, the axiom audit, and the Lean
# specification against the NIST verification vectors.
#
#   scripts/check.sh          everything except the slow spec keygen/signing runs
#   scripts/check.sh full     also runs the spec on keygen and signing vectors
#                             (minutes for the f sets, much longer for the s sets)
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"

(cd rust && cargo test --release)

./scripts/extract.sh > /dev/null 2>&1 || { echo "extraction FAILED"; exit 1; }
if ls lean/Slhdsa | grep -q External; then
  echo "FOUND opaque/external declarations in the extraction"; exit 1
fi
if grep -nE "^(axiom|opaque|noncomputable opaque)|sorry" lean/Slhdsa/Funs.lean lean/Slhdsa/Types.lean; then
  echo "FOUND an axiom or opaque declaration in the extraction"; exit 1
fi

(cd lean && lake build && lake build spectest)

if grep -rnE "sorry|native_decide|^axiom|bv_decide|admit" lean/Slhdsa/Proofs lean/Slhdsa/Theorems.lean lean/Spec; then
  echo "FOUND a placeholder or extra axiom"; exit 1
fi

# Axiom audit: every headline theorem must depend on the three standard axioms only.
(cd lean && lake env lean Slhdsa/Theorems.lean) > lean/.lake/axioms.txt
total=$(grep -c "depends on axioms" lean/.lake/axioms.txt)
good=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" lean/.lake/axioms.txt)
echo "axiom audit: $good of $total headline theorems use only [propext, Classical.choice, Quot.sound]"
if [ "$total" -ne 37 ] || [ "$good" -ne 37 ]; then
  cat lean/.lake/axioms.txt; echo "axiom audit FAILED"; exit 1
fi

mode=ver
[ "$1" = "full" ] && mode=all
for s in 128s 128f 192s 192f 256s 256f; do
  (cd lean && .lake/build/bin/spectest $s $mode) &
done
fail=0
for job in $(jobs -p); do wait "$job" || fail=1; done
[ "$fail" -eq 0 ] || { echo "spec test FAILED"; exit 1; }
echo "All checks passed."
