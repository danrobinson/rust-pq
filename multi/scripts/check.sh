#!/bin/sh
# Re-run the checks that hold for the six-parameter-set tree at this stage:
# the Rust tests in every build (NIST ACVP vectors for all six sets, the
# cross-test against ../rust, interoperability with RustCrypto, the interface
# and checked-signer tests, the hash kernels against the `sha2` crate), both
# re-extractions with Charon + Aeneas and their opaque/axiom checks, that both
# translations typecheck, and the Lean specification against the NIST
# verification vectors.
#
# The refinement proofs under lean/Slhdsa/Proofs describe the previous Rust
# code and are stale (see STATUS.md); they are not built unless asked:
#
#   scripts/check.sh          everything except the stale proofs and the slow spec runs
#   scripts/check.sh full     also runs the spec on keygen and signing vectors
#   scripts/check.sh proofs   also tries the stale proofs (expected to FAIL)
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
(cd lean && lake build Slhdsa.Funs Spec spectest)

# The hw-sha2 build: everything but the intrinsic wrappers of sha256::hw::arm,
# which are defined by ../lean-hw's model (linked from lean-hw/Slhdsa).
out=$(./scripts/extract-hw.sh 2>&1) || { echo "$out"; echo "hw-sha2 extraction FAILED"; exit 1; }
echo "$out" | grep "declarations left"
if grep -nE "^(axiom|opaque|noncomputable opaque)|sorry" lean-hw/Slhdsa/Funs.lean lean-hw/Slhdsa/Types.lean; then
  echo "FOUND an axiom or opaque declaration in the hw-sha2 extraction"; exit 1
fi
(cd lean-hw && lake build)

if [ "$1" = "proofs" ]; then
  (cd lean && lake build) || { echo "the stale proofs do not build (expected at this stage)"; exit 1; }
fi

mode=ver
[ "$1" = "full" ] && mode=all
for s in 128s 128f 192s 192f 256s 256f; do
  (cd lean && .lake/build/bin/spectest $s $mode) &
done
fail=0
for job in $(jobs -p); do wait "$job" || fail=1; done
[ "$fail" -eq 0 ] || { echo "spec test FAILED"; exit 1; }
echo "All checks passed (the refinement proofs are stale and were not built)."
