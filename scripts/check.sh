#!/bin/sh
# Re-run every check: Rust tests, re-extraction, Lean proofs, axiom audit.
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
(cd rust && cargo test --release)
# The opt-in hardware backend: the same tests against it, and its intrinsic
# wrappers against the record in vectors/arm-wrappers.txt.
(cd rust && cargo test --release --features hw-sha2)
# The default build: translation, proofs, specification tests.
./scripts/extract.sh
(cd lean && lake build && lake build spectest)
(cd security && lake build)
# The build with hw-sha2: translation, proofs (the same six theorems, over the
# instruction model in lean-hw/Arm.lean), and that model on the recorded cases.
./scripts/extract-hw.sh
(cd lean-hw && lake build && lake build Slhdsa.Proofs.Hw.Wrappers && lake env lean --run ArmTest.lean ../vectors/arm-wrappers.txt)
if grep -rnE "sorry|native_decide|^axiom|bv_decide" lean/Slhdsa/Proofs lean/Slhdsa/Theorems.lean lean/Spec security/Link security/E2E \
     lean-hw/Arm.lean lean-hw/ArmTest.lean lean-hw/Slhdsa | grep -v "no .native_decide"; then
  echo "FOUND a placeholder or extra axiom"; exit 1
fi
echo "All checks passed. For the (slow) spec-vs-NIST run: lean/.lake/build/bin/spectest vectors/slh-dsa-sha2-128s.json"
