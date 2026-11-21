#!/bin/sh
# Re-run every check: Rust tests, re-extraction, Lean proofs, axiom audit.
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
(cd rust && cargo test --release)
# The opt-in hardware backend (not covered by the proofs): same tests against it.
(cd rust && cargo test --release --features hw-sha2)
./scripts/extract.sh
(cd lean && lake build && lake build spectest)
(cd security && lake build)
if grep -rnE "sorry|native_decide|^axiom|bv_decide" lean/Slhdsa/Proofs lean/Slhdsa/Theorems.lean lean/Spec security/Link security/E2E | grep -v "no .native_decide"; then
  echo "FOUND a placeholder or extra axiom"; exit 1
fi
echo "All checks passed. For the (slow) spec-vs-NIST run: lean/.lake/build/bin/spectest vectors/slh-dsa-sha2-128s.json"
