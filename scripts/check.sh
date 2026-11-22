#!/bin/sh
# Re-run every check: Rust tests, re-extraction, Lean proofs, axiom audit.
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
(cd rust && cargo test --release)
# The opt-in hardware backend: the same tests against it, and its intrinsic
# wrappers against the record in vectors/arm-wrappers.txt.
(cd rust && cargo test --release --features hw-sha2)
# The RustCrypto-compatible adapter (unverified glue): the same source against
# both crates, with and without the hardware backend.
(cd compat && cargo test && cargo test --features hw-sha2)
# The default build: translation, proofs, specification tests.
./scripts/extract.sh
(cd lean && lake build && lake build spectest)
# Constant time (default build): regenerate the instrumented copy of the translation, then the
# checker, the erasure theorems and the headline statements.
./scripts/ct-gen.sh
(cd lean && lake build Ct)
(cd security && lake build)
# The build with hw-sha2: translation, proofs (the same six theorems, over the
# instruction model in lean-hw/Arm.lean), and that model on the recorded cases.
./scripts/extract-hw.sh
(cd lean-hw && lake build && lake build Slhdsa.Proofs.Hw.Wrappers && lake env lean --run ArmTest.lean ../vectors/arm-wrappers.txt)
# Constant time for the hw-sha2 build: the same statements, over this build's translation and a
# leakage model of the intrinsic wrappers (lean-hw/Ct/ModelBuild.lean).
./scripts/ct-gen.sh hw
(cd lean-hw && lake build Ct)
# The security statements of security/, compiled against the hw-sha2 build's translation.
# (It compiles its own copies of the security libraries: about four minutes from clean.)
(cd security-hw && lake build)
if grep -rnE --include='*.lean' "sorry|native_decide|^axiom|bv_decide" lean/Slhdsa/Proofs lean/Slhdsa/Theorems.lean lean/Slhdsa/ApiTheorems.lean lean/Spec lean/Ct lean/Ct.lean lean-hw/Ct lean-hw/Ct.lean \
     security/Link security/E2E security/Reduction security/Ideal security/Link.lean security/E2E.lean security/Reduction.lean security/Ideal.lean \
     lean-hw/Arm.lean lean-hw/ArmTest.lean lean-hw/Slhdsa | grep -v "no .native_decide"; then
  echo "FOUND a placeholder or extra axiom"; exit 1
fi
echo "All checks passed. For the (slow) spec-vs-NIST run: lean/.lake/build/bin/spectest vectors/slh-dsa-sha2-128s.json"
