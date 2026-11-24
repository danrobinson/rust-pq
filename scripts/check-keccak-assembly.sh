#!/bin/sh
# Recompile the x86-64 Linux release and verify the exact AVX-512 permutation
# instruction stream against the independently defined FIPS 202 permutation.
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
(cd rust && CARGO_TARGET_DIR="$scratch/target" cargo rustc --locked --release \
    --features "${1:-platform-sha2}" --target x86_64-unknown-linux-gnu --lib -- --emit asm)
find "$scratch/target" -type f -name 'slhdsa*.s' > "$scratch/outputs"
test "$(wc -l < "$scratch/outputs")" -eq 1
python3 scripts/check-keccak-assembly.py "$(cat "$scratch/outputs")" "$scratch/Code.lean"
cmp "$scratch/Code.lean" lean-hw/Keccakasm/Code.lean
(cd lean-hw && lake build Keccakasm.Proof && lake env lean --stdin > "$scratch/axioms" <<'LEAN'
import Keccakasm.Proof
#print axioms slhdsa.KeccakAsm.permutation_fips
LEAN
)
grep -Fx "'slhdsa.KeccakAsm.permutation_fips' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/axioms"
