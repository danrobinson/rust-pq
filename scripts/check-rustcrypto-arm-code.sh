#!/bin/sh
# Re-emit the dependency used by the production crate on each release target.
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export CARGO_TARGET_DIR="$scratch/target"
export RUSTFLAGS="--emit=asm,link"
for target in aarch64-unknown-linux-gnu aarch64-apple-darwin; do
  cargo build --manifest-path rust/Cargo.toml --locked --release \
    --features platform-sha2 --target "$target"
  python3 - "$CARGO_TARGET_DIR/$target/release" "$scratch/$target.s" <<'PY'
from pathlib import Path
import shutil
import sys

source, dest = map(Path, sys.argv[1:])
assembly, = source.rglob("sha2-*.s")
shutil.copyfile(assembly, dest)
PY
done
python3 scripts/check-rustcrypto-arm-code.py "$scratch/aarch64-unknown-linux-gnu.s" \
  "$scratch/aarch64-apple-darwin.s" "$scratch/Code.lean"
cmp "$scratch/Code.lean" lean-hw/Rcarmcode/Code.lean
python3 scripts/check-rustcrypto-arm-code.py --bits 512 "$scratch/aarch64-unknown-linux-gnu.s" \
  "$scratch/aarch64-apple-darwin.s" "$scratch/Code512.lean"
cmp "$scratch/Code512.lean" lean-hw/Rcarmcode/Code512.lean
cd "$root/lean-hw"
lake build Rcarmcode.Proof Rcarmcode.Proof512
lake env lean --stdin >"$scratch/axioms" <<'LEAN'
import Rcarmcode.Proof
import Rcarmcode.Proof512
#print axioms slhdsa.RcArmCode.S512.armstream_contract
#print axioms slhdsa.RcArmCode.armstream_contract
LEAN
grep -Fx "'slhdsa.RcArmCode.armstream_contract' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/axioms"
grep -Fx "'slhdsa.RcArmCode.S512.armstream_contract' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/axioms"
