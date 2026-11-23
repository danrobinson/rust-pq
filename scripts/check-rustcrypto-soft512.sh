#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export CARGO_TARGET_DIR="$scratch/target"
python3 scripts/extract-rustcrypto-soft512.py "$scratch/rcsoftware"
mkdir "$scratch/Rcsoft"
(cd "$scratch/rcsoftware" && "$root/.tools/aeneas/charon/bin/charon" cargo --preset=aeneas \
    --start-from 'crate::sha512::soft::unroll::compress' --start-from 'crate::consts::K64' \
    --opaque 'crate::sha512::soft::unroll::rk' --dest-file "$scratch/rcsoft.llbc" -- \
    --target aarch64-unknown-linux-gnu)
.tools/aeneas/bin/aeneas -backend lean -abort-on-error -no-progress-bar -namespace RcSoft \
  -split-files -dest "$scratch/Rcsoft" "$scratch/rcsoft.llbc"
for part in Types Funs; do
  cmp "$scratch/Rcsoft/$part.lean" "lean-hw/Rcsoft/$part.lean"
done
test "$(grep '^axiom ' "$scratch/Rcsoft/FunsExternal_Template.lean")" = \
  'axiom sha512.soft.unroll.rk : Std.Usize → Result Std.U64'
cd lean-hw
lake build Rcsoft.Proof
lake env lean --stdin >"$scratch/axioms" <<'LEAN'
import Rcsoft.Proof
#print axioms slhdsa.RcSoftProof.armstream_contract
LEAN
grep -Fx "'slhdsa.RcSoftProof.armstream_contract' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/axioms"
