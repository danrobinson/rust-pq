#!/bin/sh
# Check either or both Arm software fallback selections from the locked upstream source.
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export CARGO_TARGET_DIR="$scratch/target"
if [ "$#" = 0 ]; then set -- 256 512; fi
for bits do
  case "$bits" in
    256) package=Rcsoft256; namespace=RcSoft256; word=32 ;;
    512) package=Rcsoft; namespace=RcSoft; word=64 ;;
    *) echo "Expected 256 or 512" >&2; exit 2 ;;
  esac
  name=$(echo "$package" | tr '[:upper:]' '[:lower:]')
  theorem="slhdsa.${namespace}Proof.armstream_contract"
  crate="$scratch/crate$bits"
  python3 scripts/extract-rustcrypto-soft.py --bits "$bits" "$crate"
  mkdir "$scratch/$package"
  (cd "$crate" && "$root/.tools/aeneas/charon/bin/charon" cargo --preset=aeneas \
      --start-from "crate::sha${bits}::soft::unroll::compress" --start-from "crate::consts::K$word" \
      --opaque "crate::sha${bits}::soft::unroll::rk" --dest-file "$scratch/$name.llbc" -- \
      --target aarch64-unknown-linux-gnu)
  .tools/aeneas/bin/aeneas -backend lean -abort-on-error -no-progress-bar -namespace "$namespace" \
    -split-files -dest "$scratch/$package" "$scratch/$name.llbc"
  for part in Types Funs; do
    cmp "$scratch/$package/$part.lean" "lean-hw/$package/$part.lean"
  done
  test "$(grep '^axiom ' "$scratch/$package/FunsExternal_Template.lean")" = \
    "axiom sha${bits}.soft.unroll.rk : Std.Usize → Result Std.U$word"
  (cd lean-hw && lake build "$package.Proof" &&
    lake env lean --stdin >"$scratch/$package.axioms" <<LEAN
import $package.Proof
#print axioms $theorem
LEAN
  )
  grep -Fx "'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/$package.axioms"
done
