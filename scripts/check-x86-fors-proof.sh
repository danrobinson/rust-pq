#!/bin/sh
# Re-extract the AVX-512 FORS subtree and kernel-check its FIPS Algorithm 15 refinement.
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
(cd rust && "$root/.tools/aeneas/charon/bin/charon" cargo --preset=aeneas --start-from 'crate::fors::wide::subtree' \
  --opaque 'crate::sha256::x86::fors_leaves' --opaque 'crate::sha256::x86::fors_parents' \
  --opaque 'crate::sha512::parents::parents' --opaque 'crate::hash::thash_pair' \
  --dest-file "$scratch/xfors.llbc" -- --locked --features platform-sha2 --target x86_64-unknown-linux-gnu)
"$root/.tools/aeneas/bin/aeneas" -backend lean -abort-on-error -no-progress-bar -namespace XForsRust \
  -split-files -dest "$scratch/Xfors" "$scratch/xfors.llbc"
# Qualify the namespace where Aeneas also named a Rust local "address".
sed 's/let a3 ← address.Adrs.with_word3 address i1/let a3 ← XForsRust.address.Adrs.with_word3 address i1/' "$scratch/Xfors/Funs.lean" > "$scratch/qualified.lean"
cmp "$scratch/qualified.lean" lean-hw/Xfors/Funs.lean
cmp "$scratch/Xfors/Types.lean" lean-hw/Xfors/Types.lean
sed -n 's/^axiom \([^ :]*\).*/\1/p' "$scratch"/Xfors/*External_Template.lean | LC_ALL=C sort > "$scratch/actual"
cat > "$scratch/expected" <<'NAMES'
hash.thash_pair
sha256.x86.fors_leaves
sha256.x86.fors_parents
sha512.parents.parents
NAMES
cmp "$scratch/expected" "$scratch/actual"
(cd lean-hw && lake build Xfors.Top && lake env lean --stdin > "$scratch/axioms" <<'LEAN'
import Xfors.Top
#print axioms slhdsa.X86.Fors.subtree_fips
LEAN
)
grep -Fx "'slhdsa.X86.Fors.subtree_fips' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/axioms"
