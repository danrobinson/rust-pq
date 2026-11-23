#!/bin/sh
# Re-extract the production x86 functions and kernel-check their lane specifications.
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
mkdir "$scratch/Platform"
(cd rust && "$root/.tools/aeneas/charon/bin/charon" cargo --preset=aeneas \
  --start-from 'crate::sha256::x86::avx512::round' --opaque 'core::core_arch' \
  --dest-file "$scratch/platform.llbc" -- --locked --features platform-sha2 --target x86_64-unknown-linux-gnu)
.tools/aeneas/bin/aeneas -backend lean -abort-on-error -no-progress-bar -split-files \
  -dest "$scratch/Platform" "$scratch/platform.llbc"
for name in Types Funs; do
  cmp "$scratch/Platform/$name.lean" "lean/Platform/$name.lean"
done
# New intrinsic calls require an explicit semantic model.
sed -n 's/^axiom \([^ :]*\).*/\1/p' "$scratch"/Platform/*External_Template.lean | sort > "$scratch/actual"
cat > "$scratch/expected" <<'NAMES'
core.core_arch.x86.__m512i
core.core_arch.x86.avx512f._mm512_add_epi32
core.core_arch.x86.avx512f._mm512_ror_epi32
core.core_arch.x86.avx512f._mm512_set1_epi32
core.core_arch.x86.avx512f._mm512_ternarylogic_epi32
NAMES
cmp "$scratch/actual" "$scratch/expected"
(cd lean && lake build Platform && lake env lean Platform/Rounds.lean > "$scratch/axioms")
grep -Fx "'slhdsa.X86.round_spec' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/axioms"
