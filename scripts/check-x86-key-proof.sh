#!/bin/sh
# Check the complete, fixed-size SHA-2 key-generation entries compiled for x86.
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
for size in 128s 128f 192s 192f 256s 256f; do
  set -- "$@" --start-from "crate::sets::sha2_$size::keygen" --start-from "crate::sets::sha2_$size::public_key"
done
(cd rust && "$root/.tools/aeneas/charon/bin/charon" cargo --preset=aeneas "$@" \
  --opaque 'crate::sha256::compress' --opaque 'crate::sha512::compress' \
  --opaque 'crate::sha256::x86::chain_blocks' --opaque 'crate::sha256::x86::avx512_available' \
  --opaque 'crate::xmss::wide::batch_root' --opaque 'crate::xmss::hash2' --opaque 'crate::hash::thash_values' \
  --dest-file "$scratch/x86key.llbc" -- --locked --features platform-sha2 --target x86_64-unknown-linux-gnu)
"$root/.tools/aeneas/bin/aeneas" -backend lean -abort-on-error -no-progress-bar -namespace X86KeyRust \
  -split-files -dest "$scratch/X86key" "$scratch/x86key.llbc"
for file in Types Funs; do cmp "$scratch/X86key/$file.lean" "lean-hw/X86key/$file.lean"; done
sed -n 's/^axiom \([^ :]*\).*/\1/p' "$scratch"/X86key/*External_Template.lean | LC_ALL=C sort > "$scratch/actual"
cat > "$scratch/expected" <<'NAMES'
core.ops.range.RangeInclusive.contains
hash.thash_values
sha256.compress
sha256.x86.avx512_available
sha256.x86.chain_blocks
sha512.compress
xmss.hash2
xmss.wide.batch_root
NAMES
cmp "$scratch/expected" "$scratch/actual"
echo 'import X86key.Sets' > "$scratch/check.lean"
for size in 128s 128f 192s 192f 256s 256f; do
  for fn in keygen_fips public_key_fips; do
    echo "#print axioms slhdsa.X86.Key.sha2_$size.$fn" >> "$scratch/check.lean"
  done
done
(cd lean-hw && lake build X86key.Sets && lake env lean --stdin < "$scratch/check.lean") > "$scratch/axioms"
for size in 128s 128f 192s 192f 256s 256f; do
  for fn in keygen_fips public_key_fips; do
    grep -Fx "'slhdsa.X86.Key.sha2_$size.$fn' depends on axioms: [propext, Classical.choice, Quot.sound]" "$scratch/axioms"
  done
done
