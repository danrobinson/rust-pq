#!/bin/sh
# Regenerate the Lean translation of the crate as built with the `hw-sha2`
# feature (lean-hw/Slhdsa/{Types,Funs}.lean).
#
# Everything is translated except `sha256::hw::arm`, the module of one-line
# wrappers around the NEON and SHA-256 intrinsics. Aeneas lists what it left
# out in two template files; their hand-written counterparts are
# lean-hw/Slhdsa/TypesExternal.lean and FunsExternal.lean, which give each
# wrapper its meaning (lean-hw/Arm.lean). This script fails if a wrapper has no
# definition there.
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$PATH"
# Aeneas names the Lean modules after the .llbc file, so it is `slhdsa.llbc`
# here too, in its own directory.
(cd rust && ../.tools/aeneas/charon/bin/charon cargo --preset=aeneas \
   --opaque 'slhdsa::sha256::hw::arm' --dest hw-sha2 -- --features hw-sha2)
./.tools/aeneas/bin/aeneas -backend lean -dest lean-hw/Slhdsa -split-files rust/hw-sha2/slhdsa.llbc
cd lean-hw/Slhdsa
missing=0
for name in $(grep -h '^axiom ' TypesExternal_Template.lean FunsExternal_Template.lean | awk '{print $2}'); do
  if ! grep -q "^def $name\b" TypesExternal.lean FunsExternal.lean; then
    echo "no definition for $name in lean-hw/Slhdsa/{Types,Funs}External.lean"; missing=1
  fi
done
rm -f TypesExternal_Template.lean FunsExternal_Template.lean
[ "$missing" = 0 ]
