#!/bin/sh
# Re-extract the production adapter code and check its proof against that extraction.
set -eu
cd "$(dirname "$0")/.."
root=$PWD
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
(cd compat && "$root/.tools/aeneas/charon/bin/charon" cargo --preset=aeneas \
  --start-from crate::multipart::join --dest-file "$scratch/slh_dsa.llbc" -- --locked)
"$root/.tools/aeneas/bin/aeneas" -backend lean -dest "$scratch" "$scratch/slh_dsa.llbc"
cmp "$scratch/SlhDsa.lean" lean/Slhdsa/Compat/SlhDsa.lean
(cd lean && lake build Slhdsa.Compat.Multipart)
