#!/bin/sh
# Regenerate the Lean translation of the Rust crate (lean/Slhdsa/{Types,Funs}.lean).
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$PATH"
case "${1:-}" in
  --check)
    [ "$#" -eq 1 ] || exit 2
    out=$(mktemp -d)
    trap 'rm -rf "$out"' EXIT
    (cd rust && ../.tools/aeneas/charon/bin/charon cargo --preset=aeneas --dest-file "$out/slhdsa.llbc")
    .tools/aeneas/bin/aeneas -backend lean -dest "$out/Slhdsa" -split-files "$out/slhdsa.llbc"
    cmp "$out/Slhdsa/Funs.lean" lean/Slhdsa/Funs.lean
    cmp "$out/Slhdsa/Types.lean" lean/Slhdsa/Types.lean
    echo "Extracted Rust functions and types match the proof inputs."
    exit 0
    ;;
  "") ;;
  *) echo "Usage: $0 [--check]" >&2; exit 2 ;;
esac
(cd rust && ../.tools/aeneas/charon/bin/charon cargo --preset=aeneas)
.tools/aeneas/bin/aeneas -backend lean -dest lean/Slhdsa -split-files rust/slhdsa.llbc
