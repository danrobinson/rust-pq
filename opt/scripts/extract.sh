#!/bin/sh
# Regenerate the Lean translation of the optimised crate (opt/lean/Slhdsa/{Types,Funs}.lean).
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$PATH"
(cd rust && ../../.tools/aeneas/charon/bin/charon cargo --preset=aeneas)
../.tools/aeneas/bin/aeneas -backend lean -dest lean/Slhdsa -split-files rust/slhdsa.llbc
