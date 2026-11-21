#!/bin/bash
# Diagnostics for the dudect flags on bare SHA-256 / HMAC / thash:
# is the effect a property of the VALUE hashed, or of repeating one value?
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p out
D=./target/release/dudect
if [ "${1:-}" = "dit" ]; then
  # Same fixed-vs-random experiments with PSTATE.DIT = 1 on the measuring thread.
  for seed in 1001 1002; do
    echo "## sha256, DIT=1: fixed-random, fixed = pseudo-random, seed $seed"; $D components --filter sha256 --dit --seed $seed 2>/dev/null
    echo "## sha256, DIT=1: fixed-random, fixed = all-zero, seed $seed"; $D components --filter sha256 --dit --fixed-zero --seed $seed 2>/dev/null
  done
  exit 0
fi
for f in sha256 thash; do
  for seed in 1001 1002; do
    echo "## $f: random-random (true null), seed $seed";  $D components --filter $f --classes random-random --seed $seed 2>/dev/null
    echo "## $f: fixed-fixed (two different fixed pseudo-random secrets), seed $seed"; $D components --filter $f --classes fixed-fixed --seed $seed 2>/dev/null
    echo "## $f: fixed-random, fixed = pseudo-random, seed $seed"; $D components --filter $f --seed $seed 2>/dev/null
    echo "## $f: fixed-random, fixed = all-zero, seed $seed"; $D components --filter $f --fixed-zero --seed $seed 2>/dev/null
  done
done
