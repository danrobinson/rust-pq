#!/bin/bash
# Diagnostics for dudect flags on the hash-level rows: is a fixed-vs-random
# difference a property of the VALUE that is processed, of REPEATING one
# value, or of the harness?
#
#   scripts/dudect_diag.sh <default|hw-sha2>
#
# On ten rows (compress, sha256 at four lengths, thash_short at both lengths,
# one 15-step chain, fors_sk_gen, fors_node at z = 0), the class designs
#
#   RR      random vs random: a true null experiment
#   FF      two different fixed pseudo-random secrets (two pairs: seeds 1001, 1002)
#   FR      fixed pseudo-random vs random: the dudect design
#   FR/same as FR, both classes prepared by the same code path
#   FR/x8   as FR, eight times as many calls per measurement (a quarter of the
#           measurements): a cost paid once per measurement shrinks eightfold
#           per call, a cost paid on every call does not
#   FZ      fixed all-zero vs random
#   FR/DIT, FZ/DIT, FF/DIT   the same with PSTATE.DIT = 1 on the measuring thread
#   ZF      fixed all-zero vs a fixed pseudo-random secret (both repeated: is
#           the all-zero value special?), and ZF/DIT
set -euo pipefail
cd "$(dirname "$0")/.."
v=${1:?variant: default or hw-sha2}
if [ "$v" = hw-sha2 ]; then D=./target-hw/release/dudect; else D=./target/release/dudect; fi
ROWS='compress|sha256/len=1|thash_short|chain_blocks/n=1,steps=0..15|fors_sk_gen|fors_node/z=0'
run() { # title, then dudect options
  local title=$1; shift
  echo "## $title"
  uptime
  $D components --filter "$ROWS" "$@" 2>/dev/null
  echo
}
run "RR: random vs random (null), seed 1001" --classes random-random --seed 1001
run "FF: fixed A vs fixed B, seed 1001" --classes fixed-fixed --seed 1001
run "FF: fixed A vs fixed B, seed 1002" --classes fixed-fixed --seed 1002
run "FR: fixed (pseudo-random) vs random, seed 1001" --seed 1001
run "FR/same: fixed (pseudo-random) vs random, same preparation path, seed 1001" --same-prep --seed 1001
run "FR/x8: fixed (pseudo-random) vs random, 8 x calls per measurement, seed 1001" --reps-mul 8 --scale 0.25 --seed 1001
run "FZ: fixed (all-zero) vs random, seed 1001" --fixed-zero --seed 1001
run "FR/DIT: fixed (pseudo-random) vs random, DIT = 1, seed 1001" --dit --seed 1001
run "FZ/DIT: fixed (all-zero) vs random, DIT = 1, seed 1001" --fixed-zero --dit --seed 1001
run "FF/DIT: fixed A vs fixed B, DIT = 1, seed 1001" --classes fixed-fixed --dit --seed 1001
run "RR: random vs random (null), seed 1002" --classes random-random --seed 1002
run "ZF: fixed all-zero vs fixed pseudo-random B, seed 1001" --classes fixed-fixed --fixed-zero --seed 1001
run "ZF/DIT: fixed all-zero vs fixed pseudo-random B, DIT = 1, seed 1001" --classes fixed-fixed --fixed-zero --dit --seed 1001
uptime
