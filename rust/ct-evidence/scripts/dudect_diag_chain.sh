#!/bin/bash
# Follow-up diagnostics on the multi-block `chain_blocks` rows, four times the
# usual number of measurements, mainly with PSTATE.DIT = 1: is a flag in the
# fixed-vs-random design there a property of the data, of repeating it, or of
# how the harness prepares the two classes?
#
#   scripts/dudect_diag_chain.sh <default|hw-sha2>
#
#   RR       random vs random: a true null experiment
#   FF       two different fixed pseudo-random block contents
#   FR       fixed vs random, the dudect design: the fixed class's input is
#            copied from one buffer, the random class's is copied and then
#            partly overwritten with fresh bytes
#   FR/same  as FR, both classes prepared by the same code path (drawn like
#            the random class; the fixed class then overwritten with its
#            fixed bytes)
#   ZF       fixed all-zero vs a fixed pseudo-random value (both classes
#            prepared alike: is the all-zero value special?)
set -euo pipefail
cd "$(dirname "$0")/.."
v=${1:?variant: default or hw-sha2}
if [ "$v" = hw-sha2 ]; then D=./target-hw/release/dudect; else D=./target/release/dudect; fi
ROWS='chain_blocks/n=4|chain_blocks/n=35|chain_blocks/n=14|chain_blocks/n=128'
run() { # title, then dudect options
  local title=$1; shift
  echo "## $title"
  uptime
  $D components --filter "$ROWS" --scale 4 "$@" 2>/dev/null
  echo
}
for seed in 2001 2002; do
  run "RR/DIT: random vs random (null), DIT = 1, seed $seed" --classes random-random --dit --seed $seed
  run "FF/DIT: fixed A vs fixed B, DIT = 1, seed $seed" --classes fixed-fixed --dit --seed $seed
  run "FR/DIT: fixed (pseudo-random) vs random, DIT = 1, seed $seed" --dit --seed $seed
  run "FR/same/DIT: fixed (pseudo-random) vs random, same preparation path, DIT = 1, seed $seed" --same-prep --dit --seed $seed
done
run "RR: random vs random (null), seed 2001" --classes random-random --seed 2001
run "FF: fixed A vs fixed B, seed 2001" --classes fixed-fixed --seed 2001
run "FR: fixed (pseudo-random) vs random, seed 2001" --seed 2001
run "FR/same: fixed (pseudo-random) vs random, same preparation path, seed 2001" --same-prep --seed 2001
run "ZF: fixed all-zero vs fixed pseudo-random B, seed 2001" --classes fixed-fixed --fixed-zero --seed 2001
run "ZF/DIT: fixed all-zero vs fixed pseudo-random B, DIT = 1, seed 2001" --classes fixed-fixed --fixed-zero --dit --seed 2001
uptime
