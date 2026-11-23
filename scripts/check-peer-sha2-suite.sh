#!/usr/bin/env bash
# Recreate the peer's byte encodings from verified Cargo archives and check Lean.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
python3 scripts/extract-peer-sha2-suite.py "$scratch/Suite.lean" "$scratch/Initial.lean"
cmp "$scratch/Suite.lean" lean-hw/RcSlhSha2/Suite.lean
cmp "$scratch/Initial.lean" lean-hw/RcSlhSha2/Initial.lean
cd lean-hw
lake build RcSlhSha2.Peer
lake env lean --stdin >"$scratch/axioms" <<'LEAN'
import RcSlhSha2.Peer
#print axioms slhdsa.RcSlhSha2.suite_on_platform
#print axioms slhdsa.RcSlhSha2.suite_is_fips
#print axioms slhdsa.RcSlhSha2.absorb_buffer
#print axioms slhdsa.RcSlhSha2.feed_complete
LEAN
for theorem in suite_on_platform suite_is_fips absorb_buffer feed_complete; do
  line=$(grep -F "'slhdsa.RcSlhSha2.$theorem'" "$scratch/axioms")
  printf '%s\n' "$line"
  case "$line" in
    *"depends on axioms: [propext, Classical.choice, Quot.sound]"|*"depends on axioms: [propext, Quot.sound]"|*"does not depend on any axioms") ;;
    *) exit 1 ;;
  esac
done
cd ..
python3 scripts/test-peer-sha2-order.py
