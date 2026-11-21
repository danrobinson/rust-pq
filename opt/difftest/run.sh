#!/bin/sh
# Differential check: original crate (rust/) vs optimised crate (opt/rust/).
# Usage: opt/difftest/run.sh [random cases, default 40]
set -e
cd "$(dirname "$0")"
export PATH="$HOME/.cargo/bin:$PATH"
N=${1:-40}
V=../../vectors/slh-dsa-sha2-128s.json
OUT=${TMPDIR:-/tmp}/slhdsa-difftest.$$
mkdir -p "$OUT"
(cd orig && cargo build --release --offline -q)
(cd new && cargo build --release --offline -q)
orig/target/release/dump "$V" "$N" > "$OUT/orig.txt" &
new/target/release/dump "$V" "$N" > "$OUT/new.txt" &
wait
wc -l "$OUT/orig.txt" "$OUT/new.txt"
grep -c '^kat-' "$OUT/new.txt" | sed 's/^/vector lines: /'
grep -c '^rnd-' "$OUT/new.txt" | sed 's/^/random lines: /'
if cmp "$OUT/orig.txt" "$OUT/new.txt"; then
  echo "IDENTICAL ($(shasum -a 256 "$OUT/new.txt" | cut -c1-16))"
else
  diff "$OUT/orig.txt" "$OUT/new.txt" | head
  echo "DIFFERENT"; exit 1
fi
