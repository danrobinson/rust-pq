#!/bin/sh
# Time keygen / sign / verify for the original (rust/) and optimised (opt/rust/)
# crates with the same harness, alternating the two. Usage: bench.sh [rounds] [runs per round]
set -e
cd "$(dirname "$0")"
export PATH="$HOME/.cargo/bin:$PATH"
R=${1:-3}; N=${2:-5}
(cd orig && cargo build --release --offline -q)
(cd new && cargo build --release --offline -q)
i=0
while [ $i -lt "$R" ]; do
  orig/target/release/bench "$N" | sed 's/^/orig /'
  new/target/release/bench "$N" | sed 's/^/new /'
  i=$((i + 1))
done
