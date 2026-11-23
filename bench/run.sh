#!/usr/bin/env bash
# Reproduces everything in RESULTS.md:  ./run.sh            (ROUNDS=2 by default)
#
#   1. checks that the frozen copies variants/base (= `verified-before`) and variants/current
#      still equal opt/original/rust/src and rust/src of the single-set tree they were taken
#      from (git commit 26aa3d8, read with `git show`), then ACVP tests of all copies under
#      variants/. `verified` and `verified-api` are the current six-set crate's 128s functions
#      (../rust, ../compat).
#   2. interoperability check (src/bin/interop.rs)
#   3. SHA-256 compression counts (count/)
#   4. ROUNDS rounds; each round runs three build configurations back to back,
#      odd rounds in forward library order, even rounds reversed:
#        default : cargo bench as shipped (release profile: opt-level 3, lto off, 16 CGUs)
#        soft    : sha2 forced to its portable backend (affects rustcrypto-slh-dsa, fips205)
#        tuned   : lto=fat, codegen-units=1, -C target-cpu=native (Rust implementations)
#        asm     : default profile, sha2 0.10 with its `asm` feature (ARMv8 SHA-2), for fips205
#        hw      : default profile, the verified crate with its opt-in `hw-sha2` feature
#                  (entry `verified+hw-sha2`), next to the hardware-SHA-2 libraries
#      plus the SHA-256 micro-benchmark in default and soft builds.
#   5. results/<stamp>/summary.md (scripts: summarize.py)
#
# Needs: rustup toolchain (cargo on PATH or in ~/.cargo/bin), Homebrew OpenSSL >= 3.5
# at /opt/homebrew/opt/openssl@4 (override with OPENSSL_DIR), network access on the
# first build (crates.io). Nothing outside this directory is written.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.cargo/bin:$PATH"
ROUNDS="${ROUNDS:-2}"
ROUND_START="${ROUND_START:-1}"   # to add rounds to an existing results dir: STAMP=<dir> ROUND_START=3 ./run.sh
CONFIGS="${CONFIGS:-default soft tuned asm hw}"     # subset of: default soft tuned asm hw
STAMP="${STAMP:-$(date +%Y%m%d-%H%M%S)}"
OUT="results/$STAMP"
mkdir -p "$OUT"

{
  echo "date: $(date)"
  echo "host: $(sysctl -n machdep.cpu.brand_string), $(sysctl -n hw.ncpu) cores, $(( $(sysctl -n hw.memsize) / 1073741824 )) GiB"
  echo "os: $(sw_vers -productName) $(sw_vers -productVersion) ($(sw_vers -buildVersion)), $(uname -m)"
  echo "rustc: $(rustc --version)"
  echo "cc: $(cc --version | head -1)"
  echo "openssl: $("${OPENSSL_DIR:-/opt/homebrew/opt/openssl@4}/bin/openssl" version)"
  echo "load at start: $(uptime)"
} | tee -a "$OUT/env.txt"

echo "== frozen copies under variants/ still match the single-set tree (git 26aa3d8; modulo the cfg(feature = \"count\") counter)"
strip_counter() { grep -v -e 'feature = "count"' -e 'COMPRESSIONS' -e 'Benchmark-only: number of compression'; }
OLD=26aa3d8
# variants/current is the single-set crate minus the functions removed from this repository on
# 2026-11-22 (HANDOFF.md): there the copy may differ from the original only by deleted lines,
# doc-comment lines, and `use` lists that lost names.
only_removals() { python3 -I -c '
import sys, re, difflib
a = open(sys.argv[1]).read().split("\n"); b = open(sys.argv[2]).read().split("\n")
pieces = lambda s: [p.strip() for p in re.split("[,{]", s)]
def sub(l, x):
    it = iter(pieces(x))
    return all(any(p == q for q in it) for p in pieces(l))
ok = True
for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
    if op in ("equal", "delete"): continue
    for l in b[j1:j2]:
        if l.strip() == "" or l.lstrip().startswith("//"): continue
        if "," in l and any(sub(l, x) for x in a[i1:i2]): continue
        print("added:", l); ok = False
sys.exit(0 if ok else 1)' "$1" "$2"; }
for pair in "variants/base/src:opt/original/rust/src" "variants/current/src:rust/src"; do
  copy=${pair%%:*}; orig=${pair##*:}
  files=$(git -C .. ls-tree --name-only "$OLD" "$orig/" | grep '\.rs$') || { echo "cannot read $OLD:$orig (needs the git history)"; exit 1; }
  for f in $files; do
    if [ "$copy" = variants/current/src ]; then
      only_removals <(git -C .. show "$OLD:$f" | strip_counter) <(strip_counter < "$copy/$(basename "$f")") > /dev/null \
        || { echo "STALE COPY: $copy/$(basename "$f") is not $OLD:$f with lines removed"; exit 1; }
    elif ! diff -qB <(git -C .. show "$OLD:$f" | strip_counter) <(strip_counter < "$copy/$(basename "$f")") >/dev/null; then
      echo "STALE COPY: $copy/$(basename "$f") differs from $OLD:$f"; exit 1
    fi
  done
  echo "$copy == $OLD:$orig$([ "$copy" = variants/current/src ] && echo ' (with the removed functions taken out)')"
done | tee "$OUT/copies.txt"

echo "== ACVP tests of the variant copies"
cargo test --release -q -p slhdsa_base -p slhdsa_current -p slhdsa_a -p slhdsa_b -p slhdsa_c -p slhdsa_d 2>&1 | grep -E "^test result|FAILED|panicked" | tee "$OUT/variants-acvp.txt"

echo "== interoperability"
cargo run --release -q --bin interop 2>/dev/null | tee "$OUT/interop.md"
echo "== interoperability, verified crate built with hw-sha2"
CARGO_TARGET_DIR=target/hw cargo run --release -q --features hw --bin interop 2>/dev/null | tee "$OUT/interop-hw.md"

echo "== compression counts"
cargo run --release -q -p count 2>/dev/null | tee "$OUT/compressions.md"

run_sig() { # config round
  local cfg=$1 r=$2 rev=0
  [ $((r % 2)) -eq 0 ] && rev=1
  local home="$OUT/$cfg-r$r"
  echo "== round $r, config $cfg, reverse=$rev ($(uptime | sed 's/.*load/load/'))" | tee -a "$OUT/load.txt"
  case $cfg in
    default) CRITERION_HOME="$home" BENCH_REVERSE=$rev cargo bench -q --bench sig ;;
    soft) CARGO_TARGET_DIR=target/soft RUSTFLAGS='--cfg sha2_backend="soft"' CRITERION_HOME="$home" \
            BENCH_REVERSE=$rev BENCH_ONLY=rustcrypto-slh-dsa,fips205 cargo bench -q --features soft --bench sig ;;
    tuned) CARGO_TARGET_DIR=target/tuned RUSTFLAGS='-C target-cpu=native' CARGO_PROFILE_BENCH_LTO=fat \
            CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 CRITERION_HOME="$home" BENCH_REVERSE=$rev \
            BENCH_ONLY=rustcrypto-slh-dsa,fips205,variant-A,variant-B,variant-C,variant-D cargo bench -q --bench sig ;;
    asm) CARGO_TARGET_DIR=target/asm CRITERION_HOME="$home" BENCH_REVERSE=$rev BENCH_ONLY=fips205 \
            cargo bench -q --features asm010 --bench sig ;;
    hw) CARGO_TARGET_DIR=target/hw CRITERION_HOME="$home" BENCH_REVERSE=$rev \
            BENCH_ONLY=verified+hw-sha2,verified-api+hw-sha2,rustcrypto-slh-dsa,openssl,slhdsa-c cargo bench -q --features hw --bench sig ;;
  esac > "$home.log" 2>&1
}
run_sha() { # config round
  local cfg=$1 r=$2 home="$OUT/sha-$1-r$2"
  case $cfg in
    default) CRITERION_HOME="$home" cargo bench -q --bench sha ;;
    soft) CARGO_TARGET_DIR=target/soft RUSTFLAGS='--cfg sha2_backend="soft"' CRITERION_HOME="$home" \
            cargo bench -q --features soft --bench sha ;;
    asm) CARGO_TARGET_DIR=target/asm CRITERION_HOME="$home" cargo bench -q --features asm010 --bench sha ;;
  esac > "$home.log" 2>&1
}

echo "== building all configurations"
cargo bench -q --no-run 2>/dev/null
CARGO_TARGET_DIR=target/soft RUSTFLAGS='--cfg sha2_backend="soft"' cargo bench -q --features soft --no-run 2>/dev/null
CARGO_TARGET_DIR=target/tuned RUSTFLAGS='-C target-cpu=native' CARGO_PROFILE_BENCH_LTO=fat CARGO_PROFILE_BENCH_CODEGEN_UNITS=1 \
  cargo bench -q --no-run 2>/dev/null
CARGO_TARGET_DIR=target/asm cargo bench -q --features asm010 --no-run 2>/dev/null
CARGO_TARGET_DIR=target/hw cargo bench -q --features hw --no-run 2>/dev/null

for r in $(seq "$ROUND_START" $((ROUND_START + ROUNDS - 1))); do
  cfgs="$CONFIGS"
  if [ $((r % 2)) -eq 0 ]; then cfgs=$(echo $CONFIGS | tr ' ' '\n' | tail -r | tr '\n' ' '); fi
  for cfg in $cfgs; do run_sig "$cfg" "$r"; done
  for cfg in $CONFIGS; do [ "$cfg" = tuned ] || [ "$cfg" = hw ] || run_sha "$cfg" "$r"; done
done
echo "load at end: $(uptime)" >> "$OUT/env.txt"

python3 -I summarize.py "$OUT" | tee "$OUT/summary.md"
