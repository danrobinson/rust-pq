#!/bin/bash
# Reruns the binary-level constant-time experiments for the slhdsa crate.
#
#   ./run.sh setup      create .venv, pip-install the Unicorn wheel (libunicorn), build   (~1 min, needs network once)
#   ./run.sh trace      component trace comparison under Unicorn                          (~6 min on 12 cores)
#   ./run.sh sign       whole-signature declassification-pinned trace comparison          (~40 min on 12 cores)
#   ./run.sh profile    whole-signature unconditioned profile                             (~2 min)
#   ./run.sh disasm     static disassembly facts + rlib comparison                        (seconds)
#   ./run.sh dudect     dudect timing tests, components (fixed=random value, fixed=zero, and DIT=1)  (~35 min, run on an idle machine)
#   ./run.sh dudect-diag  class-design diagnostics for bare SHA-256/HMAC/thash, without and with DIT (~25 min)
#   ./run.sh dudect-sign  dudect timing tests on whole signing                            (~20 min)
#   ./run.sh results    regenerate RESULTS.md from out/ and scripts/RESULTS.template.md   (instant)
#   ./run.sh all        everything above in that order (~2.5 h)
#
# Results are written to ./out/*.md|txt. Nothing outside this directory is
# modified, except that `disasm` runs `cargo build --release` in the parent
# crate if its release rlib does not exist yet (writes only ../target).
set -euo pipefail
cd "$(dirname "$0")"
CARGO=${CARGO:-$HOME/.cargo/bin/cargo}
THREADS=${THREADS:-$(sysctl -n hw.perflevel0.physicalcpu 2>/dev/null || echo 4)}
mkdir -p out

unicorn_dir() {
  .venv/bin/python -c 'import unicorn, os; print(os.path.join(os.path.dirname(unicorn.__file__), "lib"))'
}
setup() {
  if [ ! -x .venv/bin/python ]; then python3 -m venv .venv; fi
  .venv/bin/python -c 'import unicorn' 2>/dev/null || .venv/bin/pip install -q 'unicorn==2.1.4'
  UNICORN_LIB_DIR="$(unicorn_dir)" "$CARGO" build --release
}
need_build() { [ -x target/release/cttrace ] && [ -x target/release/dudect ] || setup; }

trace() {
  need_build
  ./target/release/cttrace components --threads "$THREADS" | tee out/trace_components.md
}
sign() {
  need_build
  # control flow + memory addresses: 8 public configurations x 4 fresh secret sets
  ./target/release/cttrace sign --pubs 8 --secrets 4 --threads "$THREADS" | tee out/trace_sign.md
  # slh_sign (context wrapper), control flow only: 4 x 3
  ./target/release/cttrace sign-ctx --no-mem --pubs 4 --secrets 3 --threads "$THREADS" | tee out/trace_sign_ctx.md
}
profile() {
  need_build
  ./target/release/cttrace sign-profile --pubs 24 --threads "$THREADS" | tee out/trace_sign_profile.md
}
disasm() {
  need_build
  ours=$(find target/release -name 'libslhdsa-*.rlib' | head -1)
  theirs=$(find ../target/release -name 'libslhdsa-*.rlib' 2>/dev/null | head -1 || true)
  if [ -z "$theirs" ]; then (cd .. && "$CARGO" build --release); theirs=$(find ../target/release -name 'libslhdsa-*.rlib' | head -1); fi
  python3 scripts/disasm_check.py target/release/cttrace "$ours" "$theirs" | tee out/disasm.md
}
dudect() {
  need_build
  ./target/release/dudect components | tee out/dudect_components_fixed_random.md
  ./target/release/dudect components --fixed-zero | tee out/dudect_components_fixed_zero.md
  ./target/release/dudect components --dit | tee out/dudect_components_fixed_random_DIT.md
}
dudect_diag() {
  need_build
  ./scripts/dudect_diag.sh | tee out/dudect_diag.md
  ./scripts/dudect_diag.sh dit | tee out/dudect_diag_dit.md
}
dudect_sign() {
  need_build
  ./target/release/dudect sign-key --n 300 | tee out/dudect_sign_key.md
  ./target/release/dudect sign-addrnd --n 300 | tee out/dudect_sign_addrnd.md
}

case "${1:-all}" in
  setup) setup ;;
  trace) trace ;;
  sign) sign ;;
  profile) profile ;;
  disasm) disasm ;;
  dudect) dudect ;;
  dudect-sign) dudect_sign ;;
  dudect-diag) dudect_diag ;;
  results) python3 scripts/make_results.py ;;
  all) setup; trace; sign; profile; disasm; dudect; dudect_diag; dudect_sign; python3 scripts/make_results.py ;;
  *) echo "usage: $0 {setup|trace|sign|profile|disasm|dudect|dudect-diag|dudect-sign|results|all}"; exit 2 ;;
esac
