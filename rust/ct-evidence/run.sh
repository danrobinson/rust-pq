#!/bin/bash
# Reruns the binary-level constant-time experiments for the slhdsa crate, for
# both builds of the crate: its default features, and `--features hw-sha2`.
#
#   ./run.sh <step> [default|hw-sha2|both]        (second argument: which build; default both)
#
#   setup        .venv + Unicorn wheel (needs network once), build both variants, record the
#                toolchain and the hashes of the crate's sources, check the emulator
#                against native output and count the SHA-256 instructions it executes
#   trace        component trace comparison under Unicorn
#   sign         whole-signature declassification-pinned trace comparison, 8 entry points
#   profile      whole-signature unconditioned profile
#   disasm       static disassembly facts + object-code comparison with the main crate's build
#   dudect-null  quick look at the timing noise floor: random-vs-random classes on every row,
#                and the two leaky controls
#   dudect       dudect timing tests, components: random-vs-random (null), fixed = pseudo-random,
#                fixed = zero, DIT = 1, random-vs-random again; then fixed-vs-random with both
#                classes prepared alike (DIT = 0 and 1) and all-zero vs another fixed secret
#                (the recorded runs used SCALE=0.5)
#   dudect-sign  dudect timing tests on whole signing
#   dudect-diag  class-design diagnostics on ten hash-level rows (scripts/dudect_diag.sh) and
#                on the multi-block chain_blocks rows (scripts/dudect_diag_chain.sh)
#   results      regenerate RESULTS.md from out/ and scripts/RESULTS.template.md
#   all          setup, trace, sign, profile, disasm, results (not the timing steps: run those
#                on an idle machine, and look at dudect-null first)
#
# Results are written to ./out/<variant>/. Nothing outside this directory is
# modified: the main crate is only read (its own-manifest build for `disasm`
# goes to a target directory inside this one).
set -euo pipefail
cd "$(dirname "$0")"
CARGO=${CARGO:-$HOME/.cargo/bin/cargo}
THREADS=${THREADS:-8}
SCALE=${SCALE:-1}
PY=.venv/bin/python

tdir() { if [ "$1" = hw-sha2 ]; then echo target-hw; else echo target; fi; }
feat() { if [ "$1" = hw-sha2 ]; then echo "--features hw-sha2"; fi; }
unicorn_dir() {
  $PY -I -c 'import unicorn, os; print(os.path.join(os.path.dirname(unicorn.__file__), "lib"))'
}
venv() {
  if [ ! -x $PY ]; then python3 -m venv .venv; fi
  $PY -I -c 'import unicorn' 2>/dev/null || .venv/bin/pip install -q 'unicorn==2.1.4'
}
build() { # variant
  # shellcheck disable=SC2046
  UNICORN_LIB_DIR="$(unicorn_dir)" "$CARGO" build --release --target-dir "$(tdir "$1")" $(feat "$1")
}
setup() { # variant
  local v=$1 t; t=$(tdir "$v"); mkdir -p "out/$v"
  venv
  build "$v"
  {
    echo "date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "variant: $v"
    echo "machine: $(sysctl -n machdep.cpu.brand_string), $(sysctl -n hw.perflevel0.physicalcpu)+$(sysctl -n hw.perflevel1.physicalcpu 2>/dev/null || echo 0) cores; $(sw_vers -productName) $(sw_vers -productVersion) ($(sw_vers -buildVersion)); $(uname -srm)"
    echo "rustc: $("$(dirname "$CARGO")/rustc" -Vv | tr '\n' ';')"
    echo "cargo: $("$CARGO" -V)"
    echo "unicorn: $($PY -I -c 'import unicorn; print(unicorn.__version__)')"
    echo "sha256 of the crate under test (..):"
    (cd .. && shasum -a 256 Cargo.toml src/*.rs)
    echo "sha256 of the harness binaries:"
    shasum -a 256 "$t/release/cttrace" "$t/release/dudect"
  } > "out/$v/build.txt"
  "./$t/release/cttrace" hwcheck | tee "out/$v/hwcheck.md"
}
need_build() { [ -x "$(tdir "$1")/release/cttrace" ] && [ -x "$(tdir "$1")/release/dudect" ] || setup "$1"; }

trace() {
  local v=$1; need_build "$v"
  "./$(tdir "$v")/release/cttrace" components --threads "$THREADS" | tee "out/$v/trace_components.md"
}
sign() {
  local v=$1 c; c="./$(tdir "$v")/release/cttrace"; need_build "$v"
  if [ "$v" = hw-sha2 ]; then
    # about 3e8 instructions per signature: everything with memory addresses
    $c sign --entry internal --pubs 16 --secrets 6 --threads "$THREADS" | tee "out/$v/trace_sign_internal.md"
    $c sign --entry internal-checked --pubs 16 --secrets 6 --threads "$THREADS" | tee "out/$v/trace_sign_internal-checked.md"
    for e in slh slh-checked api api-checked api-det api-det-checked; do
      $c sign --entry $e --pubs 4 --secrets 3 --threads "$THREADS" | tee "out/$v/trace_sign_$e.md"
    done
  else
    # about 6.5e9 (1.2e10 checked) instructions per signature
    $c sign --entry internal --pubs 8 --secrets 4 --threads "$THREADS" | tee "out/$v/trace_sign_internal.md"
    $c sign --entry internal-checked --pubs 8 --secrets 4 --threads "$THREADS" | tee "out/$v/trace_sign_internal-checked.md"
    # the wrappers around them, control flow only
    for e in slh slh-checked api api-checked api-det api-det-checked; do
      $c sign --entry $e --no-mem --pubs 4 --secrets 3 --threads "$THREADS" | tee "out/$v/trace_sign_$e.md"
    done
  fi
}
profile() {
  local v=$1 c; c="./$(tdir "$v")/release/cttrace"; need_build "$v"
  $c sign-profile --entry internal --pubs 24 --threads "$THREADS" | tee "out/$v/trace_sign_profile_internal.md"
  $c sign-profile --entry internal-checked --pubs 24 --threads "$THREADS" | tee "out/$v/trace_sign_profile_internal-checked.md"
}
disasm() {
  local v=$1 t ours theirs; t=$(tdir "$v"); need_build "$v"
  # the main crate built from its own manifest, into a directory of ours
  # shellcheck disable=SC2046
  "$CARGO" build --release --locked --offline --manifest-path ../Cargo.toml --target-dir "$t/parent" $(feat "$v")
  ours=$(find "$t/release" -name 'libslhdsa-*.rlib' | head -1)
  theirs=$(find "$t/parent/release" -name 'libslhdsa-*.rlib' | head -1)
  python3 -I scripts/disasm_check.py "$t/release/cttrace" "$ours" "$theirs" | tee "out/$v/disasm.md"
}
dudect_null() {
  local v=$1 d; d="./$(tdir "$v")/release/dudect"; need_build "$v"
  { uptime; $d components --classes random-random --scale "$SCALE"; $d components --filter CONTROL --scale "$SCALE"; uptime; } | tee "out/$v/dudect_null_random_random.md"
}
dudect() {
  local v=$1 d; d="./$(tdir "$v")/release/dudect"; need_build "$v"
  # the null experiment brackets the others: the noise floor before and after
  { uptime; $d components --classes random-random --scale "$SCALE"; uptime; } | tee "out/$v/dudect_null_before.md"
  { uptime; $d components --scale "$SCALE"; uptime; } | tee "out/$v/dudect_components_fixed_random.md"
  { uptime; $d components --fixed-zero --scale "$SCALE"; uptime; } | tee "out/$v/dudect_components_fixed_zero.md"
  { uptime; $d components --dit --scale "$SCALE"; uptime; } | tee "out/$v/dudect_components_fixed_random_DIT.md"
  { uptime; $d components --classes random-random --scale "$SCALE"; uptime; } | tee "out/$v/dudect_null_after.md"
  # fixed vs random again with both classes prepared by one code path (the
  # standard preparation is itself visible on the rows with kilobytes of
  # varied bytes), and the all-zero secret against another fixed one
  { uptime; $d components --same-prep --scale "$SCALE"; uptime; } | tee "out/$v/dudect_components_sameprep.md"
  { uptime; $d components --same-prep --dit --scale "$SCALE"; uptime; } | tee "out/$v/dudect_components_sameprep_DIT.md"
  { uptime; $d components --classes fixed-fixed --fixed-zero --scale "$SCALE"; uptime; } | tee "out/$v/dudect_components_zero_vs_fixed.md"
}
dudect_diag() {
  local v=$1; need_build "$v"
  ./scripts/dudect_diag.sh "$v" | tee "out/$v/dudect_diag.md"
  ./scripts/dudect_diag_chain.sh "$v" | tee "out/$v/dudect_diag_chain.md"
}
dudect_sign() {
  local v=$1 d; d="./$(tdir "$v")/release/dudect"; need_build "$v"
  for e in internal internal-checked; do
    { uptime; $d sign-key --entry $e --n 300; uptime; } | tee "out/$v/dudect_sign_key_$e.md"
    { uptime; $d sign-addrnd --entry $e --n 300; uptime; } | tee "out/$v/dudect_sign_addrnd_$e.md"
  done
}

case "${2:-both}" in
  both) VARIANTS="default hw-sha2" ;;
  default|hw-sha2) VARIANTS=$2 ;;
  *) echo "variant must be default, hw-sha2 or both"; exit 2 ;;
esac
step=${1:-all}
case "$step" in
  results) python3 -I scripts/make_results.py; exit ;;
  setup|trace|sign|profile|disasm|dudect|all) ;;
  dudect-null) step=dudect_null ;;
  dudect-sign) step=dudect_sign ;;
  dudect-diag) step=dudect_diag ;;
  *) echo "usage: $0 {setup|trace|sign|profile|disasm|dudect-null|dudect|dudect-sign|dudect-diag|results|all} [default|hw-sha2|both]"; exit 2 ;;
esac
for v in $VARIANTS; do
  mkdir -p "out/$v"
  if [ "$step" = all ]; then
    setup "$v"; trace "$v"; sign "$v"; profile "$v"; disasm "$v"
  else
    "$step" "$v"
  fi
done
if [ "$step" = all ]; then python3 -I scripts/make_results.py; fi
