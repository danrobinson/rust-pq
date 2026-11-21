#!/usr/bin/env bash
# usage: scratch/qfors/chk.sh FILE.lean [OUT.olean]
export PATH=$HOME/.elan/bin:$PATH
cd /Users/danrobinson/Projects/formal-sig/quantum
SECLIB=../security/.lake/build/lib/lean; AENLIB=../.tools/aeneas/backends/lean/.lake/build/lib/lean; OUT=.lake/build/integration
LP="$(lake env printenv LEAN_PATH):$SECLIB:$AENLIB:$OUT"
if [ -n "${2:-}" ]; then LEAN_PATH="$LP" lean -o "$2" "$1"; else LEAN_PATH="$LP" lean "$1"; fi
