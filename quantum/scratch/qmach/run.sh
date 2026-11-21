#!/bin/bash
cd /Users/danrobinson/Projects/formal-sig/quantum
export PATH=$HOME/.elan/bin:$PATH
SECLIB=../security/.lake/build/lib/lean; AENLIB=../.tools/aeneas/backends/lean/.lake/build/lib/lean; OUT=.lake/build/integration
LP="$(lake env printenv LEAN_PATH):$SECLIB:$AENLIB:$OUT"
if [ -n "$2" ]; then LEAN_PATH="$LP" timeout ${TO:-600} lean -o "$OUT/Integration/$2.olean" "$1"; else
LEAN_PATH="$LP" timeout ${TO:-300} lean "$1"; fi
