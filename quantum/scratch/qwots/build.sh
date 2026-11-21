#!/bin/bash
# usage: build.sh NAME   (compiles quantum/Integration/NAME.lean)
cd /Users/danrobinson/Projects/formal-sig/quantum
export PATH=$HOME/.elan/bin:$PATH
SECLIB=../security/.lake/build/lib/lean; AENLIB=../.tools/aeneas/backends/lean/.lake/build/lib/lean; OUT=.lake/build/integration
LP="$(lake env printenv LEAN_PATH):$SECLIB:$AENLIB:$OUT"
LEAN_PATH="$LP" lean -o "$OUT/Integration/$1.olean" Integration/$1.lean
