export PATH=$HOME/.elan/bin:$PATH
cd /Users/danrobinson/Projects/formal-sig/quantum
SECLIB=../security/.lake/build/lib/lean; AENLIB=../.tools/aeneas/backends/lean/.lake/build/lib/lean; OUT=.lake/build/integration
LP="$(lake env printenv LEAN_PATH):$SECLIB:$AENLIB:$OUT"
