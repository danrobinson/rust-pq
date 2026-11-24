#!/usr/bin/env bash
set -eu
cpp=${CXX:-c++}
"$cpp" -pthread -std=c++20 -O3 -Ibotan/build/include/public bench/optimized-peers/native.cpp botan/libbotan-3.a -o peer-botan
if test "$(uname -m)" = x86_64; then
    "$cpp" -pthread -std=c++20 -O3 -march=native -flto -DFLUHRER -Iparallel-sphincsplus bench/optimized-peers/native.cpp parallel-sphincsplus/slh-dsa-fast.a -o peer-fluhrer
fi
