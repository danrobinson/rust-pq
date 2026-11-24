#!/usr/bin/env bash
set -eu
# Run in the Botan checkout. Include the parallel hash engines and each
# architecture's accelerated implementations in the minimized build.
mods=slh_dsa_sha2,slh_dsa_shake,hash_engine_sha2_32,hash_engine_sha2_64,hash_engine_keccak
case "$(uname -m)" in
arm64|aarch64) mods+=,sha2_32_armv8,sha2_64_armv8 ;;
x86_64) mods+=,sha2_32_x86,sha2_32_avx2,sha2_64_x86,sha2_64_avx2,sha2_64_avx512,keccak_perm_bmi2,keccak_perm_avx512
for base in hash_engine_sha2_32 hash_engine_sha2_64 hash_engine_keccak; do mods+=",${base}_avx2,${base}_avx512"; done ;;
esac
python3 configure.py --minimized-build --enable-modules="$mods" --build-targets=static "$@"
make -j"${JOBS:-2}" libs
