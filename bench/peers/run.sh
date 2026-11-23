#!/usr/bin/env bash
# Run at the root of an isolated snapshot with the desired OpenSSL source built.
set -euo pipefail
export PATH="$HOME/.cargo/bin:$PATH"
mkdir -p out
cp bench/peers/public.rs rust/benches/platforms.rs
cargo bench --manifest-path rust/Cargo.toml --locked --features platform-sha2 --bench platforms --no-run --message-format=json > build.json
cp "$(python3 -c 'import json; print(next(q["executable"] for q in map(json.loads,open("build.json")) if q.get("executable")))' )" ./peer-rust
if [[ "$(uname)" == Darwin ]]; then
    prefix="$(brew --prefix openssl@4)"
    cc -O3 -I"$prefix/include" bench/peers/openssl.c -L"$prefix/lib" -lcrypto -o peer-openssl
    { sw_vers; sysctl -n machdep.cpu.brand_string; "$prefix/bin/openssl" version -a; otool -L peer-openssl; } >out/host.txt
else
    cc -O3 -I"$HOME/openssl/include" bench/peers/openssl.c "$HOME/openssl/libcrypto.a" -ldl -pthread -o peer-openssl
    { lscpu; uname -a; cat /etc/os-release; (cd "$HOME/openssl"; perl configdata.pm --dump | head -65 || true); } >out/host.txt
fi
rustc -vV >>out/host.txt
cc --version >>out/host.txt
python3 bench/peers/sweep.py
