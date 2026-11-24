#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.cargo/bin:$PATH"
cp bench/peers/encodings.rs rust/benches/platforms.rs
cargo bench --manifest-path rust/Cargo.toml --locked --features platform-sha2 --bench platforms --no-run --message-format=json >encoding-build.json
cp "$(python3 -c 'import json; print(next(q["executable"] for q in map(json.loads,open("encoding-build.json")) if q.get("executable")))' )" ./codecs-rust
if [[ "$(uname)" == Darwin ]]; then
    prefix="$(brew --prefix openssl@4)"
    cc -O3 -I"$prefix/include" bench/peers/encodings.c -L"$prefix/lib" -lcrypto -o codecs-openssl
else
    cc -O3 -I"$HOME/openssl/include" bench/peers/encodings.c "$HOME/openssl/libcrypto.a" -ldl -pthread -o codecs-openssl
fi
python3 bench/peers/sweep-encodings.py
