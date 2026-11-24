#!/usr/bin/env bash
# Run in a disposable directory containing the pinned checkouts alongside
# rust/, bench/peers/public.rs, and bench/optimized-peers/.
set -euo pipefail
export PATH="$HOME/.cargo/bin:$PATH"
export RUSTFLAGS='-C target-cpu=native'
cp bench/peers/public.rs rust/benches/platforms.rs
cargo bench --locked --manifest-path rust/Cargo.toml --features platform-sha2 --bench platforms --no-run --message-format=json >formal-build.json
cp "$(python3 -c 'import json; print(next(x["executable"] for x in map(json.loads,open("formal-build.json")) if x.get("executable")))')" peer-formal
cp bench/optimized-peers/experiments.rs slh-experiments/src/bin/peer-experiments.rs
cargo build --locked --release --manifest-path slh-experiments/Cargo.toml --bin peer-experiments
cp slh-experiments/target/release/peer-experiments .
if [[ "$(uname)" == Darwin ]]; then
    cargo build --locked --release --manifest-path slh-experiments/Cargo.toml --bin peer-experiments --features opencl
    cp slh-experiments/target/release/peer-experiments peer-opencl
fi
