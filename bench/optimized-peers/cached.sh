#!/usr/bin/env bash
# Run after the main sweep so compilations and timings do not overlap.
set -eu
export PATH="$HOME/.cargo/bin:$PATH" RUSTFLAGS='-C target-cpu=native'
cp bench/optimized-peers/experiments.rs slh-experiments/src/bin/peer-experiments.rs
cargo build --manifest-path slh-experiments/Cargo.toml --locked --release --bin peer-experiments --features multithread
cp slh-experiments/target/release/peer-experiments peer-cached
python3 bench/optimized-peers/sweep.py --cached
