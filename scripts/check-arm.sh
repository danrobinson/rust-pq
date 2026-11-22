#!/bin/sh
# Check the hw-sha2 backend on this machine's processor. Needs only Rust (rustup).
#
# The Lean model of the Arm instructions (lean-hw/Arm.lean) is tied to real
# hardware by vectors/arm-wrappers.txt: 1,745 calls of the eighteen intrinsic
# wrappers with the results one processor gave. This script replays the same
# calls on the processor it runs on and fails on the first result that differs,
# then runs every other test of the crate on the hardware backend. Run it on a
# second AArch64 machine (for example an AWS Graviton instance) to learn
# whether that processor agrees with the record.
set -e
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$PATH"

case "$(uname -m)" in
  aarch64|arm64) ;;
  *) echo "check-arm: this is $(uname -m), not an AArch64 machine"; exit 1 ;;
esac

echo "== Processor"
uname -srm
if [ -r /proc/cpuinfo ]; then
  # Linux: implementer and part number identify the core (e.g. 0x41 / 0xd40 is Neoverse V1).
  grep -m1 -i 'model name' /proc/cpuinfo || true
  grep -m1 'CPU implementer' /proc/cpuinfo || true
  grep -m1 'CPU part' /proc/cpuinfo || true
  grep -m1 'CPU variant' /proc/cpuinfo || true
  if grep -m1 '^Features' /proc/cpuinfo | grep -qw sha2; then echo "sha2: reported by the kernel"; else echo "sha2: NOT reported by the kernel"; fi
  if grep -m1 '^Features' /proc/cpuinfo | grep -qw dit; then echo "dit: reported by the kernel"; else echo "dit: not reported by the kernel"; fi
else
  sysctl -n machdep.cpu.brand_string 2>/dev/null || true
  echo "sha2: hw.optional.arm.FEAT_SHA256 = $(sysctl -n hw.optional.arm.FEAT_SHA256 2>/dev/null || echo unknown)"
  echo "dit: hw.optional.arm.FEAT_DIT = $(sysctl -n hw.optional.arm.FEAT_DIT 2>/dev/null || echo unknown)"
fi
rustc --version

echo "== The recorded calls against this processor's instructions"
(cd rust && cargo test --release --features hw-sha2 --lib arm_wrappers_match_the_record -- --exact --nocapture \
    sha256::hw::vectors::arm_wrappers_match_the_record)

echo "== All tests of the crate on the hardware backend"
(cd rust && cargo test --release --features hw-sha2)

echo "== The RustCrypto-compatible adapter on the hardware backend"
(cd compat && cargo test --features hw-sha2)

echo "check-arm: this processor agrees with vectors/arm-wrappers.txt on all $(wc -l < vectors/arm-wrappers.txt | tr -d ' ') recorded calls."
