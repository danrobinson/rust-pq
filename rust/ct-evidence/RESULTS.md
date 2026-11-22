# Binary-level constant-time evidence for `slhdsa` (SLH-DSA-SHA2-128s): results

*This file is generated from `scripts/RESULTS.template.md` and the raw outputs
in `out/default/` and `out/hw-sha2/` by `scripts/make_results.py`. Every table
and number is taken from the raw files; the prose describes the runs of
2026-11-21. If you rerun and regenerate, re-read the prose against the new
numbers (the generator stops if a raw file contradicts a stated outcome, but
it does not read the prose).*

**Status: evidence, not proof.** Everything below is testing of two compiled
artefacts on one machine. The source-level argument is the separate Lean
effort; this document only checks what rustc actually emitted.

## Environment

| | |
|---|---|
| Date | 2026-11-21 (local time; the `date:` lines below are UTC) |
| Machine | Apple M5 Ultra (12 performance + 24 efficiency cores), 512 GB |
| OS | macOS 27.2 (26B118), Darwin 27.2.0, arm64 |
| Compiler | rustc 1.100.0 (0ef1bc386 2026-11-09), LLVM 23.1.5, host/target `aarch64-apple-darwin` |
| Flags | default cargo `release` profile: `opt-level=3`, no LTO, `codegen-units=16`, `panic=unwind`, no `RUSTFLAGS`, no `target-cpu` override |
| Emulator | Unicorn 2.1.4 (`libunicorn.2.dylib` from the PyPI wheel), CPU model `max` |
| Crate under test | `..` (`slhdsa` 0.1.0) as of 2026-11-21, unmodified, read only; the SHA-256 of every source file at build time is listed below (the files were the same when this file was generated, and equal to git commit c199248). Two builds: **default** features, and **hw-sha2** (`--features hw-sha2`) |

Build record of the default variant (`out/default/build.txt`):

```
date: 2026-11-22T04:36:47Z
variant: default
machine: Apple M5 Ultra, 12+24 cores; macOS 27.2 (26B118); Darwin 27.2.0 arm64
rustc: rustc 1.100.0 (0ef1bc386 2026-11-09);binary: rustc;commit-hash: 0ef1bc386059596dada8fb65b50425aab2ea637a;commit-date: 2026-11-09;host: aarch64-apple-darwin;release: 1.100.0;LLVM version: 23.1.5;
cargo: cargo 1.100.0 (3acc79c0c 2026-11-05)
unicorn: 2.1.4
sha256 of the crate under test (..):
0c31f095d4151b64a657b1f5560879a69c640bef6d0aeac4a1a214101ab94ab4  Cargo.toml
5f1d3647f1d1cb006aa7b471b4ce48f1454b4ece027096e59c0225efe749c5c6  src/address.rs
07e9c51610329f577065e768d2f87666c13dad81c169b0f408beec4d4759e49b  src/api.rs
3f2109af90dda63ae3887988ef929c3156cad8aed31fa242d6823980bf413581  src/fors.rs
afdcb8d1aba78e4da41a545f9c45ba26593e14d0ee0d64fbd0c924457390e1cd  src/hash.rs
0b5721edc661ee55e8bf72ee80e8b62980d6500bd01a6394774a4fb163292fe8  src/ht.rs
7cd4344ee5801f9184dd7870651ce46082d17ac37c7db40c535eb0069558f31a  src/lib.rs
e87ef58e0dc4e1c5978e6f2d8ed809bf0c0caf094e0e8416f76ba0bee54675e5  src/params.rs
5cb1b2ebfe0a589f5c3da8816935f45e82ba8cb12503f3c9eb55856c8198f358  src/sha256.rs
af6cbc2880ef8a26adbd067013c21df3460734b7d6ffe755b08b65f209d1e7d3  src/slh.rs
458d560db3d47deae7280ae1a8fa6bb9bc9b8d16641ccdf0f41b18d850413891  src/util.rs
2dd8185a2fdc561f785138a45f398fe6bdc8f97c8233c26a3337b4b9d85292d8  src/wots.rs
d5548f0857e9666006d885dfd75a983dabc170a2e361c89721ae67108fc01d4e  src/xmss.rs
sha256 of the harness binaries:
80da4a54c166d286291c61ff8cb19a573f72a22a5f6c5583f7291bd4cbc67edf  target/release/cttrace
7f5bdc6b8fef5e2ec3772d9107f4010c031b911fd1847a4c081022cad0daf98d  target/release/dudect
```

Build record of the hw-sha2 variant (`out/hw-sha2/build.txt`):

```
date: 2026-11-22T04:37:10Z
variant: hw-sha2
machine: Apple M5 Ultra, 12+24 cores; macOS 27.2 (26B118); Darwin 27.2.0 arm64
rustc: rustc 1.100.0 (0ef1bc386 2026-11-09);binary: rustc;commit-hash: 0ef1bc386059596dada8fb65b50425aab2ea637a;commit-date: 2026-11-09;host: aarch64-apple-darwin;release: 1.100.0;LLVM version: 23.1.5;
cargo: cargo 1.100.0 (3acc79c0c 2026-11-05)
unicorn: 2.1.4
sha256 of the crate under test (..):
0c31f095d4151b64a657b1f5560879a69c640bef6d0aeac4a1a214101ab94ab4  Cargo.toml
5f1d3647f1d1cb006aa7b471b4ce48f1454b4ece027096e59c0225efe749c5c6  src/address.rs
07e9c51610329f577065e768d2f87666c13dad81c169b0f408beec4d4759e49b  src/api.rs
3f2109af90dda63ae3887988ef929c3156cad8aed31fa242d6823980bf413581  src/fors.rs
afdcb8d1aba78e4da41a545f9c45ba26593e14d0ee0d64fbd0c924457390e1cd  src/hash.rs
0b5721edc661ee55e8bf72ee80e8b62980d6500bd01a6394774a4fb163292fe8  src/ht.rs
7cd4344ee5801f9184dd7870651ce46082d17ac37c7db40c535eb0069558f31a  src/lib.rs
e87ef58e0dc4e1c5978e6f2d8ed809bf0c0caf094e0e8416f76ba0bee54675e5  src/params.rs
5cb1b2ebfe0a589f5c3da8816935f45e82ba8cb12503f3c9eb55856c8198f358  src/sha256.rs
af6cbc2880ef8a26adbd067013c21df3460734b7d6ffe755b08b65f209d1e7d3  src/slh.rs
458d560db3d47deae7280ae1a8fa6bb9bc9b8d16641ccdf0f41b18d850413891  src/util.rs
2dd8185a2fdc561f785138a45f398fe6bdc8f97c8233c26a3337b4b9d85292d8  src/wots.rs
d5548f0857e9666006d885dfd75a983dabc170a2e361c89721ae67108fc01d4e  src/xmss.rs
sha256 of the harness binaries:
ca41aae29f37e70702b9bec66ca51085b428cf285aef87f946b1a0d2701357fc  target-hw/release/cttrace
0165e3fbf53cfe31171ca9039703a473c1ae4e56fd77e7f6f67cf10878c61cb9  target-hw/release/dudect
```

**The traced code is the native code.** `cttrace` executes its own Mach-O
image inside the emulator, so no bare-metal rebuild is involved. In addition,
`scripts/disasm_check.py` compared the `slhdsa` object code inside this
package's dependency rlib (A) with the rlib that `cargo build --release
--locked` produces from the main crate's own manifest (B; built into a target
directory inside this package, so `..` is not written to):

* default: 51 functions identical instruction-for-instruction (incl. relocation targets), 0 different, 0 present in only one; 6991 disassembly lines (instructions + relocation records) compared in A; 0 code ranges left unnamed.
* hw-sha2: 55 functions identical instruction-for-instruction (incl. relocation targets), 0 different, 0 present in only one; 9004 disassembly lines (instructions + relocation records) compared in A; 0 code ranges left unnamed.

The constant tables are the same too; the only difference between A and B is
that the source-file paths in the panic-location records are absolute in A
and relative in B (section 2).

## Summary

| # | Experiment | default build | hw-sha2 build |
|---|---|---|---|
| T0 | Emulator check: SHA-256 instructions executed, emulated output = native output | 14 entry points, none executes a SHA-256 instruction, all outputs equal | 14 entry points, all execute SHA-256 instructions, all outputs equal |
| T1 | Component traces with the secret varied (control flow + memory addresses + call-outs): full event sequence between runs with identical public inputs | 61 function/parameter rows, 197 public configurations, 3433 pairs: **all identical, 0 divergences** | 61 rows, 197 public configurations, 3433 pairs: **all identical, 0 divergences** |
| T1b | The verifier's recomputation (`*_pk_from_sig`) with the signature bytes varied | 3 rows, 108 pairs: all identical | 3 rows, 108 pairs: all identical |
| T2 | Positive controls (leaky code in the harness), same checker | 3 controls, 194 pairs, 147 differing: **all detected** | 3 controls, 194 pairs, 147 differing: **all detected** |
| T3 | Public-variation controls (a public input varied must change the trace) | 3 controls, 100 pairs, 100 differing: all detected | 4 controls, 108 pairs, 108 differing (includes the `PREFIX` row): all detected |
| T4 | Whole signing with the declassified values pinned, 8 entry points: run B (fresh SK.seed, SK.prf, addrnd) vs run A with R, PK_FORS and the XMSS roots forced to A's values | 40 public configurations, 136 pairs: **all identical**; every unpinned control differs | 56 public configurations, 264 pairs: **all identical**; every unpinned control differs |
| T5 | Whole-signature unconditioned profile over honest random keys | 24 + 24 runs; call counts of every function constant; instruction count spread 3452 out of 6.51e+09 (checked: 3452 out of 1.22e+10) | 24 + 24 runs; call counts and SHA-256 instruction counts constant; instruction count spread 3837 out of 3.11e+08 (checked: 3837 out of 5.83e+08) |
| S1 | Static disassembly of the `slhdsa` functions in the binary | 45 functions, 6330 instructions: 252 conditional branches, 0 indirect branches, 0 integer divisions, 0 crypto-extension instructions; no call of `memcmp`/`bcmp` | 44 functions, 8088 instructions: 291 conditional branches, 0 indirect branches, 0 integer divisions, 1114 crypto-extension instructions; no call of `memcmp`/`bcmp` |
| D0 | Timing noise floor: random vs random before and after each series, 52 rows | no row above 4.5 (largest 3.84 before, 3.42 after): timing usable | no row above 4.5 (largest 3.19 before, 3.47 after): timing usable |
| D1 | dudect, 50 component rows, fixed vs random secret (both classes prepared alike), `PSTATE.DIT = 0` | **8 rows above 4.5**, all short hash-level calls (largest 67.86) | **1 row above 4.5**: `sha256/len=1` (6.7) |
| D2 | the same with `PSTATE.DIT = 1` | no row above 4.5 (largest 3.28) | no row above 4.5 (largest 3.09) |
| D3 | diagnostics, `PSTATE.DIT = 0`: two different fixed secrets; the all-zero secret vs another fixed one | not distinguishable; **distinguishable in 25 of 50 rows** (bulk hash inputs; largest 238.37) | not distinguishable; **distinguishable in 6 of 50 rows** (largest 22.17; includes an all-zero SK.seed in `fors_sk_gen`) |
| D4 | the same diagnostics with `PSTATE.DIT = 1` | not distinguishable | not distinguishable |
| D5 | dudect, whole signing, plain and checked signer, 4 x 600 signatures, `PSTATE.DIT = 0` | no row above 4.5 (largest 2.64) | no row above 4.5 (largest 2.82) |
| D6 | dudect positive controls (`leaky_cmp`, `leaky_loop`) | detected in every fixed-vs-random run (max abs t 76, 116 in the first) | detected in every fixed-vs-random run (76, 108 in the first) |

**No secret-dependent divergence was found in the compiled code of either
build** (control flow, memory addresses, allocation sizes, copy lengths).
The one non-clean result is in the timing tests and concerns the processor:
with `PSTATE.DIT = 0` (the state the crate runs in unless its caller sets
DIT) the time the hash-level functions take depends on the data they process
-- a class that keeps presenting one value is distinguishable from one that
never repeats a value, and an all-zero value from another value -- in both
builds, more weakly in the hw-sha2 build; with `PSTATE.DIT = 1` no dependence
was detected in any row. No timing difference was found in whole signing, nor
in any design in the rows at the level of WOTS+, XMSS, FORS above the leaves
and key generation. See "Timing finding" in section 3.

## 1. Deterministic trace comparison

### Method

See README.md for the mechanism. In short: the release-optimised native code is
executed under Unicorn from a fixed initial state; every executed basic block
(address, size), every memory read/write (address, size) and every call-out
(malloc/realloc/free/memcpy/memset with pointer and length arguments) is
recorded; two runs are "identical" iff the complete event sequences are equal
(compared via 128-bit rolling hash, event counts and checkpoints every 65536
events). Stack, heap and I/O buffers are at fixed guest addresses and the
guest allocator is deterministic, so addresses are compared without any
normalisation. Every emulated run's output was compared with a native call of
the same wrapper: all equal ("emu==native" column), so the emulator executed
the code faithfully, including the SHA-256 instructions of the hw-sha2 build.

For each row: the public inputs (PK.seed, ADRS, indices, lengths, step ranges,
block prefixes, public messages) are pseudo-random but fixed per "public
config"; the varied input is redrawn for every pair. A pair = (reference run,
run with a different value of the varied bytes); the first pair of every
public configuration uses the all-zero value, the others fresh pseudo-random
values. All trace experiments ran with 8 threads.

### T0. The emulator executes the SHA-256 instructions (`out/*/hwcheck.md`)

Each entry point is run once under the emulator with block profiling; the
executed blocks are decoded and the SHA-256 instructions counted.

default build:

| entry point | insns executed | SHA256H | SHA256H2 | SHA256SU0 | SHA256SU1 | emu==native output | verdict |
|---|---|---|---|---|---|---|---|
| sha256/len=64 | 7520 | 0 | 0 | 0 | 0 | yes | as expected |
| compress (copy inlined into the wrapper) | 3207 | 0 | 0 | 0 | 0 | yes | as expected |
| thash_short/len=16 | 3252 | 0 | 0 | 0 | 0 | yes | as expected |
| thash/len=224 | 13360 | 0 | 0 | 0 | 0 | yes | as expected |
| thash_values | 32042 | 0 | 0 | 0 | 0 | yes | as expected |
| prf_msg/mlen=32 | 14107 | 0 | 0 | 0 | 0 | yes | as expected |
| chain_blocks/n=1,steps=0..15 | 43776 | 0 | 0 | 0 | 0 | yes | as expected |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | 822717 | 0 | 0 | 0 | 0 | yes | as expected |
| chain_blocks_portable/n=4,steps=0..15 | 174740 | 0 | 0 | 0 | 0 | yes | as expected |
| wots_pk_gen | 1666912 | 0 | 0 | 0 | 0 | yes | as expected |
| fors_node/z=7 | 1173585 | 0 | 0 | 0 | 0 | yes | as expected |
| slh_keygen_internal | 855131659 | 0 | 0 | 0 | 0 | yes | as expected |
| slh::slh_sign_internal | 6513220472 | 0 | 0 | 0 | 0 | yes | as expected |
| slh::slh_sign_internal_checked | 12171178015 | 0 | 0 | 0 | 0 | yes | as expected |

SHA-256 instructions present in this binary's `__text` section (static count): SHA256H 0, SHA256H2 0, SHA256SU0 0, SHA256SU1 0.

hw-sha2 build:

| entry point | insns executed | SHA256H | SHA256H2 | SHA256SU0 | SHA256SU1 | emu==native output | verdict |
|---|---|---|---|---|---|---|---|
| sha256/len=64 | 1868 | 32 | 32 | 24 | 24 | yes | as expected |
| compress (copy inlined into the wrapper) | 392 | 16 | 16 | 12 | 12 | yes | as expected |
| thash_short/len=16 | 495 | 16 | 16 | 12 | 12 | yes | as expected |
| thash/len=224 | 2124 | 64 | 64 | 48 | 48 | yes | as expected |
| thash_values | 4071 | 160 | 160 | 120 | 120 | yes | as expected |
| prf_msg/mlen=32 | 2721 | 64 | 64 | 48 | 48 | yes | as expected |
| chain_blocks/n=1,steps=0..15 | 1877 | 226 | 211 | 180 | 180 | yes | as expected |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | 37889 | 4231 | 3949 | 3384 | 3384 | yes | as expected |
| chain_blocks_portable/n=4,steps=0..15 | 23290 | 960 | 960 | 720 | 720 | yes | as expected |
| wots_pk_gen | 75867 | 8562 | 8002 | 6840 | 6840 | yes | as expected |
| fors_node/z=7 | 82912 | 5754 | 5371 | 4596 | 4596 | yes | as expected |
| slh_keygen_internal | 39104965 | 4391936 | 4105216 | 3508224 | 3508224 | yes | as expected |
| slh::slh_sign_internal | 311239549 | 33328712 | 31150032 | 26621856 | 26621856 | yes | as expected |
| slh::slh_sign_internal_checked | 583224615 | 62265032 | 58194448 | 49735392 | 49735392 | yes | as expected |

SHA-256 instructions present in this binary's `__text` section (static count): SHA256H 315, SHA256H2 295, SHA256SU0 254, SHA256SU1 254.

In the hw-sha2 build every hash goes through the instructions (for example a
15-step chain executes 15 x 15 + 1 = 226 `SHA256H`: fifteen four-round groups
per step, and the first group once for the whole chain), the emulator's
results equal the CPU's on every run of every experiment, and
`sha256::hw_active()` is true (on `aarch64-apple-darwin` the feature test is a
compile-time constant, so no detection code runs in the guest). The default
build contains and executes no SHA-256 instruction.

### T1-T3. Components and controls, default build (`out/default/trace_components.md`)

crate under test: `slhdsa` built with default features, cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

| function (public params) | varied input | public configs | pairs | identical traces | differing | insns/run | blocks/run | mem accesses/run | call-outs/run | emu==native output | verdict |
|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 1 | 65 | 65 | 0 | 4361 | 351 | 952 | 6 | yes | PASS (all identical) |
| sha256/len=16 | all message bytes | 1 | 65 | 65 | 0 | 4112 | 305 | 867 | 5 | yes | PASS (all identical) |
| sha256/len=55 | all message bytes | 1 | 65 | 65 | 0 | 3552 | 214 | 685 | 4 | yes | PASS (all identical) |
| sha256/len=56 | all message bytes | 1 | 65 | 65 | 0 | 7604 | 510 | 1428 | 5 | yes | PASS (all identical) |
| sha256/len=64 | all message bytes | 1 | 65 | 65 | 0 | 7520 | 569 | 1407 | 5 | yes | PASS (all identical) |
| sha256/len=119 | all message bytes | 1 | 65 | 65 | 0 | 6732 | 434 | 1149 | 4 | yes | PASS (all identical) |
| sha256/len=120 | all message bytes | 1 | 65 | 65 | 0 | 10784 | 730 | 1892 | 5 | yes | PASS (all identical) |
| sha256/len=256 | all message bytes | 1 | 65 | 65 | 0 | 17057 | 1232 | 2799 | 5 | yes | PASS (all identical) |
| sha256/len=560 | all message bytes | 1 | 65 | 65 | 0 | 29076 | 1994 | 4425 | 4 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 1 | 65 | 65 | 0 | 16248 | 1385 | 3446 | 21 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 1 | 65 | 65 | 0 | 22789 | 1861 | 4440 | 22 | yes | PASS (all identical) |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 1 | 65 | 65 | 0 | 19962 | 1742 | 4124 | 22 | yes | PASS (all identical) |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 1 | 65 | 65 | 0 | 16773 | 1492 | 3637 | 23 | yes | PASS (all identical) |
| compress (copy inlined into the wrapper) | state and block | 1 | 65 | 65 | 0 | 3207 | 157 | 500 | 0 | yes | PASS (all identical) |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 3252 | 228 | 581 | 1 | yes | PASS (all identical) |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 3252 | 228 | 581 | 1 | yes | PASS (all identical) |
| thash/len=16 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 4030 | 287 | 896 | 8 | yes | PASS (all identical) |
| thash/len=32 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 3822 | 255 | 832 | 8 | yes | PASS (all identical) |
| thash/len=224 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 13360 | 917 | 2224 | 8 | yes | PASS (all identical) |
| thash/len=560 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 33165 | 2369 | 5251 | 10 | yes | PASS (all identical) |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 4 | 68 | 68 | 0 | 32042 | 1583 | 4873 | 0 | yes | PASS (all identical) |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 14494 | 898 | 2659 | 11 | yes | PASS (all identical) |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 14107 | 836 | 2538 | 12 | yes | PASS (all identical) |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 17235 | 1048 | 2986 | 12 | yes | PASS (all identical) |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 65754 | 4433 | 10213 | 13 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 43776 | 1727 | 6407 | 1 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=3..10 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 20568 | 815 | 3127 | 1 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=5..5 (none) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 140 | 16 | 200 | 1 | yes | PASS (all identical) |
| chain_blocks/n=3,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 131086 | 5159 | 18835 | 1 | yes | PASS (all identical) |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 174741 | 6875 | 25049 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 1527902 | 60043 | 217651 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 904066 | 35532 | 129444 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=d_i..15 (wots_pk_from_sig) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 976470 | 38381 | 139637 | 1 | yes | PASS (all identical) |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 68 | 68 | 0 | 42665 | 1684 | 6821 | 1 | yes | PASS (all identical) |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 388760 | 15259 | 60737 | 1 | yes | PASS (all identical) |
| chain_blocks/n=7,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 144 | 144 | 0 | 111097 | 4383 | 16107 | 1 | yes | PASS (all identical) |
| chain_blocks/n=64,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 665004 | 26198 | 96212 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,random ranges,distinct prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 369193 | 14547 | 53491 | 1 | yes | PASS (all identical) |
| chain_blocks_portable/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 174740 | 6874 | 25049 | 1 | yes | PASS (all identical) |
| chain_blocks_portable/n=35,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 36 | 36 | 0 | 360126 | 14201 | 52090 | 1 | yes | PASS (all identical) |
| wots_pk_gen | SK.seed | 4 | 68 | 68 | 0 | 1666912 | 65859 | 239449 | 2 | yes | PASS (all identical) |
| wots_sign | SK.seed (message m public, fixed) | 8 | 72 | 72 | 0 | 1027524 | 40775 | 149220 | 20 | yes | PASS (all identical) |
| xmss_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 1666938 | 65863 | 239479 | 2 | yes | PASS (all identical) |
| xmss_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 3337117 | 131955 | 479495 | 5 | yes | PASS (all identical) |
| xmss_node/z=2 | SK.seed | 4 | 68 | 68 | 0 | 6677475 | 264139 | 959527 | 11 | yes | PASS (all identical) |
| xmss_node/z=3 | SK.seed | 2 | 34 | 34 | 0 | 13358191 | 528507 | 1919591 | 23 | yes | PASS (all identical) |
| xmss_node/z=4 | SK.seed | 2 | 34 | 34 | 0 | 26719623 | 1057243 | 3839719 | 47 | yes | PASS (all identical) |
| xmss_sign | SK.seed (m, idx public, fixed) | 2 | 18 | 18 | 0 | 854372796 | 33808295 | 122780035 | 1544 | yes | PASS (all identical) |
| fors_sk_gen | SK.seed | 4 | 68 | 68 | 0 | 3270 | 230 | 598 | 1 | yes | PASS (all identical) |
| fors_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 6441 | 262 | 1298 | 2 | yes | PASS (all identical) |
| fors_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 15722 | 632 | 2843 | 2 | yes | PASS (all identical) |
| fors_node/z=3 | SK.seed | 4 | 68 | 68 | 0 | 70987 | 2811 | 11859 | 2 | yes | PASS (all identical) |
| fors_node/z=6 | SK.seed | 4 | 68 | 68 | 0 | 585620 | 23062 | 95131 | 2 | yes | PASS (all identical) |
| fors_node/z=7 | SK.seed | 4 | 68 | 68 | 0 | 1173585 | 46189 | 190163 | 2 | yes | PASS (all identical) |
| fors_node/z=8 | SK.seed | 2 | 18 | 18 | 0 | 2350413 | 92606 | 380864 | 5 | yes | PASS (all identical) |
| fors_node/z=12 | SK.seed | 2 | 18 | 18 | 0 | 37655253 | 1485116 | 6101894 | 95 | yes | PASS (all identical) |
| fors_sign | SK.seed (md public, fixed) | 2 | 18 | 18 | 0 | 526649311 | 20767300 | 85367011 | 1457 | yes | PASS (all identical) |
| fors_pk_gen | SK.seed | 2 | 18 | 18 | 0 | 527187174 | 20792653 | 85428490 | 1344 | yes | PASS (all identical) |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 2 | 26 | 26 | 0 | 855131659 | 33839032 | 122888215 | 1535 | yes | PASS (all identical) |
| slh_keygen_internal/all-inputs | SK.seed, SK.prf and PK.seed | 1 | 13 | 13 | 0 | 855131659 | 33839032 | 122888215 | 1535 | yes | PASS (all identical) |
| api::keygen | SK.seed and SK.prf (PK.seed fixed) | 2 | 18 | 18 | 0 | 855131683 | 33839034 | 122888251 | 1535 | yes | PASS (all identical) |
| wots_pk_from_sig | WOTS+ signature bytes (m public, fixed) | 4 | 36 | 36 | 0 | 822120 | 32870 | 118744 | 10 | yes | PASS (all identical) |
| xmss_pk_from_sig | XMSS signature bytes (m, idx public, fixed) | 4 | 36 | 36 | 0 | 938408 | 38357 | 136133 | 19 | yes | PASS (all identical) |
| fors_pk_from_sig | FORS signature bytes (md public, fixed) | 4 | 36 | 36 | 0 | 579119 | 23529 | 98738 | 19 | yes | PASS (all identical) |
| INFO fors_sign, PUBLIC md varied | public digest md (SK.seed fixed) | 1 | 9 | 9 | 0 | 526649311 | 20767300 | 85367011 | 1457 | yes | info: identical |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 1 | 65 | 35 | 30 | 15 | 2 | 5 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_table (secret-indexed lookup) | secret index (leaky by construction) | 1 | 64 | 0 | 64 | 14 | 1 | 7 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 1 | 65 | 12 | 53 | 11544 | 776 | 2327 | 12 | yes | PASS (control: difference detected) |
| CONTROL wots_sign, PUBLIC m varied | public message m (chain lengths are public) | 2 | 34 | 0 | 34 | 897100 | 35646 | 130827 | 20 | yes | PASS (control: difference detected) |
| CONTROL chain_blocks n=4, PUBLIC end of block 0 varied | public step count of one block (0..255) | 1 | 33 | 0 | 33 | 108018 | 4253 | 15619 | 1 | yes | PASS (control: difference detected) |
| CONTROL sha256, PUBLIC length varied | public message length (0..255) | 1 | 33 | 0 | 33 | 6979 | 471 | 1225 | 4 | yes | PASS (control: difference detected) |
| PREFIX chain_blocks n=8, PUBLIC: whether block 2 shares the others' 16-byte prefix | one public bit: block 2 starts like the other blocks, or not | 1 | 8 | 8 | 0 | 94034 | 3700 | 13817 | 1 | yes | info: identical |

Divergence details (first differing pair of each row):

- `CONTROL leaky_cmp (early-exit compare of secret)`: first divergence at event #5: last common event: read 0x50007ffefb (size/arg 1) in basic block ct_evidence::w_leaky_cmp+0x0; A: exec block ct_evidence::w_leaky_cmp+0x6c (size/arg 16) in basic block ct_evidence::w_leaky_cmp+0x6c | B: exec block ct_evidence::w_leaky_cmp+0x2c (size/arg 36) in basic block ct_evidence::w_leaky_cmp+0x2c
- `CONTROL leaky_table (secret-indexed lookup)`: first divergence at event #6: last common event: read 0x50007ffef8 (size/arg 8) in basic block ct_evidence::w_leaky_table+0x0; A: read 0x10254821c (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0 | B: read 0x102548150 (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0
- `CONTROL leaky_loop (secret-dependent iteration count)`: first divergence at event #12: last common event: write 0x50007ffeb8 (size/arg 8) in basic block ct_evidence::w_leaky_loop+0x0; A: exec block ct_evidence::w_leaky_loop+0x30 (size/arg 28) in basic block ct_evidence::w_leaky_loop+0x30 | B: exec block ct_evidence::w_leaky_loop+0x5c (size/arg 24) in basic block ct_evidence::w_leaky_loop+0x5c
- `CONTROL wots_sign, PUBLIC m varied`: first divergence at event #22197: last common event: write 0x50007ff3ac (size/arg 4) in basic block slhdsa::hash::chain_blocks_portable+0x98; A: exec block slhdsa::hash::chain_blocks_portable+0xb0 (size/arg 464) in basic block slhdsa::hash::chain_blocks_portable+0xb0 | B: exec block slhdsa::hash::chain_blocks_portable+0x7c (size/arg 12) in basic block slhdsa::hash::chain_blocks_portable+0x7c
- `CONTROL chain_blocks n=4, PUBLIC end of block 0 varied`: first divergence at event #213: last common event: write 0x50007ff93c (size/arg 4) in basic block slhdsa::hash::chain_blocks_portable+0x98; A: exec block slhdsa::hash::chain_blocks_portable+0xb0 (size/arg 464) in basic block slhdsa::hash::chain_blocks_portable+0xb0 | B: exec block slhdsa::hash::chain_blocks_portable+0x7c (size/arg 12) in basic block slhdsa::hash::chain_blocks_portable+0x7c
- `CONTROL sha256, PUBLIC length varied`: first divergence at event #33: last common event: write 0x50007ffd40 (size/arg 8) in basic block slhdsa::sha256::sha256_from+0x0; A: exec block slhdsa::sha256::sha256_from+0x58 (size/arg 36) in basic block slhdsa::sha256::sha256_from+0x58 | B: exec block slhdsa::sha256::sha256_from+0x4c (size/arg 12) in basic block slhdsa::sha256::sha256_from+0x4c

overall: ALL ROWS AS EXPECTED

### T1-T3. Components and controls, hw-sha2 build (`out/hw-sha2/trace_components.md`)

crate under test: `slhdsa` built with `--features hw-sha2` (`sha256::hw_active()` = true), cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

| function (public params) | varied input | public configs | pairs | identical traces | differing | insns/run | blocks/run | mem accesses/run | call-outs/run | emu==native output | verdict |
|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 1 | 65 | 65 | 0 | 1490 | 242 | 613 | 6 | yes | PASS (all identical) |
| sha256/len=16 | all message bytes | 1 | 65 | 65 | 0 | 1241 | 196 | 528 | 5 | yes | PASS (all identical) |
| sha256/len=55 | all message bytes | 1 | 65 | 65 | 0 | 682 | 105 | 346 | 4 | yes | PASS (all identical) |
| sha256/len=56 | all message bytes | 1 | 65 | 65 | 0 | 1943 | 291 | 812 | 5 | yes | PASS (all identical) |
| sha256/len=64 | all message bytes | 1 | 65 | 65 | 0 | 1868 | 286 | 794 | 5 | yes | PASS (all identical) |
| sha256/len=119 | all message bytes | 1 | 65 | 65 | 0 | 1077 | 152 | 530 | 4 | yes | PASS (all identical) |
| sha256/len=120 | all message bytes | 1 | 65 | 65 | 0 | 2338 | 338 | 996 | 5 | yes | PASS (all identical) |
| sha256/len=256 | all message bytes | 1 | 65 | 65 | 0 | 3035 | 424 | 1322 | 5 | yes | PASS (all identical) |
| sha256/len=560 | all message bytes | 1 | 65 | 65 | 0 | 3890 | 487 | 1790 | 4 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 1 | 65 | 65 | 0 | 4936 | 824 | 2208 | 21 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 1 | 65 | 65 | 0 | 5897 | 950 | 2626 | 22 | yes | PASS (all identical) |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 1 | 65 | 65 | 0 | 5864 | 1005 | 2604 | 22 | yes | PASS (all identical) |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 1 | 65 | 65 | 0 | 5461 | 931 | 2399 | 23 | yes | PASS (all identical) |
| compress (copy inlined into the wrapper) | state and block | 1 | 65 | 65 | 0 | 392 | 46 | 184 | 0 | yes | PASS (all identical) |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 495 | 53 | 263 | 1 | yes | PASS (all identical) |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 495 | 53 | 263 | 1 | yes | PASS (all identical) |
| thash/len=16 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 1159 | 181 | 557 | 8 | yes | PASS (all identical) |
| thash/len=32 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 951 | 149 | 493 | 8 | yes | PASS (all identical) |
| thash/len=224 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 2124 | 288 | 1029 | 8 | yes | PASS (all identical) |
| thash/len=560 | m (len=224: the 14 FORS roots) | 4 | 68 | 68 | 0 | 5189 | 690 | 2328 | 10 | yes | PASS (all identical) |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 4 | 68 | 68 | 0 | 4071 | 466 | 1973 | 0 | yes | PASS (all identical) |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 3108 | 458 | 1395 | 11 | yes | PASS (all identical) |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 2721 | 397 | 1274 | 12 | yes | PASS (all identical) |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 3064 | 436 | 1442 | 12 | yes | PASS (all identical) |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 9733 | 1261 | 4360 | 13 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 1877 | 54 | 439 | 1 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=3..10 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 1029 | 38 | 423 | 1 | yes | PASS (all identical) |
| chain_blocks/n=1,steps=5..5 (none) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 210 | 16 | 338 | 1 | yes | PASS (all identical) |
| chain_blocks/n=3,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 5581 | 71 | 2003 | 1 | yes | PASS (all identical) |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 7585 | 91 | 2715 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 64477 | 659 | 20971 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 41371 | 782 | 16490 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,steps=d_i..15 (wots_pk_from_sig) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 44173 | 803 | 17145 | 1 | yes | PASS (all identical) |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 68 | 68 | 0 | 2857 | 133 | 1654 | 1 | yes | PASS (all identical) |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 24076 | 1022 | 12340 | 1 | yes | PASS (all identical) |
| chain_blocks/n=7,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 144 | 144 | 0 | 5365 | 156 | 2305 | 1 | yes | PASS (all identical) |
| chain_blocks/n=64,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 32361 | 824 | 13996 | 1 | yes | PASS (all identical) |
| chain_blocks/n=35,random ranges,distinct prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 72 | 72 | 0 | 18380 | 535 | 8177 | 1 | yes | PASS (all identical) |
| chain_blocks_portable/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 34 | 34 | 0 | 23290 | 2794 | 10699 | 1 | yes | PASS (all identical) |
| chain_blocks_portable/n=35,random ranges,two prefixes | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 36 | 36 | 0 | 48067 | 5837 | 21950 | 1 | yes | PASS (all identical) |
| wots_pk_gen | SK.seed | 4 | 68 | 68 | 0 | 75867 | 1436 | 26735 | 2 | yes | PASS (all identical) |
| wots_sign | SK.seed (message m public, fixed) | 8 | 72 | 72 | 0 | 51246 | 1529 | 20987 | 20 | yes | PASS (all identical) |
| xmss_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 75893 | 1439 | 26765 | 2 | yes | PASS (all identical) |
| xmss_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 152270 | 2932 | 53749 | 5 | yes | PASS (all identical) |
| xmss_node/z=2 | SK.seed | 4 | 68 | 68 | 0 | 305024 | 5918 | 107717 | 11 | yes | PASS (all identical) |
| xmss_node/z=3 | SK.seed | 2 | 34 | 34 | 0 | 610532 | 11890 | 215653 | 23 | yes | PASS (all identical) |
| xmss_node/z=4 | SK.seed | 2 | 34 | 34 | 0 | 1221548 | 23834 | 431525 | 47 | yes | PASS (all identical) |
| xmss_sign | SK.seed (m, idx public, fixed) | 2 | 18 | 18 | 0 | 39071767 | 763925 | 13806316 | 1544 | yes | PASS (all identical) |
| fors_sk_gen | SK.seed | 4 | 68 | 68 | 0 | 513 | 54 | 280 | 1 | yes | PASS (all identical) |
| fors_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 905 | 52 | 790 | 2 | yes | PASS (all identical) |
| fors_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 1737 | 97 | 1360 | 2 | yes | PASS (all identical) |
| fors_node/z=3 | SK.seed | 4 | 68 | 68 | 0 | 5876 | 278 | 3850 | 2 | yes | PASS (all identical) |
| fors_node/z=6 | SK.seed | 4 | 68 | 68 | 0 | 42012 | 1851 | 23852 | 2 | yes | PASS (all identical) |
| fors_node/z=7 | SK.seed | 4 | 68 | 68 | 0 | 82912 | 3622 | 46216 | 2 | yes | PASS (all identical) |
| fors_node/z=8 | SK.seed | 2 | 18 | 18 | 0 | 166310 | 7297 | 92652 | 5 | yes | PASS (all identical) |
| fors_node/z=12 | SK.seed | 2 | 18 | 18 | 0 | 2668250 | 117547 | 1485732 | 95 | yes | PASS (all identical) |
| fors_sign | SK.seed (md public, fixed) | 2 | 18 | 18 | 0 | 37376192 | 1647132 | 20857671 | 1457 | yes | PASS (all identical) |
| fors_pk_gen | SK.seed | 2 | 18 | 18 | 0 | 37357897 | 1646065 | 20801027 | 1344 | yes | PASS (all identical) |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 2 | 26 | 26 | 0 | 39104965 | 764410 | 13815845 | 1535 | yes | PASS (all identical) |
| slh_keygen_internal/all-inputs | SK.seed, SK.prf and PK.seed | 1 | 13 | 13 | 0 | 39104965 | 764410 | 13815845 | 1535 | yes | PASS (all identical) |
| api::keygen | SK.seed and SK.prf (PK.seed fixed) | 2 | 18 | 18 | 0 | 39104989 | 764412 | 13815881 | 1535 | yes | PASS (all identical) |
| wots_pk_from_sig | WOTS+ signature bytes (m public, fixed) | 4 | 36 | 36 | 0 | 42515 | 1525 | 17504 | 10 | yes | PASS (all identical) |
| xmss_pk_from_sig | XMSS signature bytes (m, idx public, fixed) | 4 | 36 | 36 | 0 | 50373 | 2019 | 20594 | 19 | yes | PASS (all identical) |
| fors_pk_from_sig | FORS signature bytes (md public, fixed) | 4 | 36 | 36 | 0 | 50393 | 2755 | 30372 | 19 | yes | PASS (all identical) |
| INFO fors_sign, PUBLIC md varied | public digest md (SK.seed fixed) | 1 | 9 | 9 | 0 | 37376192 | 1647132 | 20857671 | 1457 | yes | info: identical |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 1 | 65 | 35 | 30 | 15 | 2 | 5 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_table (secret-indexed lookup) | secret index (leaky by construction) | 1 | 64 | 0 | 64 | 14 | 1 | 7 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 1 | 65 | 12 | 53 | 2931 | 449 | 1310 | 12 | yes | PASS (control: difference detected) |
| CONTROL wots_sign, PUBLIC m varied | public message m (chain lengths are public) | 2 | 34 | 0 | 34 | 45597 | 1450 | 18862 | 20 | yes | PASS (control: difference detected) |
| CONTROL chain_blocks n=4, PUBLIC end of block 0 varied | public step count of one block (0..255) | 1 | 33 | 0 | 33 | 4832 | 85 | 1751 | 1 | yes | PASS (control: difference detected) |
| CONTROL sha256, PUBLIC length varied | public message length (0..255) | 1 | 33 | 0 | 33 | 1323 | 189 | 606 | 4 | yes | PASS (control: difference detected) |
| PREFIX chain_blocks n=8, PUBLIC: whether block 2 shares the others' 16-byte prefix | one public bit: block 2 starts like the other blocks, or not | 1 | 8 | 0 | 8 | 4560 | 97 | 1974 | 1 | yes | PASS (control: difference detected) |

Divergence details (first differing pair of each row):

- `CONTROL leaky_cmp (early-exit compare of secret)`: first divergence at event #5: last common event: read 0x50007ffefb (size/arg 1) in basic block ct_evidence::w_leaky_cmp+0x0; A: exec block ct_evidence::w_leaky_cmp+0x6c (size/arg 16) in basic block ct_evidence::w_leaky_cmp+0x6c | B: exec block ct_evidence::w_leaky_cmp+0x2c (size/arg 36) in basic block ct_evidence::w_leaky_cmp+0x2c
- `CONTROL leaky_table (secret-indexed lookup)`: first divergence at event #6: last common event: read 0x50007ffef8 (size/arg 8) in basic block ct_evidence::w_leaky_table+0x0; A: read 0x102b75d8c (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0 | B: read 0x102b75cc0 (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0
- `CONTROL leaky_loop (secret-dependent iteration count)`: first divergence at event #12: last common event: write 0x50007ffeb8 (size/arg 8) in basic block ct_evidence::w_leaky_loop+0x0; A: exec block ct_evidence::w_leaky_loop+0x30 (size/arg 28) in basic block ct_evidence::w_leaky_loop+0x30 | B: exec block ct_evidence::w_leaky_loop+0x5c (size/arg 24) in basic block ct_evidence::w_leaky_loop+0x5c
- `CONTROL wots_sign, PUBLIC m varied`: first divergence at event #5277: last common event: read 0x40000000f0 (size/arg 4) in basic block slhdsa::hash::chain_blocks+0x1f4; A: exec block slhdsa::hash::chain_blocks+0x204 (size/arg 40) in basic block slhdsa::hash::chain_blocks+0x204 | B: exec block slhdsa::hash::chain_blocks+0x1e4 (size/arg 16) in basic block slhdsa::hash::chain_blocks+0x1e4
- `CONTROL chain_blocks n=4, PUBLIC end of block 0 varied`: first divergence at event #346: last common event: read 0x50007ffcb0 (size/arg 4) in basic block slhdsa::hash::chain_blocks+0x1f4; A: exec block slhdsa::hash::chain_blocks+0x204 (size/arg 40) in basic block slhdsa::hash::chain_blocks+0x204 | B: exec block slhdsa::hash::chain_blocks+0x1e4 (size/arg 16) in basic block slhdsa::hash::chain_blocks+0x1e4
- `CONTROL sha256, PUBLIC length varied`: first divergence at event #29: last common event: write 0x50007ffe18 (size/arg 8) in basic block slhdsa::sha256::sha256_from+0x0; A: exec block slhdsa::sha256::sha256_from+0x50 (size/arg 20) in basic block slhdsa::sha256::sha256_from+0x50 | B: exec block slhdsa::sha256::sha256_from+0x48 (size/arg 8) in basic block slhdsa::sha256::sha256_from+0x48
- `PREFIX chain_blocks n=8, PUBLIC: whether block 2 shares the others' 16-byte prefix`: first divergence at event #443: last common event: read 0x6000010088 (size/arg 8) in basic block slhdsa::hash::chain_blocks+0x204; A: exec block slhdsa::hash::chain_blocks+0x22c (size/arg 36) in basic block slhdsa::hash::chain_blocks+0x22c | B: exec block slhdsa::hash::chain_blocks+0x194 (size/arg 96) in basic block slhdsa::hash::chain_blocks+0x194

overall: ALL ROWS AS EXPECTED

What this establishes, for the tested inputs and for both builds: the control
flow and the addresses/sizes of all memory accesses of the compiled `sha256`,
`hmac_sha256`, `compress`, `thash_short`, `thash`, `thash_values`, `prf_msg`,
`chain_blocks` (and `chain_blocks_portable`), `wots_pk_gen`, `wots_sign`,
`xmss_node` (z = 0..4), `xmss_sign`, `fors_sk_gen`, `fors_node` (z up to 12,
through both the batched path, z <= 7, and the recursive one), `fors_sign`,
`fors_pk_gen`, the whole `slh_keygen_internal` (which is `xmss_node` at
z = 9) and `api::keygen` did not depend on the secret bytes. For
`chain_blocks` the varied bytes are everything in each 64-byte block except
its first 16 bytes; what was held fixed, and is public in every call the crate
makes, is the number of blocks, the step ranges, and those 16-byte prefixes.
`slh_keygen_internal` was additionally run with PK.seed varied: identical,
i.e. its trace is independent of all three inputs.

The three `*_pk_from_sig` rows vary bytes that are about to be published (the
signature), not secrets: the traces are identical, i.e. the recomputation the
signer runs on its own signature branches only on the public message digits
and indices. The pinned experiment T4 relies on this.

Informational rows (a public input varied, outcome not judged) --
default: `INFO fors_sign, PUBLIC md varied`: identical (9 pairs); `PREFIX chain_blocks n=8, PUBLIC: whether block 2 shares the others' 16-byte prefix`: identical (8 pairs); hw-sha2: `INFO fors_sign, PUBLIC md varied`: identical (9 pairs).
So `fors_sign`'s trace is identical even across different *public* digests in
both builds (the FORS indices flow into address words and single-step ranges
`t..t+1`, never into a branch or an address).

Controls: the checker flags an early-exit comparison (control-flow leak, first
divergence = a different basic block inside `w_leaky_cmp`), a secret-indexed
table lookup (same control flow, different *read address*, i.e. only the
memory hook can see it) and a secret-dependent loop count; and it reports
different traces when a public WOTS+ message, a public step count of
`chain_blocks` or a public message length is changed.

**The hw-sha2 scheduling and its cache.** The two parts of the hw-sha2
`chain_blocks` whose control flow looks data-dependent are driven by public
data only, and the tracer sees both:

* *Slot scheduling* (`chain_all`: which chains occupy the four lanes, for how
  many periods, in which of the 1-, 2-, 3- or 4-lane kernels) is a function of
  the `start`/`end` step ranges. The `chain_blocks` rows with pseudo-random
  ranges (16 + 8 + 8 public configurations, each a different schedule, many
  with empty ranges interleaved) are identical across block contents, and the
  control that changes one step count changes the trace (first divergence in
  `slhdsa::hash::chain_blocks`, at the test `start[next] < end[next]`).
* *The first-rounds cache* (`enter`: rounds 0..3 of the last block entered are
  reused if the next block starts with the same 16 bytes) is a branch on the
  equality of two 16-byte address prefixes. The `PREFIX` row flips one public
  bit, whether block 2 shares the others' prefix: in the hw-sha2 build every
  such pair differs (first divergence in `slhdsa::hash::chain_blocks`, the
  block that recomputes the rounds), in the default build none does. The rows
  with two prefixes and with all-distinct prefixes exercise hits and misses
  in fixed public patterns and are identical across block contents. In the
  crate the prefix is `ADRSc[0..16]` (layer, tree, type, key pair, upper half
  of word 2), which never contains secret data; within one call all blocks
  share it.

### T4. Whole signing with the declassified values pinned (`out/*/trace_sign_*.md`)

One cannot fix the signature and vary the key. The audit's claim is that the
trace of signing is a function of (M, PK.seed, PK.root, signature); more
precisely that secrets reach branches and addresses only through `R`,
`PK_FORS` and the seven XMSS roots (which determine the digest, the indices
and all WOTS+ digits), all of which the verifier recomputes. That claim is
directly testable: run A signs honestly and the tracer records these values
when the calls producing them return; run B has the same M, ctx, PK.seed,
PK.root but fresh SK.seed, SK.prf and addrnd, and the tracer overwrites the
results of the same calls with A's values. All other data in run B (every
FORS secret and node, every WOTS+ secret and chain value, every Merkle node,
the 7840-byte signature body) differ from run A.

The values, and where they are taken (all five functions are out-of-line
symbols in both builds; nothing in the crate was changed and nothing had to be
wrapped):

| value | hook point (result of the call) | per signature | checked signer |
|---|---|---|---|
| `R` | `slhdsa::hash::prf_msg` | 1 | 1 |
| `PK_FORS`, from the FORS signature | `slhdsa::fors::fors_pk_from_sig` | 1 | 1 |
| `PK_FORS`, from the secret seed | `slhdsa::fors::fors_pk_gen` | - | 1 |
| XMSS root of layer j, from the XMSS signature | `slhdsa::xmss::xmss_pk_from_sig` | 7 | 7 |
| XMSS root of layer j < 6, from the secret seed | `slhdsa::xmss::xmss_node` called with i = 0, z = 9 | - | 6 |
| | total | 9 | 16 |

(The 2026-11-20 harness hooked `thash` and picked calls by address type. In
the current crate the roots are no longer results of `thash`, and at the
level of the hash calls the two routes of the checked signer cannot be told
apart, so the hooks are on the functions that return the values. The checked
signer compares its top root with `PK.root` instead of recomputing it, hence
6 second-route roots.)

Sanity checks performed in every configuration (all passed; a failure prints
a `- config` line and makes the generator of this file stop):

* the emulated output of A equals the native signature, and it verifies with
  the crate's `slh_verify_internal`;
* the recorded values are, in order and in kind, exactly the values a
  verifier computes natively from (M', PK, signature of A): `R` read off the
  signature, `PK_FORS = fors_pk_from_sig(..)`, and the chain of
  `xmss_pk_from_sig(..)` roots ending in `PK.root`; the second-route values of
  the checked signer equal the first-route ones. So the pinned values are
  public by construction of the check, not only by the audit's argument, and
  the hook points and the return convention (`[u8; 16]` through the x8 result
  pointer) are confirmed;
* replaying A's values into A leaves trace and output unchanged;
* in B all 9 (16) values are pinned, B returns a signature whose `R` is A's
  and whose body differs from A's (in the checked signer this also means its
  comparisons succeeded on the pinned values);
* without pinning, B's trace differs from A's (the "unpinned control"
  column), so the pinning is what makes them equal.

default build (`slh_sign_internal` and `slh_sign_internal_checked` with
control flow and memory addresses; the six wrappers around them with control
flow only):

| entry point | compared | public configs | values recorded and pinned | pairs (A, B) | pinned: identical | unpinned controls differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| `slh::slh_sign_internal` | control flow + memory addresses | 8 | 9 | 32 | 32 | 16/16 | 6.513e+09 | 1.203e+09 | PASS |
| `slh::slh_sign_internal_checked` | control flow + memory addresses | 8 | 16 | 32 | 32 | 16/16 | 1.217e+10 | 2.250e+09 | PASS |
| `slh::slh_sign` | control flow only | 4 | 9 | 12 | 12 | 8/8 | 6.513e+09 | 2.577e+08 | PASS |
| `slh::slh_sign_checked` | control flow only | 4 | 16 | 12 | 12 | 8/8 | 1.217e+10 | 4.816e+08 | PASS |
| `api::sign` | control flow only | 4 | 9 | 12 | 12 | 8/8 | 6.513e+09 | 2.577e+08 | PASS |
| `api::sign_checked` | control flow only | 4 | 16 | 12 | 12 | 8/8 | 1.217e+10 | 4.816e+08 | PASS |
| `api::sign_deterministic` | control flow only | 4 | 9 | 12 | 12 | 8/8 | 6.513e+09 | 2.577e+08 | PASS |
| `api::sign_deterministic_checked` | control flow only | 4 | 16 | 12 | 12 | 8/8 | 1.217e+10 | 4.816e+08 | PASS |

hw-sha2 build (everything with control flow and memory addresses):

| entry point | compared | public configs | values recorded and pinned | pairs (A, B) | pinned: identical | unpinned controls differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| `slh::slh_sign_internal` | control flow + memory addresses | 16 | 9 | 96 | 96 | 32/32 | 3.112e+08 | 1.247e+08 | PASS |
| `slh::slh_sign_internal_checked` | control flow + memory addresses | 16 | 16 | 96 | 96 | 32/32 | 5.832e+08 | 2.347e+08 | PASS |
| `slh::slh_sign` | control flow + memory addresses | 4 | 9 | 12 | 12 | 8/8 | 3.112e+08 | 1.247e+08 | PASS |
| `slh::slh_sign_checked` | control flow + memory addresses | 4 | 16 | 12 | 12 | 8/8 | 5.832e+08 | 2.347e+08 | PASS |
| `api::sign` | control flow + memory addresses | 4 | 9 | 12 | 12 | 8/8 | 3.112e+08 | 1.247e+08 | PASS |
| `api::sign_checked` | control flow + memory addresses | 4 | 16 | 12 | 12 | 8/8 | 5.832e+08 | 2.347e+08 | PASS |
| `api::sign_deterministic` | control flow + memory addresses | 4 | 9 | 12 | 12 | 8/8 | 3.112e+08 | 1.247e+08 | PASS |
| `api::sign_deterministic_checked` | control flow + memory addresses | 4 | 16 | 12 | 12 | 8/8 | 5.832e+08 | 2.347e+08 | PASS |

Per-configuration tables, default build, `slh_sign_internal`:

| public config (M, PK.seed, key A) | message bytes | values recorded and pinned | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 32 | 9 | 4 | 4 | 0 | 2/2 | 6513219407 | 1203415794 | PASS |
| 1 | 0 | 9 | 4 | 4 | 0 | 2/2 | 6513216244 | 1203415211 | PASS |
| 2 | 100 | 9 | 4 | 4 | 0 | 2/2 | 6513224909 | 1203416738 | PASS |
| 3 | 1 | 9 | 4 | 4 | 0 | 2/2 | 6513217857 | 1203415991 | PASS |
| 4 | 32 | 9 | 4 | 4 | 0 | 2/2 | 6513218689 | 1203415454 | PASS |
| 5 | 0 | 9 | 4 | 4 | 0 | 2/2 | 6513216145 | 1203415175 | PASS |
| 6 | 100 | 9 | 4 | 4 | 0 | 2/2 | 6513225763 | 1203417151 | PASS |
| 7 | 1 | 9 | 4 | 4 | 0 | 2/2 | 6513216012 | 1203415091 | PASS |

default build, `slh_sign_internal_checked`:

| public config (M, PK.seed, key A) | message bytes | values recorded and pinned | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 32 | 16 | 4 | 4 | 0 | 2/2 | 12171176950 | 2250023606 | PASS |
| 1 | 0 | 16 | 4 | 4 | 0 | 2/2 | 12171173787 | 2250023023 | PASS |
| 2 | 100 | 16 | 4 | 4 | 0 | 2/2 | 12171182452 | 2250024550 | PASS |
| 3 | 1 | 16 | 4 | 4 | 0 | 2/2 | 12171175400 | 2250023803 | PASS |
| 4 | 32 | 16 | 4 | 4 | 0 | 2/2 | 12171176232 | 2250023266 | PASS |
| 5 | 0 | 16 | 4 | 4 | 0 | 2/2 | 12171173688 | 2250022987 | PASS |
| 6 | 100 | 16 | 4 | 4 | 0 | 2/2 | 12171183306 | 2250024963 | PASS |
| 7 | 1 | 16 | 4 | 4 | 0 | 2/2 | 12171173555 | 2250022903 | PASS |

hw-sha2 build, `slh_sign_internal`:

| public config (M, PK.seed, key A) | message bytes | values recorded and pinned | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 32 | 9 | 6 | 6 | 0 | 2/2 | 311240556 | 124711643 | PASS |
| 1 | 0 | 9 | 6 | 6 | 0 | 2/2 | 311238566 | 124708864 | PASS |
| 2 | 100 | 9 | 6 | 6 | 0 | 2/2 | 311237841 | 124706508 | PASS |
| 3 | 1 | 9 | 6 | 6 | 0 | 2/2 | 311240433 | 124711091 | PASS |
| 4 | 32 | 9 | 6 | 6 | 0 | 2/2 | 311237181 | 124706208 | PASS |
| 5 | 0 | 9 | 6 | 6 | 0 | 2/2 | 311238080 | 124707923 | PASS |
| 6 | 100 | 9 | 6 | 6 | 0 | 2/2 | 311240878 | 124711006 | PASS |
| 7 | 1 | 9 | 6 | 6 | 0 | 2/2 | 311238559 | 124708719 | PASS |
| 8 | 32 | 9 | 6 | 6 | 0 | 2/2 | 311237892 | 124707815 | PASS |
| 9 | 0 | 9 | 6 | 6 | 0 | 2/2 | 311240540 | 124711855 | PASS |
| 10 | 100 | 9 | 6 | 6 | 0 | 2/2 | 311240862 | 124711010 | PASS |
| 11 | 1 | 9 | 6 | 6 | 0 | 2/2 | 311238356 | 124708402 | PASS |
| 12 | 32 | 9 | 6 | 6 | 0 | 2/2 | 311238044 | 124708162 | PASS |
| 13 | 0 | 9 | 6 | 6 | 0 | 2/2 | 311237646 | 124707321 | PASS |
| 14 | 100 | 9 | 6 | 6 | 0 | 2/2 | 311239094 | 124708566 | PASS |
| 15 | 1 | 9 | 6 | 6 | 0 | 2/2 | 311238887 | 124709271 | PASS |

hw-sha2 build, `slh_sign_internal_checked`:

| public config (M, PK.seed, key A) | message bytes | values recorded and pinned | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 32 | 16 | 6 | 6 | 0 | 2/2 | 583225622 | 234665948 | PASS |
| 1 | 0 | 16 | 6 | 6 | 0 | 2/2 | 583223632 | 234663169 | PASS |
| 2 | 100 | 16 | 6 | 6 | 0 | 2/2 | 583222907 | 234660813 | PASS |
| 3 | 1 | 16 | 6 | 6 | 0 | 2/2 | 583225499 | 234665396 | PASS |
| 4 | 32 | 16 | 6 | 6 | 0 | 2/2 | 583222247 | 234660513 | PASS |
| 5 | 0 | 16 | 6 | 6 | 0 | 2/2 | 583223146 | 234662228 | PASS |
| 6 | 100 | 16 | 6 | 6 | 0 | 2/2 | 583225944 | 234665311 | PASS |
| 7 | 1 | 16 | 6 | 6 | 0 | 2/2 | 583223625 | 234663024 | PASS |
| 8 | 32 | 16 | 6 | 6 | 0 | 2/2 | 583222958 | 234662120 | PASS |
| 9 | 0 | 16 | 6 | 6 | 0 | 2/2 | 583225606 | 234666160 | PASS |
| 10 | 100 | 16 | 6 | 6 | 0 | 2/2 | 583225928 | 234665315 | PASS |
| 11 | 1 | 16 | 6 | 6 | 0 | 2/2 | 583223422 | 234662707 | PASS |
| 12 | 32 | 16 | 6 | 6 | 0 | 2/2 | 583223110 | 234662467 | PASS |
| 13 | 0 | 16 | 6 | 6 | 0 | 2/2 | 583222712 | 234661626 | PASS |
| 14 | 100 | 16 | 6 | 6 | 0 | 2/2 | 583224160 | 234662871 | PASS |
| 15 | 1 | 16 | 6 | 6 | 0 | 2/2 | 583223953 | 234663576 | PASS |

(The per-configuration tables of the six other entry points are in
`out/*/trace_sign_{slh,slh-checked,api,api-checked,api-det,api-det-checked}.md`.
Message lengths 32, 0, 100 and 1 bytes rotate over the configurations; the
entry points with a context use a 17-byte context; in the deterministic
entry points `addrnd` is PK.seed, so only SK.seed and SK.prf are varied.)

What this establishes: for 136 (default) and
264 (hw-sha2) pairs of unrelated secret sets, once the
public intermediate values are equal, the entire execution
(6.51e+09 instructions per signature in the default
build, 1.22e+10 checked;
3.11e+08 and 5.83e+08 in
the hw-sha2 build) is identical in control flow and, where memory was traced,
in every memory address, allocation size and copy length. This includes, in
the hw-sha2 build, the lane scheduling of every one of the ~11600 (checked:
~21800) `chain_blocks` calls of a signature and every hit and miss of the
first-rounds cache. What it does not establish: anything about inputs not
sampled. In run B the key is not a valid key pair (PK.root is A's) and the
output is not a valid signature; that is irrelevant to the property tested,
which is about which data the trace depends on.

The checked signer adds, on top of plain signing, two more computations from
the secret seed (`fors_pk_gen`, a T1 row, and six `xmss_node` at z = 9, which
is what the T1 row `slh_keygen_internal` runs) and eight 16-byte comparisons,
which the compiler emitted
branch-free (`cmp`/`ccmp`/`cset`, `eor`/`orr`/`csel`: see section 2); their
outcome is a public bit in an honest run and only decides, at the very end,
whether the signature is returned.

### T5. Unconditioned profile of whole signing (`out/*/trace_sign_profile_*.md`)

default build, `slh_sign_internal`:

- runs: 24 (run 0 = base key, others = fresh honest (SK.seed, SK.prf, addrnd), PK.seed and M fixed); failed runs: 0; every run returned a signature equal to the native one: yes
- distinct full control-flow traces: 24 (expected: all distinct, the public transcript differs)
- distinct executed-instruction counts: 24 (min 6513217366, max 6513220818, spread 3452)
- distinct basic-block counts: 18
- distinct call-out (malloc/realloc/free/memcpy/memset) counts: [12456]
- executed SHA-256 instructions, distinct values: SHA256H [0], SHA256H2 [0], SHA256SU0 [0], SHA256SU1 [0]
- calls of the crate's out-of-line functions, same number in every run: `fors::fors_batch` 532, `fors::fors_node` 896, `fors::fors_pk_from_sig` 1, `fors::fors_sign` 1, `hash::chain_blocks_portable` 11584, `hash::h_msg` 1, `hash::prf_msg` 1, `hash::thash` 1, `hash::thash_short` 3955, `hash::thash_values` 3584, `ht::ht_sign` 1, `sha256::schedule` 39808, `sha256::sha256_from` 5, `slh::slh_sign_internal` 1, `util::base_2b` 30, `wots::sk_blocks` 3584, `wots::wots_digits` 14, `wots::wots_pk_from_sig` 7, `wots::wots_pk_gen` 3570, `wots::wots_sign` 7, `xmss::xmss_node` 7084, `xmss::xmss_pk_from_sig` 7, `xmss::xmss_sign` 7
- calls of the crate's out-of-line functions, number varies between runs: none
- distinct block-execution histograms (multiset of executed blocks, order ignored): 24

default build, `slh_sign_internal_checked`:

- runs: 24 (run 0 = base key, others = fresh honest (SK.seed, SK.prf, addrnd), PK.seed and M fixed); failed runs: 0; every run returned a signature equal to the native one: yes
- distinct full control-flow traces: 24 (expected: all distinct, the public transcript differs)
- distinct executed-instruction counts: 24 (min 12171174909, max 12171178361, spread 3452)
- distinct basic-block counts: 18
- distinct call-out (malloc/realloc/free/memcpy/memset) counts: [23010]
- executed SHA-256 instructions, distinct values: SHA256H [0], SHA256H2 [0], SHA256SU0 [0], SHA256SU1 [0]
- calls of the crate's out-of-line functions, same number in every run: `fors::fors_batch` 980, `fors::fors_node` 1778, `fors::fors_pk_from_sig` 1, `fors::fors_pk_gen` 1, `fors::fors_sign` 1, `hash::chain_blocks_portable` 21760, `hash::h_msg` 1, `hash::prf_msg` 1, `hash::thash` 2, `hash::thash_short` 7455, `hash::thash_values` 6656, `ht::ht_sign_checked` 1, `sha256::schedule` 74032, `sha256::sha256_from` 6, `slh::slh_sign_internal_checked` 1, `util::base_2b` 30, `wots::sk_blocks` 6656, `wots::wots_digits` 14, `wots::wots_pk_from_sig` 7, `wots::wots_pk_gen` 6642, `wots::wots_sign` 7, `xmss::xmss_node` 13222, `xmss::xmss_pk_from_sig` 7, `xmss::xmss_sign` 7
- calls of the crate's out-of-line functions, number varies between runs: none
- distinct block-execution histograms (multiset of executed blocks, order ignored): 24

hw-sha2 build, `slh_sign_internal`:

- runs: 24 (run 0 = base key, others = fresh honest (SK.seed, SK.prf, addrnd), PK.seed and M fixed); failed runs: 0; every run returned a signature equal to the native one: yes
- distinct full control-flow traces: 24 (expected: all distinct, the public transcript differs)
- distinct executed-instruction counts: 24 (min 311236600, max 311240437, spread 3837)
- distinct basic-block counts: 23
- distinct call-out (malloc/realloc/free/memcpy/memset) counts: [12456]
- executed SHA-256 instructions, distinct values: SHA256H [33328712], SHA256H2 [31150032], SHA256SU0 [26621856], SHA256SU1 [26621856]
- calls of the crate's out-of-line functions, same number in every run: `fors::fors_batch` 532, `fors::fors_node` 896, `fors::fors_pk_from_sig` 1, `fors::fors_sign` 1, `hash::chain_blocks` 11584, `hash::h_msg` 1, `hash::prf_msg` 1, `hash::thash` 1, `hash::thash_short` 3955, `hash::thash_values` 3584, `ht::ht_sign` 1, `sha256::sha256_from` 5, `slh::slh_sign_internal` 1, `util::base_2b` 30, `wots::sk_blocks` 3584, `wots::wots_digits` 14, `wots::wots_pk_from_sig` 7, `wots::wots_pk_gen` 3570, `wots::wots_sign` 7, `xmss::xmss_node` 7084, `xmss::xmss_pk_from_sig` 7, `xmss::xmss_sign` 7
- calls of the crate's out-of-line functions, number varies between runs: none
- distinct block-execution histograms (multiset of executed blocks, order ignored): 24

hw-sha2 build, `slh_sign_internal_checked`:

- runs: 24 (run 0 = base key, others = fresh honest (SK.seed, SK.prf, addrnd), PK.seed and M fixed); failed runs: 0; every run returned a signature equal to the native one: yes
- distinct full control-flow traces: 24 (expected: all distinct, the public transcript differs)
- distinct executed-instruction counts: 24 (min 583221666, max 583225503, spread 3837)
- distinct basic-block counts: 23
- distinct call-out (malloc/realloc/free/memcpy/memset) counts: [23010]
- executed SHA-256 instructions, distinct values: SHA256H [62265032], SHA256H2 [58194448], SHA256SU0 [49735392], SHA256SU1 [49735392]
- calls of the crate's out-of-line functions, same number in every run: `fors::fors_batch` 980, `fors::fors_node` 1778, `fors::fors_pk_from_sig` 1, `fors::fors_pk_gen` 1, `fors::fors_sign` 1, `hash::chain_blocks` 21760, `hash::h_msg` 1, `hash::prf_msg` 1, `hash::thash` 2, `hash::thash_short` 7455, `hash::thash_values` 6656, `ht::ht_sign_checked` 1, `sha256::sha256_from` 6, `slh::slh_sign_internal_checked` 1, `util::base_2b` 30, `wots::sk_blocks` 6656, `wots::wots_digits` 14, `wots::wots_pk_from_sig` 7, `wots::wots_pk_gen` 6642, `wots::wots_sign` 7, `xmss::xmss_node` 13222, `xmss::xmss_pk_from_sig` 7, `xmss::xmss_sign` 7
- calls of the crate's out-of-line functions, number varies between runs: none
- distinct block-execution histograms (multiset of executed blocks, order ignored): 24

So over random honest keys the *amount* of work is essentially constant:
every signature makes exactly the same number of calls of every function of
the crate and of the allocator, and in the hw-sha2 build executes exactly the
same number of SHA-256 instructions. The instruction count varies by a few
thousand (out of 6.5e9, resp. 3e8) with the public transcript, presumably
from public-data-dependent paths such as the left/right choice when climbing
authentication paths, how the 15 steps per WOTS+ chain are split between
signing and public-key recomputation, and in the hw-sha2 build which lane
kernels run; this was not broken down further. The *order* of work differs
with the public transcript. That the amount of work is
this constant is what makes a total-time measurement of signing (section 3,
D3) meaningful at all.

## 2. Static facts about the native code (`out/*/disasm.md`)

### default build

#### Static summary of slhdsa functions in target/release/cttrace

| function | insns | conditional branches | indirect br/blr | udiv/sdiv | crypto-ext insns | SIMD/FP-register insns | csel-family |
|---|---|---|---|---|---|---|---|
| `<instantiation in slhdsa> do_reserve_and_handle::alloc::Global` | 34 | 2 | 0 | 0 | 0 | 0 | 3 |
| `<instantiation in slhdsa> raw_vec::Raw::finish_grow` | 44 | 5 | 0 | 0 | 0 | 0 | 1 |
| `<instantiation in slhdsa> raw_vec::Raw::grow_one` | 25 | 1 | 0 | 0 | 0 | 0 | 1 |
| `slhdsa::api::keygen` | 24 | 0 | 0 | 0 | 0 | 8 | 0 |
| `slhdsa::api::sign` | 47 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::api::sign_checked` | 43 | 3 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::api::sign_deterministic` | 46 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::api::sign_deterministic_checked` | 42 | 3 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::fors::fors_batch` | 335 | 10 | 0 | 0 | 0 | 107 | 0 |
| `slhdsa::fors::fors_node` | 64 | 1 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::fors::fors_pk_from_sig` | 608 | 24 | 0 | 0 | 0 | 128 | 0 |
| `slhdsa::fors::fors_pk_gen` | 85 | 4 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::fors::fors_sign` | 151 | 9 | 0 | 0 | 0 | 13 | 0 |
| `slhdsa::fors::fors_sk_gen` | 21 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::hash::chain_blocks` | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::hash::chain_blocks_portable` | 300 | 8 | 0 | 0 | 0 | 70 | 1 |
| `slhdsa::hash::h_msg` | 292 | 13 | 0 | 0 | 0 | 22 | 0 |
| `slhdsa::hash::prf_msg` | 271 | 6 | 0 | 0 | 0 | 13 | 0 |
| `slhdsa::hash::seed_ctx` | 111 | 1 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::hash::thash` | 121 | 4 | 0 | 0 | 0 | 16 | 0 |
| `slhdsa::hash::thash_short` | 173 | 3 | 0 | 0 | 0 | 20 | 0 |
| `slhdsa::hash::thash_values` | 297 | 2 | 0 | 0 | 0 | 85 | 0 |
| `slhdsa::ht::ht_sign` | 100 | 6 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::ht::ht_sign_checked` | 129 | 7 | 0 | 0 | 0 | 9 | 3 |
| `slhdsa::ht::ht_verify` | 201 | 7 | 0 | 0 | 0 | 14 | 2 |
| `slhdsa::sha256::hmac_sha256` | 142 | 13 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::sha256::schedule` | 144 | 8 | 0 | 0 | 0 | 33 | 9 |
| `slhdsa::sha256::sha256` | 6 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::sha256::sha256_from` | 402 | 23 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::slh::slh_keygen_internal` | 135 | 1 | 0 | 0 | 0 | 16 | 0 |
| `slhdsa::slh::slh_sign` | 47 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::slh::slh_sign_checked` | 43 | 3 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::slh::slh_sign_internal` | 267 | 13 | 0 | 0 | 0 | 12 | 0 |
| `slhdsa::slh::slh_sign_internal_checked` | 280 | 15 | 0 | 0 | 0 | 12 | 0 |
| `slhdsa::slh::slh_verify_internal` | 163 | 2 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::slh::with_context` | 86 | 6 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::util::base_2b` | 87 | 8 | 0 | 0 | 0 | 2 | 1 |
| `slhdsa::wots::sk_blocks` | 124 | 1 | 0 | 0 | 0 | 23 | 0 |
| `slhdsa::wots::wots_digits` | 141 | 8 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::wots::wots_pk_from_sig` | 142 | 4 | 0 | 0 | 0 | 29 | 0 |
| `slhdsa::wots::wots_pk_gen` | 42 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::wots::wots_sign` | 89 | 5 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::xmss::xmss_node` | 58 | 1 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::xmss::xmss_pk_from_sig` | 81 | 3 | 0 | 0 | 0 | 9 | 1 |
| `slhdsa::xmss::xmss_sign` | 286 | 10 | 0 | 0 | 0 | 24 | 0 |
| **total (45 functions)** | 6330 | 252 | 0 | 0 | 0 | 703 | 22 |

Crypto-extension instructions in slhdsa code (mnemonic: count): none

Other SIMD/FP-register instructions in slhdsa code (mnemonic: count): str: 189, ldr: 161, stp: 57, ldur: 50, stur: 44, mov.b: 24, movi.2d: 14, ushl.2d: 14, ldp: 12, shl.4s: 12, orr.16b: 12, mov.s: 10, ushl.4s: 10, dup.4s: 8, mov: 8, ushll.4s: 8, tbl.16b: 8, uzp1.8h: 7, xtn.8b: 7, uzp1.8b: 7, uzp1.4s: 6, and.16b: 6, dup.2d: 4, umov.b: 4, xtn.4h: 4, zip1.4s: 4, xtn.2s: 2, mov.d: 2, zip1.8b: 2, movi.16b: 2, eor.16b: 2, rev64.4s: 1, trn2.4s: 1, ld4.8b: 1

Call sites in slhdsa code whose target is outside the crate (target: sites): `rust_dealloc`: 61, `__Unwind_Resume`: 27, `_memcpy`: 16, `grow_oneB7_`: 14, `panic_bounds_check`: 11, `slice_index_fail`: 11, `_bzero`: 5, `handle_error`: 3, `rust_alloc`: 1, `rust_no_alloc_shim_is_unstable_v2`: 1, `rust_realloc`: 1

Calls of `memcmp`/`bcmp` from slhdsa code: 0.

##### Conditional branches in `slhdsa::sha256::schedule` (144 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.hs` | `cmp R, R` | forward | 4 |
| `b.lo` | `adds R, R, #0x1` | backward (loop) | 1 |
| `b.lo` | `cmp R, #0x8` | forward | 1 |
| `b.ne` | `adds R, R, #0x8` | backward (loop) | 1 |
| `b.ne` | `subs R, R, #0x1` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::sha256::schedule` (base + index register):

- `ldr w14, [x12, x11]` x1
- `str w14, [x13, x11]` x1

##### Conditional branches in `slhdsa::sha256::sha256_from` (402 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.ne` | `cmp R, R` | forward | 9 |
| `cbz` | `cbz R` | forward | 3 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 2 |
| `b.eq` | `cmp R, #0x38` | forward | 1 |
| `b.eq` | `cmp R, R` | backward (loop) | 1 |
| `b.eq` | `cmp R, R` | forward | 1 |
| `b.hs` | `cmp R, #0x40` | forward | 1 |
| `b.lo` | `cmp R, R` | backward (loop) | 1 |
| `b.ls` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `cmp R, #0x38` | forward | 1 |
| `b.ne` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `subs R, R, R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::sha256::sha256_from` (base + index register):

- `strb w8, [x9, x22]` x6
- `ldr w2, [x23, x12]` x2
- `ldr w1, [x22, x12]` x1
- `strb w8, [x24, x22]` x1
- `strb w8, [x9, x24]` x1
- `strb w9, [x8, x24]` x1
- `ldr w1, [x24, x12]` x1

##### Conditional branches in `slhdsa::hash::chain_blocks` (1 instructions, 0 crypto-extension)

(a tail jump to `slhdsa::hash::chain_blocks_portable`)

##### Conditional branches in `slhdsa::hash::chain_blocks_portable` (300 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, R` | forward | 3 |
| `b.hs` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 1 |
| `b.ne` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `subs R, R, #0x1` | backward (loop) | 1 |
| `cbz` | `cbz R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::hash::chain_blocks_portable` (base + index register):

- `ldr w20, [x3, x13, lsl #2]` x1
- `ldr w8, [x5, x13, lsl #2]` x1
- `ldr w22, [x17, x13]` x1
- `ldr w24, [x15, x13]` x1

##### Conditional branches in `slhdsa::hash::thash_short` (173 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, #0x2a` | forward | 1 |
| `b.hs` | `cmp R, #0x2b` | forward | 1 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::thash_short` (base + index register):

- `strb w8, [x23, x22]` x1
- `ldr w6, [x15, x12]` x1
- `ldr w7, [x23, x12]` x1

##### Conditional branches in `slhdsa::hash::thash_values` (297 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.lo` | `cmp R, #0x240` | backward (loop) | 1 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::thash_values` (base + index register):

- `ldr w2, [x28, x12]` x1
- `ldr w1, [x27, x12]` x1

##### Conditional branches in `slhdsa::hash::seed_ctx` (111 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.ne` | `cmp R, #0x100` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::seed_ctx` (base + index register):

- `ldr w3, [x14, x12]` x1
- `ldr w2, [x21, x12]` x1

##### Conditional branches in `slhdsa::hash::prf_msg` (271 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `cbz` | `cbz R` | forward | 3 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 2 |
| `b.hi` | `cmp R, R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::hash::prf_msg` (base + index register):

- `str q0, [x20, x8]` x1
- `ldr w2, [x22, x8]` x1
- `ldr w1, [x23, x8]` x1
- `ldr w2, [x22, x12]` x1
- `ldr w1, [x21, x12]` x1

#### Object-code comparison of slhdsa

- A: `target/release/build/slhdsa/71d522cffa462b8f/out/libslhdsa-71d522cffa462b8f.rlib`
- B: `target/parent/release/build/slhdsa/b5f420dc9e5ca955/out/libslhdsa-b5f420dc9e5ca955.rlib`

Constant-data sections of the object files (`__const`, `__literal*`, `__cstring`; unlinked, so independent of addresses):

- `__TEXT,__literal16`: 384 bytes, identical
- `__TEXT,__cstring`: 6 strings, the source-file paths of the panic locations; identical except that A has them absolute and B relative to the crate directory (44 bytes longer each)
- `__DATA,__const`: 336 bytes, identical except 14 8-byte fields that are larger in A by exactly 44: the lengths of those path strings in the panic-location records
- `__TEXT,__const`: 708 bytes, identical

constant data: same numeric constants and tables in A and B.

51 functions identical instruction-for-instruction (incl. relocation targets), 0 different, 0 present in only one; 6991 disassembly lines (instructions + relocation records) compared in A; 0 code ranges left unnamed.

### hw-sha2 build

#### Static summary of slhdsa functions in target-hw/release/cttrace

| function | insns | conditional branches | indirect br/blr | udiv/sdiv | crypto-ext insns | SIMD/FP-register insns | csel-family |
|---|---|---|---|---|---|---|---|
| `<instantiation in slhdsa> do_reserve_and_handle::alloc::Global` | 34 | 2 | 0 | 0 | 0 | 0 | 3 |
| `<instantiation in slhdsa> raw_vec::Raw::finish_grow` | 44 | 5 | 0 | 0 | 0 | 0 | 1 |
| `<instantiation in slhdsa> raw_vec::Raw::grow_one` | 25 | 1 | 0 | 0 | 0 | 0 | 1 |
| `slhdsa::api::keygen` | 24 | 0 | 0 | 0 | 0 | 8 | 0 |
| `slhdsa::api::sign` | 47 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::api::sign_checked` | 43 | 3 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::api::sign_deterministic` | 48 | 3 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::api::sign_deterministic_checked` | 44 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::fors::fors_batch` | 350 | 10 | 0 | 0 | 0 | 108 | 0 |
| `slhdsa::fors::fors_node` | 64 | 1 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::fors::fors_pk_from_sig` | 600 | 24 | 0 | 0 | 0 | 127 | 0 |
| `slhdsa::fors::fors_pk_gen` | 79 | 4 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::fors::fors_sign` | 144 | 9 | 0 | 0 | 0 | 13 | 0 |
| `slhdsa::fors::fors_sk_gen` | 21 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::hash::chain_blocks` | 2704 | 33 | 0 | 0 | 1062 | 2460 | 8 |
| `slhdsa::hash::chain_blocks_portable` | 84 | 8 | 0 | 0 | 4 | 29 | 1 |
| `slhdsa::hash::h_msg` | 247 | 14 | 0 | 0 | 4 | 48 | 0 |
| `slhdsa::hash::prf_msg` | 180 | 8 | 0 | 0 | 8 | 66 | 0 |
| `slhdsa::hash::seed_ctx` | 49 | 2 | 0 | 0 | 4 | 28 | 0 |
| `slhdsa::hash::thash` | 121 | 4 | 0 | 0 | 0 | 16 | 0 |
| `slhdsa::hash::thash_short` | 144 | 4 | 0 | 0 | 4 | 43 | 0 |
| `slhdsa::hash::thash_values` | 240 | 3 | 0 | 0 | 4 | 114 | 0 |
| `slhdsa::ht::ht_sign` | 100 | 6 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::ht::ht_sign_checked` | 129 | 7 | 0 | 0 | 0 | 9 | 3 |
| `slhdsa::ht::ht_verify` | 201 | 7 | 0 | 0 | 0 | 14 | 2 |
| `slhdsa::sha256::hmac_sha256` | 142 | 13 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::sha256::sha256` | 6 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::sha256::sha256_from` | 308 | 27 | 0 | 0 | 8 | 63 | 0 |
| `slhdsa::slh::slh_keygen_internal` | 85 | 2 | 0 | 0 | 4 | 38 | 0 |
| `slhdsa::slh::slh_sign` | 47 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::slh::slh_sign_checked` | 43 | 3 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::slh::slh_sign_internal` | 219 | 14 | 0 | 0 | 4 | 36 | 0 |
| `slhdsa::slh::slh_sign_internal_checked` | 234 | 16 | 0 | 0 | 4 | 36 | 0 |
| `slhdsa::slh::slh_verify_internal` | 114 | 3 | 0 | 0 | 4 | 32 | 0 |
| `slhdsa::slh::with_context` | 86 | 6 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::util::base_2b` | 87 | 8 | 0 | 0 | 0 | 2 | 1 |
| `slhdsa::wots::sk_blocks` | 124 | 1 | 0 | 0 | 0 | 23 | 0 |
| `slhdsa::wots::wots_digits` | 141 | 8 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::wots::wots_pk_from_sig` | 135 | 4 | 0 | 0 | 0 | 29 | 0 |
| `slhdsa::wots::wots_pk_gen` | 42 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::wots::wots_sign` | 84 | 5 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::xmss::xmss_node` | 58 | 1 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::xmss::xmss_pk_from_sig` | 81 | 3 | 0 | 0 | 0 | 9 | 1 |
| `slhdsa::xmss::xmss_sign` | 286 | 10 | 0 | 0 | 0 | 24 | 0 |
| **total (44 functions)** | 8088 | 291 | 0 | 0 | 1114 | 3405 | 21 |

Crypto-extension instructions in slhdsa code (mnemonic: count): sha256h.4s: 314, sha256h2.4s: 294, sha256su0.4s: 253, sha256su1.4s: 253

Other SIMD/FP-register instructions in slhdsa code (mnemonic: count): ldr: 458, mov.16b: 397, add.4s: 348, str: 271, stp: 117, ldp: 113, orr.16b: 100, ext.16b: 80, ldur: 52, stur: 51, rev32.16b: 45, mov.s: 30, movi.2d: 22, fmov: 21, ushr.4s: 20, shl.4s: 20, ushr.2s: 20, shl.2s: 20, dup.2s: 14, ushl.2d: 14, ushl.4s: 10, dup.4s: 8, uzp1.8h: 7, xtn.8b: 7, uzp1.8b: 7, uzp1.4s: 6, zip1.4s: 4, dup.2d: 4, umov.b: 4, xtn.4h: 4, movi.16b: 4, mov.d: 3, and.16b: 2, xtn.2s: 2, zip1.8b: 2, eor.16b: 2, rev64.4s: 1, trn2.4s: 1

Call sites in slhdsa code whose target is outside the crate (target: sites): `rust_dealloc`: 61, `__Unwind_Resume`: 27, `_memcpy`: 16, `grow_oneB7_`: 14, `slice_index_fail`: 13, `panic_bounds_check`: 8, `_bzero`: 5, `handle_error`: 3, `rust_alloc`: 1, `rust_no_alloc_shim_is_unstable_v2`: 1, `rust_realloc`: 1

Calls of `memcmp`/`bcmp` from slhdsa code: 0.

##### `slhdsa::sha256::schedule`: no out-of-line copy in this binary

##### Conditional branches in `slhdsa::sha256::sha256_from` (308 instructions, 8 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.ne` | `cmp R, R` | forward | 9 |
| `cbz` | `cbz R` | forward | 3 |
| `b.eq` | `cmp R, #0x10` | backward (loop) | 2 |
| `b.hi` | `cmp R, R` | forward | 2 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 2 |
| `b.eq` | `cmp R, #0x38` | forward | 1 |
| `b.eq` | `cmp R, R` | backward (loop) | 1 |
| `b.eq` | `cmp R, R` | forward | 1 |
| `b.hs` | `cmp R, #0x40` | forward | 1 |
| `b.hs` | `cmp R, R` | forward | 1 |
| `b.lo` | `cmp R, R` | forward | 1 |
| `b.ne` | `cmp R, #0x38` | forward | 1 |
| `b.ne` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `subs R, R, R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::sha256::sha256_from` (base + index register):

- `strb w8, [x9, x21]` x6
- `ldr q3, [x25, x9, lsl #4]` x2
- `ldr q2, [x8, x11, lsl #4]` x2
- `ldr q3, [x8, x12, lsl #4]` x2
- `ldr q3, [x8, x13, lsl #4]` x2
- `ldr q5, [x8, x12, lsl #4]` x2
- `str q4, [x8, x11, lsl #4]` x2
- `strb w8, [x26, x23]` x1
- `strb w8, [x9, x24]` x1
- `strb w20, [x8, x21]` x1

##### Conditional branches in `slhdsa::hash::chain_blocks` (2704 instructions, 1062 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.hs` | `cmp R, R` | forward | 8 |
| `b.lo` | `cmp R, #0x2` | forward | 4 |
| `b.ne` | `subs R, R, #0x1` | backward (loop) | 3 |
| `b.eq` | `cmp R, #0x2` | backward (loop) | 2 |
| `b.eq` | `cmp R, #0x3` | backward (loop) | 2 |
| `b.hs` | `cmp R, R` | backward (loop) | 2 |
| `b.eq` | `cmp R, #0x1` | backward (loop) | 1 |
| `b.hs` | `cmp R, R ; ccmp R, #0x4, #0x2, lo` | forward | 1 |
| `b.lo` | `cmp R, R` | backward (loop) | 1 |
| `b.lo` | `cmp R, R` | forward | 1 |
| `b.lo` | `cmp R, R ; ccmp R, #0x4, #0x2, lo` | backward (loop) | 1 |
| `b.lo` | `cmp R, R ; ccmp R, R, #0x0, hs` | forward | 1 |
| `b.ne` | `cmp R, #0x1` | forward | 1 |
| `b.ne` | `cmp R, #0x2` | forward | 1 |
| `b.ne` | `cmp R, #0x3` | forward | 1 |
| `b.ne` | `cmp R, R` | backward (loop) | 1 |
| `cbz` | `cbz R` | forward | 1 |
| `tbnz` | `tbnz R, #0x0` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::chain_blocks` (base + index register):

- `ldr w15, [x3, x8, lsl #2]` x1
- `ldr w16, [x5, x8, lsl #2]` x1

##### Conditional branches in `slhdsa::hash::chain_blocks_portable` (84 instructions, 4 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, R` | forward | 3 |
| `b.eq` | `cmp R, #0x10` | backward (loop) | 1 |
| `b.eq` | `cmp R, R` | backward (loop) | 1 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 1 |
| `b.hs` | `cmp R, R` | backward (loop) | 1 |
| `cbz` | `cbz R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::hash::chain_blocks_portable` (base + index register):

- `ldr w11, [x3, x8, lsl #2]` x1
- `ldr w12, [x5, x8, lsl #2]` x1
- `ldr q7, [x10, x14, lsl #4]` x1
- `ldr q6, [x9, x16, lsl #4]` x1
- `ldr q7, [x9, x17, lsl #4]` x1
- `ldr q7, [x9, x0, lsl #4]` x1
- `ldr q17, [x9, x17, lsl #4]` x1
- `str q16, [x9, x16, lsl #4]` x1

##### Conditional branches in `slhdsa::hash::thash_short` (144 instructions, 4 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, #0x10` | forward | 1 |
| `b.eq` | `cmp R, #0x2a` | forward | 1 |
| `b.hs` | `cmp R, #0x2b` | forward | 1 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::thash_short` (base + index register):

- `strb w9, [x23, x22]` x1
- `ldr q4, [x9, x8, lsl #4]` x1
- `ldr q3, [x23, x11, lsl #4]` x1
- `ldr q4, [x23, x12, lsl #4]` x1
- `ldr q4, [x23, x13, lsl #4]` x1
- `ldr q6, [x23, x12, lsl #4]` x1
- `str q5, [x23, x11, lsl #4]` x1

##### Conditional branches in `slhdsa::hash::thash_values` (240 instructions, 4 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, #0x10` | backward (loop) | 1 |
| `b.hs` | `cmp R, #0x240` | forward | 1 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::thash_values` (base + index register):

- `ldr q5, [x12, x13, lsl #4]` x1
- `ldr q4, [x11, x15, lsl #4]` x1
- `ldr q5, [x11, x16, lsl #4]` x1
- `ldr q5, [x11, x17, lsl #4]` x1
- `ldr q7, [x11, x16, lsl #4]` x1
- `str q6, [x11, x15, lsl #4]` x1

##### Conditional branches in `slhdsa::hash::seed_ctx` (49 instructions, 4 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, #0x10` | forward | 1 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::seed_ctx` (base + index register):

- `ldr q3, [x13, x11, lsl #4]` x1
- `ldr q2, [x12, x15, lsl #4]` x1
- `ldr q3, [x12, x16, lsl #4]` x1
- `ldr q3, [x12, x17, lsl #4]` x1
- `ldr q5, [x12, x16, lsl #4]` x1
- `str q4, [x12, x15, lsl #4]` x1

##### Conditional branches in `slhdsa::hash::prf_msg` (180 instructions, 8 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `cbz` | `cbz R` | forward | 3 |
| `b.eq` | `cmp R, #0x10` | forward | 2 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 2 |
| `b.hi` | `cmp R, R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::hash::prf_msg` (base + index register):

- `str q0, [x20, x8]` x1
- `ldr q3, [x23, x8, lsl #4]` x1
- `ldr q2, [x9, x11, lsl #4]` x1
- `ldr q3, [x9, x12, lsl #4]` x1
- `ldr q3, [x9, x13, lsl #4]` x1
- `ldr q5, [x9, x12, lsl #4]` x1
- `str q4, [x9, x11, lsl #4]` x1
- `ldr q1, [x23, x9, lsl #4]` x1
- `ldr q0, [x8, x11, lsl #4]` x1
- `ldr q1, [x8, x12, lsl #4]` x1
- `ldr q1, [x8, x13, lsl #4]` x1
- `ldr q3, [x8, x12, lsl #4]` x1
- `str q2, [x8, x11, lsl #4]` x1

#### Object-code comparison of slhdsa

- A: `target-hw/release/build/slhdsa/c23c362924e7fb82/out/libslhdsa-c23c362924e7fb82.rlib`
- B: `target-hw/parent/release/build/slhdsa/892bdcef6834ff45/out/libslhdsa-892bdcef6834ff45.rlib`

Constant-data sections of the object files (`__const`, `__literal*`, `__cstring`; unlinked, so independent of addresses):

- `__TEXT,__literal16`: 432 bytes, identical
- `__TEXT,__const`: 256 bytes, identical
- `__TEXT,__cstring`: 2 strings, the source-file paths of the panic locations; identical except that A has them absolute and B relative to the crate directory (44 bytes longer each)
- `__DATA,__const`: 168 bytes, identical except 7 8-byte fields that are larger in A by exactly 44: the lengths of those path strings in the panic-location records
- `__TEXT,__literal16`: 464 bytes, identical
- `__TEXT,__cstring`: 5 strings, the source-file paths of the panic locations; identical except that A has them absolute and B relative to the crate directory (44 bytes longer each)
- `__DATA,__const`: 288 bytes, identical except 12 8-byte fields that are larger in A by exactly 44: the lengths of those path strings in the panic-location records
- `__TEXT,__const`: 708 bytes, identical

constant data: same numeric constants and tables in A and B.

55 functions identical instruction-for-instruction (incl. relocation targets), 0 different, 0 present in only one; 9004 disassembly lines (instructions + relocation records) compared in A; 0 code ranges left unnamed.

### Reading

The table lists the functions that are in the linked `cttrace` binary, i.e.
everything the experiments reach; functions of the crate that the harness
does not reference (`api::verify`, `api::public_key`, `slh_verify`, `climb`,
`hash2`, `util::block`, which have out-of-line copies in the rlib but are
inlined at their uses) were removed by the linker and are compared only in
the rlib comparison.

* **No integer division, no indirect branch (no jump tables), no call of
  `memcmp`/`bcmp`** in either build. The calls that leave the crate are the
  allocator (`__rust_alloc`/`realloc`/`dealloc`, `RawVec` growth), `memcpy`,
  `bzero`, and the panic and unwind paths.
* **default build.** No crypto-extension instruction: rustc does not turn the
  portable code into `sha256h`/`sha256su`, although the target has them. The
  compression function is inlined into its callers (`chain_blocks_portable`,
  `thash_short`, `thash_values`, `seed_ctx`, `prf_msg`, `h_msg`,
  `sha256_from`, ...), each with a rounds loop `cmp R, #0x100; b.ne` (round
  counter times 4) indexing `K` and the schedule by that counter; the message
  schedule is the out-of-line `sha256::schedule` (loops on counters, four
  bounds checks of the public block offset). `chain_blocks` itself is a single
  tail jump to `chain_blocks_portable`, whose branches are: the empty-slice
  test, the block counter against the three slice lengths, `start[i]` against
  `end[i]`, the step counter against `end[i]`, and the schedule and rounds
  loops. No branch tests a message-derived or state-derived value; the SIMD
  instructions are 16-byte moves and the vectorised serialisation of words.
* **hw-sha2 build.** 1114 SHA-256 instructions in the crate's functions (the
  whole binary has 1118, T0: four more in the copy of `compress` inlined into
  the harness wrapper), 1062 of them in `chain_blocks`, into which `chain_all`, `enter`, `leave` and the four lane
  kernels `run::<1..4>` are inlined (2704 instructions). Its 33 conditional
  branches test: the slice lengths (fall back to the portable loop); `next <
  blocks.len() && n < 4` and `start[next] < end[next]` (filling the slots);
  the flag `first.known && first.head == head`, computed branch-free with
  `cmp`/`ccmp`/`cset` from the two 64-bit halves of the prefix (the cache; a
  miss executes two more SHA-256 instructions); `n` against 0, 1, 2, 3
  (kernel dispatch and slot compaction); the number of periods against 2 and
  the period counters; `slot.t < slot.end`; and the lane index against
  `blocks.len()` (bounds check before writing a finished chain back). All of
  these are counters derived from `start`/`end`, slice lengths, and the
  prefix equality; no branch or address depends on a vector register (hash
  state, schedule, chain value). The only register-indexed accesses are the
  loads of `start[next]` and `end[next]`. Outside `chain_blocks` the
  single-block `compress` is inlined into its callers as a 16-step loop
  (`cmp R, #0x10`, `cmp R, #0xc`) whose indexed loads are `K` and the four
  schedule vectors by the step counter.
* **Comparisons in the checked signer.** `ht_sign_checked` compares 16-byte
  values with `cmp`/`ccmp`/`cset` and `eor`/`orr`/`cmp`/`csel` (the three
  csel-family instructions in its row), accumulating into a flag without
  branching; its conditional branches are the layer counter (`cmp w, #0x7`,
  `cmp w, #0x6`) and `Vec` capacity checks.
* **Object code.** The functions are instruction-for-instruction the ones
  `cargo build --release` produces from the main crate's manifest. (The first
  function of each object file is disassembled under the assembler's `ltmp0`
  label; the comparison takes its name from the symbol table, so it is
  compared too, which the 2026-11-20 version of the script did not do.) The
  numeric constant sections are identical; the string and panic-location
  sections differ only in the path prefix described above.

The T1 trace equality is the dynamic confirmation of these readings.

## 3. dudect-style timing tests

In short: the noise floor was low enough to measure. No timing difference
was found in whole signing, nor, in any run of either build, in the rows
`wots_pk_gen`, `wots_sign`, `xmss_node`, `xmss_sign`, `fors_node` for z >= 1,
`fors_sign`, `fors_pk_gen` and `slh_keygen_internal` (the generator of this
file checks that). At the hash level, with `PSTATE.DIT = 0`, the fixed-vs-random test flags rows in
both builds; the diagnostics attribute this to the processor reacting to
repeated and to all-zero data (and, for the multi-block rows of the standard
design, to the harness), not to the instruction or address sequence; with
`PSTATE.DIT = 1` nothing is flagged in the corrected design.

### Method

Welch t-test between class 0 (one fixed secret) and class 1 (fresh
pseudo-random secret per measurement); all public inputs identical in both
classes; classes interleaved at random; inputs prepared outside the timed
region. Clock: `mach_absolute_time`, 41.67 ns per tick on this machine, so
short functions are called up to 16384 times per measurement (on the same
input) to make one measurement >= ~20 us; the tables give the count and all
times are per call. Statistic: maximum |t| over the uncropped test and the 100
dudect croppings (measurements above the pooled percentile
1 - 0.5^(10(i+1)/100) discarded). The conventional threshold is 4.5; values
above it are in bold. "std err" is the standard error of the uncropped
difference of class means, i.e. what the row could resolve. The timed call
includes the harness wrapper (decoding the public parameters, copying the
result out; for `chain_blocks` also copying the blocks). Nothing was pinned to
a core (macOS offers no affinity API); the measuring thread asks for
`QOS_CLASS_USER_INTERACTIVE` to stay on performance cores. `PSTATE.DIT` is the
Arm data-independent-timing bit; it is 0 unless a program sets it, the crate
never sets it, and `--dit` sets it on the measuring thread.

Class designs (letters as in the tables):

* **B, fixed vs random**: the dudect design. Class 0's input is a copy of one
  buffer; class 1's is a copy of the public buffer whose secret bytes are then
  overwritten with fresh pseudo-random bytes.
* **C, zero vs random**: as B with the all-zero secret as the fixed one.
* **D**: as B with `PSTATE.DIT = 1`.
* **A, E, random vs random**: both classes fresh random. A true null
  experiment: every |t| is noise. Run before and after B-D.
* **F, G**: as B and D, but both classes are prepared by the same code path
  (drawn like the random class; the fixed class's secret bytes then
  overwritten with the fixed value). Added after D flagged one row; see the
  finding below.
* **H, zero vs fixed**: class 0 the all-zero secret, class 1 another fixed
  pseudo-random secret. Both repeat one value, so a difference is a property
  of the value.
* In the diagnostics also **FF** (two different fixed pseudo-random secrets)
  and **x8** (eight times as many calls per measurement).

The component runs A-H used half the default number of measurements
(`SCALE=0.5`; the "n per class" column is what was measured); the
diagnostics used the default number on ten rows, and four times the default
on the multi-block `chain_blocks` rows.

### Noise floor (looked at before anything else)

The machine was shared with other jobs (Lean builds) during the day; none of
this harness's trace experiments ran while timing was measured. Whether the
timing numbers mean anything was decided from three indicators before reading
any fixed-vs-random result: the null runs A and E that bracket each build's
series; the same statistic on two null splits *within* one class, which every
row of every run carries (class-1 measurements split by arrival parity, and
likewise class 0); and the 1-minute load average before and after each run.

| build | run | 1-min load average before / after | rows | rows with max abs t > 4.5 | largest max abs t | largest within-class null abs t | positive controls: max abs t |
|---|---|---|---|---|---|---|---|
| default | random vs random (null), before | 1.74 / 1.40 | 52 | 0 | 3.84 | 3.26 | - |
| default | fixed (pseudo-random) vs random | 1.40 / 1.85 | 50 | 11 | 129.64 | 3.44 | 76, 116 |
| default | fixed (all-zero) vs random | 1.85 / 1.58 | 50 | 24 | 312.21 | 3.14 | 1083, 289 |
| default | fixed (pseudo-random) vs random, DIT = 1 | 1.58 / 1.66 | 50 | 1 | 7.86 | 3.14 | 75, 121 |
| default | random vs random (null), after | 1.66 / 1.34 | 52 | 0 | 3.42 | 3.76 | - |
| default | fixed vs random, same preparation path | 2.44 / 2.58 | 50 | 8 | 67.86 | 3.35 | 76, 119 |
| default | fixed vs random, same preparation path, DIT = 1 | 2.58 / 2.48 | 50 | 0 | 3.28 | 3.05 | 75, 120 |
| default | fixed all-zero vs fixed pseudo-random | 2.48 / 2.37 | 50 | 25 | 238.37 | 3.13 | 9034, 29883 |
| default | whole signing: slh::slh_sign_internal (m, PK.seed fixed; honest keys) | 1.78 / 1.64 | 1 | 0 | 2.10 | 2.46 | - |
| default | whole signing: slh::slh_sign_internal (m, whole key fixed) | 1.64 / 1.78 | 1 | 0 | 1.41 | 2.19 | - |
| default | whole signing: slh::slh_sign_internal_checked (m, PK.seed fixed; honest keys) | 1.78 / 3.14 | 1 | 0 | 2.23 | 2.35 | - |
| default | whole signing: slh::slh_sign_internal_checked (m, whole key fixed) | 3.14 / 1.87 | 1 | 0 | 2.64 | 2.08 | - |
| hw-sha2 | random vs random (null), before | 1.87 / 2.30 | 52 | 0 | 3.19 | 3.08 | - |
| hw-sha2 | fixed (pseudo-random) vs random | 2.30 / 1.97 | 50 | 2 | 8.27 | 3.71 | 76, 108 |
| hw-sha2 | fixed (all-zero) vs random | 1.97 / 1.39 | 50 | 10 | 18.76 | 2.91 | 1084, 290 |
| hw-sha2 | fixed (pseudo-random) vs random, DIT = 1 | 1.39 / 1.36 | 50 | 2 | 6.02 | 3.38 | 75, 119 |
| hw-sha2 | random vs random (null), after | 1.36 / 1.74 | 52 | 0 | 3.47 | 3.34 | - |
| hw-sha2 | fixed vs random, same preparation path | 2.37 / 2.41 | 50 | 1 | 6.73 | 3.39 | 76, 115 |
| hw-sha2 | fixed vs random, same preparation path, DIT = 1 | 2.41 / 2.59 | 50 | 0 | 3.09 | 2.72 | 75, 121 |
| hw-sha2 | fixed all-zero vs fixed pseudo-random | 2.59 / 2.71 | 50 | 6 | 22.17 | 3.68 | 3427, 14203 |
| hw-sha2 | whole signing: slh::slh_sign_internal (m, PK.seed fixed; honest keys) | 1.74 / 1.97 | 1 | 0 | 2.14 | 1.07 | - |
| hw-sha2 | whole signing: slh::slh_sign_internal (m, whole key fixed) | 1.97 / 2.05 | 1 | 0 | 1.82 | 2.22 | - |
| hw-sha2 | whole signing: slh::slh_sign_internal_checked (m, PK.seed fixed; honest keys) | 2.05 / 2.39 | 1 | 0 | 2.18 | 1.83 | - |
| hw-sha2 | whole signing: slh::slh_sign_internal_checked (m, whole key fixed) | 2.39 / 2.41 | 1 | 0 | 2.82 | 1.46 | - |

Reading: in the four null runs no row exceeds 4.5 (the generator of this
file checks that), the within-class null splits stay below 4 in every run,
the positive
controls are detected in every fixed-vs-random run with max |t| in the tens
to hundreds, and the load average stayed between about 1 and 3. So the noise
floor is low enough for the timing results to be reported: a row above 4.5
in runs B-H is a real difference between the two classes of that run. As D2
shows, that is not the same as a difference caused by the secret.

### D1. Components (`out/*/dudect_null_*.md`, `dudect_components_*.md`)

max |t| of every run, one line per function. default build:

| function | n per class | median, DIT = 0 / 1 (ns/call) | std err (ns) | A: null before | B: fixed vs random | C: zero vs random | D: fixed vs random, DIT = 1 | E: null after | F: as B, same preparation | G: as D, same preparation | H: zero vs fixed |
|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | 100000 | 205.1 / 234.0 | 0.055 | 1.5 | **12.7** | **13.9** | 2.2 | 1.2 | **12.9** | 2.4 | 2.2 |
| sha256/len=16 | 100000 | 189.5 / 219.1 | 0.057 | 1.7 | 2.0 | **8.9** | 1.9 | 2.6 | 1.7 | 2.1 | **8.3** |
| sha256/len=55 | 100000 | 167.0 / 194.7 | 0.056 | 1.4 | **5.9** | **19.6** | 2.1 | 2.8 | **7.3** | 2.0 | **9.8** |
| sha256/len=56 | 100000 | 340.5 / 395.8 | 0.124 | 1.9 | **5.9** | **21.1** | 1.5 | 2.0 | 3.3 | 3.0 | **8.4** |
| sha256/len=64 | 100000 | 339.8 / 391.3 | 0.129 | 3.1 | 2.5 | **38.1** | 2.1 | 1.4 | 2.3 | 2.3 | **29.5** |
| sha256/len=119 | 100000 | 300.8 / 353.5 | 0.113 | 2.7 | **5.4** | **76.7** | 2.2 | 1.2 | 1.3 | 1.8 | **38.3** |
| sha256/len=120 | 100000 | 474.6 / 556.6 | 0.177 | 3.8 | 2.7 | **28.6** | 1.3 | 2.7 | 3.5 | 2.4 | **16.4** |
| sha256/len=256 | 100000 | 751.3 / 875.0 | 0.293 | 2.4 | 2.0 | **42.4** | 2.4 | 1.7 | 2.3 | 1.5 | **56.3** |
| sha256/len=560 | 100000 | 1260.4 / 1481.8 | 0.551 | 1.8 | 1.3 | **58.6** | 2.1 | 1.9 | 1.4 | 1.4 | **57.8** |
| hmac_sha256/klen=16,mlen=32 | 50000 | 789.1 / 927.1 | 0.367 | 1.8 | 3.1 | **7.7** | 2.6 | 2.3 | 2.4 | 2.7 | **7.1** |
| hmac_sha256/klen=16,mlen=150 | 50000 | 1104.2 / 1291.7 | 0.493 | 1.8 | 2.2 | 2.2 | 2.4 | 1.3 | 1.7 | 1.5 | **4.9** |
| hmac_sha256/klen=64,mlen=64 | 50000 | 955.7 / 1122.4 | 0.430 | 1.8 | 1.4 | 1.9 | 2.7 | 1.3 | 1.1 | 2.3 | 2.5 |
| hmac_sha256/klen=32,mlen=1 | 50000 | 824.2 / 963.5 | 0.381 | 2.1 | 1.2 | **7.9** | 2.3 | 1.7 | 2.0 | 2.3 | **10.4** |
| compress (copy inlined into the wrapper) | 100000 | 135.9 / 160.8 | 0.047 | 2.0 | **129.6** | **312.2** | 2.0 | 1.9 | **67.9** | 1.8 | **238.4** |
| thash_short/len=16 | 100000 | 141.6 / 164.7 | 0.044 | 2.5 | 2.8 | 2.7 | 1.8 | 1.9 | 1.9 | 1.4 | 3.9 |
| thash_short/len=32 | 100000 | 142.4 / 165.4 | 0.048 | 2.5 | **22.2** | **6.7** | 1.9 | 2.1 | **16.6** | 2.8 | **14.1** |
| thash/len=16 | 100000 | 202.5 / 229.8 | 0.064 | 1.6 | **5.5** | **5.5** | 2.0 | 2.4 | **7.7** | 2.2 | **6.0** |
| thash/len=32 | 100000 | 198.2 / 224.6 | 0.061 | 2.7 | 4.5 | **12.3** | 1.5 | 2.0 | **13.2** | 2.6 | **6.0** |
| thash/len=224 | 100000 | 607.4 / 710.9 | 0.198 | 1.9 | 1.1 | **21.6** | 1.6 | 1.8 | 1.7 | 1.3 | **8.0** |
| thash/len=560 | 100000 | 1479.2 / 1734.4 | 0.576 | 1.7 | 1.4 | **22.5** | 3.5 | 1.8 | 1.5 | 1.8 | **20.1** |
| thash_values | 50000 | 1369.8 / 1619.8 | 0.748 | 1.6 | 2.7 | **31.3** | 2.1 | 1.3 | 2.0 | 1.6 | **34.5** |
| prf_msg/mlen=0 | 50000 | 639.3 / 750.0 | 0.315 | 1.9 | 2.1 | 1.5 | 2.3 | 2.2 | 2.4 | 1.5 | 1.9 |
| prf_msg/mlen=32 | 50000 | 644.5 / 751.3 | 0.317 | 2.4 | 2.8 | 4.0 | 1.9 | 1.7 | 1.6 | 3.3 | **5.0** |
| prf_msg/mlen=100 | 50000 | 778.6 / 912.8 | 0.401 | 3.3 | 3.0 | 1.8 | 1.5 | 2.8 | 2.2 | 2.1 | 2.4 |
| prf_msg/mlen=1000 | 50000 | 2880.2 / 3385.4 | 1.745 | 1.8 | 2.1 | 1.5 | 1.7 | 1.6 | 2.4 | 2.1 | 2.0 |
| chain_blocks/n=1,steps=0..15 | 50000 | 2026.0 / 2541.7 | 1.117 | 1.6 | **57.7** | **63.6** | 2.2 | 2.6 | **65.2** | 3.2 | **4.8** |
| chain_blocks/n=4,steps=0..15 | 25000 | 8083.3 / 10083.3 | 6.727 | 1.5 | 2.0 | **55.4** | 2.2 | 1.9 | 2.0 | 2.3 | **34.6** |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | 10000 | 70708.3 / 87916.7 | 61.146 | 2.7 | 3.6 | **41.8** | 3.1 | 1.7 | 3.7 | 3.1 | **39.0** |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | 10000 | 31166.7 / 38791.7 | 36.805 | 2.7 | **5.8** | **23.4** | 2.8 | 2.3 | 2.7 | 1.9 | **24.7** |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | 25000 | 1895.8 / 2250.0 | 1.687 | 2.3 | 2.0 | **43.0** | 2.4 | 1.6 | 1.6 | 1.3 | **40.3** |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | 5000 | 17291.7 / 20416.7 | 33.724 | 1.9 | **6.1** | **19.5** | **7.9** | 2.1 | 2.7 | 2.6 | **13.2** |
| wots_pk_gen | 25000 | 76625.0 / 95041.7 | 41.256 | 2.1 | 1.7 | 1.3 | 2.6 | 3.4 | 2.2 | 2.6 | 1.8 |
| wots_sign | 25000 | 39375.0 / 48666.7 | 26.671 | 2.0 | 1.2 | 1.3 | 2.6 | 2.7 | 2.6 | 2.2 | 1.8 |
| xmss_node/z=0 | 5000 | 76625.0 / 95041.7 | 87.238 | 2.1 | 2.5 | 2.0 | 1.2 | 2.3 | 2.7 | 2.2 | 3.0 |
| xmss_node/z=1 | 5000 | 153458.3 / 190375.0 | 216.861 | 2.1 | 1.9 | 2.0 | 1.3 | 1.8 | 2.5 | 1.5 | 1.9 |
| xmss_node/z=2 | 1500 | 306958.3 / 381791.7 | 699.938 | 1.7 | 2.7 | 1.8 | 2.5 | 1.6 | 2.7 | 1.7 | 1.9 |
| xmss_node/z=3 | 1500 | 616958.3 / 764208.3 | 1056.523 | 2.3 | 1.9 | 3.3 | 1.9 | 2.4 | 2.2 | 2.8 | 1.9 |
| xmss_node/z=4 | 1500 | 1238958.3 / 1535291.7 | 2113.485 | 2.7 | 1.1 | 2.3 | 2.6 | 2.6 | 2.9 | 1.9 | 2.2 |
| xmss_sign | 250 | 39727250.0 / 49170583.3 | 89273.715 | 2.8 | 1.7 | 2.2 | 2.5 | 1.5 | 2.3 | 2.5 | 2.8 |
| fors_sk_gen | 100000 | 146.5 / 168.6 | 0.060 | 2.2 | 1.4 | 3.5 | 2.3 | 1.7 | 2.3 | 1.8 | 3.8 |
| fors_node/z=0 | 50000 | 372.4 / 432.9 | 0.205 | 2.0 | **5.6** | 3.2 | 2.7 | 1.2 | **6.2** | 2.2 | 1.4 |
| fors_node/z=1 | 50000 | 787.8 / 928.4 | 0.393 | 1.8 | 2.1 | 1.7 | 1.7 | 2.5 | 2.1 | 2.0 | 1.3 |
| fors_node/z=3 | 15000 | 3250.0 / 3932.3 | 3.319 | 2.2 | 1.6 | 1.6 | 2.0 | 1.8 | 3.1 | 1.9 | 2.2 |
| fors_node/z=6 | 2500 | 26166.7 / 31375.0 | 73.814 | 1.3 | 1.9 | 2.0 | 2.4 | 2.5 | 2.2 | 2.0 | 1.4 |
| fors_node/z=7 | 2500 | 52166.7 / 62750.0 | 119.903 | 3.0 | 1.6 | 1.4 | 3.6 | 2.0 | 1.7 | 1.9 | 1.3 |
| fors_node/z=8 | 2500 | 104416.7 / 125625.0 | 268.583 | 1.7 | 1.8 | 1.8 | 1.9 | 2.1 | 1.9 | 2.0 | 2.8 |
| fors_node/z=12 | 1000 | 1698958.3 / 2024208.3 | 6513.608 | 1.8 | 1.9 | 1.8 | 1.8 | 2.2 | 2.8 | 1.6 | 1.3 |
| fors_sign | 150 | 24735458.3 / 28357916.7 | 127849.752 | 2.2 | 3.1 | 1.1 | 1.4 | 2.5 | 1.8 | 1.5 | 1.8 |
| fors_pk_gen | 150 | 25104875.0 / 28376875.0 | 130250.903 | 2.6 | 2.0 | 2.1 | 1.9 | 1.9 | 2.4 | 1.6 | 2.2 |
| slh_keygen_internal | 500 | 39771791.7 / 49173208.3 | 63626.152 | 1.8 | 2.8 | 1.7 | 1.9 | 2.7 | 1.8 | 1.6 | 1.7 |
| CONTROL leaky_cmp (early-exit compare of secret) | 10000 | 0.9 / 0.9 | 2.954 | 2.8 | **75.6** | **1083.1** | **75.2** | 2.3 | **75.7** | **75.2** | **9034.0** |
| CONTROL leaky_loop (secret-dependent iteration count) | 10000 | 679.7 / 796.9 | 2.543 | 2.6 | **115.6** | **289.1** | **120.6** | 2.9 | **118.6** | **119.9** | **29882.7** |

hw-sha2 build:

| function | n per class | median, DIT = 0 / 1 (ns/call) | std err (ns) | A: null before | B: fixed vs random | C: zero vs random | D: fixed vs random, DIT = 1 | E: null after | F: as B, same preparation | G: as D, same preparation | H: zero vs fixed |
|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | 100000 | 89.8 / 108.6 | 0.023 | 3.2 | **8.3** | **6.6** | 1.9 | 1.4 | **6.7** | 2.2 | 2.8 |
| sha256/len=16 | 100000 | 74.3 / 88.5 | 0.023 | 2.2 | 3.2 | 2.8 | 1.8 | 2.0 | 2.6 | 2.5 | 3.5 |
| sha256/len=55 | 100000 | 48.4 / 63.0 | 0.016 | 2.6 | 2.7 | **9.6** | 2.6 | 1.3 | 4.1 | 1.9 | **12.3** |
| sha256/len=56 | 100000 | 103.5 / 118.0 | 0.029 | 2.2 | 1.8 | 2.8 | 3.2 | 1.0 | 2.8 | 1.8 | 4.2 |
| sha256/len=64 | 100000 | 111.7 / 112.6 | 0.036 | 1.8 | 1.7 | 2.7 | 2.2 | 1.8 | 2.7 | 2.4 | 1.6 |
| sha256/len=119 | 100000 | 62.7 / 75.0 | 0.025 | 2.1 | 2.4 | **15.6** | 2.3 | 1.6 | 3.4 | 2.2 | **22.2** |
| sha256/len=120 | 100000 | 117.0 / 138.0 | 0.036 | 1.5 | 1.6 | 2.2 | 2.2 | 3.0 | 1.6 | 2.5 | 3.2 |
| sha256/len=256 | 100000 | 154.3 / 170.9 | 0.046 | 1.9 | 1.8 | 1.8 | 2.2 | 2.7 | 1.9 | 1.3 | 1.6 |
| sha256/len=560 | 100000 | 188.2 / 212.2 | 0.047 | 1.6 | 1.5 | **6.2** | 1.5 | 3.1 | 2.2 | 1.5 | **8.0** |
| hmac_sha256/klen=16,mlen=32 | 50000 | 343.8 / 413.4 | 0.186 | 2.5 | 1.4 | 1.9 | 2.1 | 1.4 | 2.0 | 1.8 | 3.2 |
| hmac_sha256/klen=16,mlen=150 | 50000 | 418.6 / 470.7 | 0.204 | 1.7 | 1.3 | 3.6 | 1.7 | 1.5 | 2.4 | 1.6 | 2.0 |
| hmac_sha256/klen=64,mlen=64 | 50000 | 391.3 / 462.9 | 0.193 | 2.5 | 1.6 | 2.2 | 3.6 | 1.3 | 1.9 | 2.8 | 2.5 |
| hmac_sha256/klen=32,mlen=1 | 50000 | 390.0 / 444.0 | 0.198 | 1.6 | 1.6 | 1.7 | 2.5 | 1.8 | 3.2 | 2.1 | 2.1 |
| compress (copy inlined into the wrapper) | 100000 | 15.7 / 17.2 | 0.003 | 1.4 | 2.5 | 2.9 | 1.9 | 1.5 | 2.1 | 1.7 | 1.7 |
| thash_short/len=16 | 100000 | 25.7 / 37.4 | 0.016 | 1.8 | 2.0 | **8.1** | 3.0 | 2.8 | 1.9 | 2.8 | **8.0** |
| thash_short/len=32 | 100000 | 24.7 / 36.5 | 0.018 | 1.3 | 1.4 | 1.8 | 1.6 | 1.7 | 1.8 | 1.1 | 1.9 |
| thash/len=16 | 100000 | 87.4 / 96.8 | 0.039 | 2.3 | 2.0 | 3.3 | 1.7 | 1.7 | 1.5 | 2.9 | **5.7** |
| thash/len=32 | 100000 | 82.2 / 94.9 | 0.033 | 1.5 | 2.8 | **6.6** | 2.0 | 2.6 | 3.5 | 1.9 | 4.5 |
| thash/len=224 | 100000 | 134.6 / 168.0 | 0.058 | 1.8 | 2.3 | **9.2** | 2.5 | 1.7 | 3.5 | 3.1 | 3.2 |
| thash/len=560 | 100000 | 306.0 / 336.6 | 0.081 | 2.6 | 2.1 | 2.1 | 1.4 | 2.0 | 1.5 | 2.5 | 1.9 |
| thash_values | 50000 | 192.4 / 204.8 | 0.071 | 2.0 | 4.0 | **7.4** | 2.1 | 1.8 | 1.3 | 2.4 | 1.4 |
| prf_msg/mlen=0 | 50000 | 160.2 / 184.2 | 0.084 | 2.2 | 1.2 | 2.8 | 3.3 | 1.9 | 2.4 | 2.7 | 3.6 |
| prf_msg/mlen=32 | 50000 | 177.1 / 195.6 | 0.122 | 1.6 | 2.8 | 1.5 | 2.4 | 3.0 | 1.6 | 2.2 | 1.9 |
| prf_msg/mlen=100 | 50000 | 204.8 / 217.8 | 0.144 | 1.8 | 1.4 | 1.6 | 1.5 | 2.4 | 0.9 | 3.1 | 1.4 |
| prf_msg/mlen=1000 | 50000 | 527.3 / 587.9 | 0.231 | 2.3 | 2.8 | 2.1 | 2.3 | 2.3 | 1.8 | 2.2 | 2.4 |
| chain_blocks/n=1,steps=0..15 | 50000 | 307.9 / 308.3 | 0.116 | 2.6 | 1.8 | 2.6 | 1.6 | 3.5 | 2.5 | 2.1 | 2.5 |
| chain_blocks/n=4,steps=0..15 | 25000 | 799.5 / 800.8 | 0.379 | 2.3 | 2.4 | 1.9 | 2.1 | 1.9 | 1.7 | 1.9 | 1.6 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | 10000 | 6812.5 / 6802.1 | 5.206 | 2.3 | **6.1** | 3.4 | 2.6 | 3.3 | 1.6 | 1.3 | 2.1 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | 10000 | 3083.3 / 3099.0 | 2.444 | 2.0 | 2.8 | **5.4** | **5.9** | 2.2 | 1.6 | 2.0 | 1.5 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | 25000 | 221.0 / 221.0 | 0.106 | 2.7 | 2.4 | 1.8 | 2.4 | 2.0 | 1.6 | 2.1 | 2.4 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | 5000 | 1817.7 / 1791.7 | 1.700 | 1.9 | 2.0 | 3.6 | **6.0** | 2.5 | 2.3 | 3.0 | 1.4 |
| wots_pk_gen | 25000 | 7687.5 / 7572.9 | 4.085 | 1.6 | 1.1 | 1.2 | 1.3 | 1.7 | 1.7 | 2.1 | 1.6 |
| wots_sign | 25000 | 4328.1 / 4239.6 | 1.849 | 2.6 | 2.5 | 2.2 | 1.9 | 2.0 | 1.4 | 2.8 | 1.9 |
| xmss_node/z=0 | 5000 | 7531.2 / 7572.9 | 7.384 | 2.6 | 1.0 | 2.0 | 2.3 | 2.3 | 2.2 | 2.9 | 1.9 |
| xmss_node/z=1 | 5000 | 15104.2 / 15187.5 | 16.019 | 1.9 | 1.9 | 1.4 | 3.5 | 2.6 | 3.2 | 2.9 | 1.9 |
| xmss_node/z=2 | 1500 | 30208.3 / 30416.7 | 57.424 | 2.1 | 2.8 | 2.2 | 1.4 | 2.4 | 1.7 | 1.7 | 2.4 |
| xmss_node/z=3 | 1500 | 60458.3 / 60875.0 | 94.936 | 2.2 | 1.4 | 2.5 | 2.2 | 2.7 | 2.6 | 2.2 | 1.7 |
| xmss_node/z=4 | 1500 | 121000.0 / 121750.0 | 172.705 | 1.8 | 1.5 | 1.8 | 1.4 | 1.6 | 2.1 | 2.2 | 2.6 |
| xmss_sign | 250 | 3898208.3 / 3926541.7 | 2758.473 | 1.2 | 1.8 | 1.4 | 2.0 | 2.3 | 2.5 | 1.8 | 1.0 |
| fors_sk_gen | 100000 | 24.7 / 36.6 | 0.013 | 1.6 | 2.2 | **18.8** | 2.4 | 2.9 | 1.3 | 1.6 | **21.7** |
| fors_node/z=0 | 50000 | 155.9 / 149.7 | 0.074 | 1.7 | 2.0 | 2.7 | 2.0 | 1.4 | 1.4 | 2.2 | 1.4 |
| fors_node/z=1 | 50000 | 217.8 / 224.3 | 0.087 | 1.8 | 1.8 | 1.7 | 2.1 | 2.4 | 2.4 | 2.3 | 2.4 |
| fors_node/z=3 | 15000 | 538.4 / 539.1 | 0.336 | 1.8 | 2.5 | 1.5 | 2.3 | 2.0 | 2.0 | 1.7 | 2.1 |
| fors_node/z=6 | 2500 | 3171.9 / 3187.5 | 5.645 | 2.1 | 2.5 | 1.6 | 3.2 | 2.1 | 1.6 | 1.9 | 1.3 |
| fors_node/z=7 | 2500 | 6135.4 / 6135.4 | 12.122 | 0.9 | 1.8 | 1.6 | 1.7 | 2.0 | 1.7 | 2.0 | 2.1 |
| fors_node/z=8 | 2500 | 12333.3 / 12375.0 | 25.951 | 2.2 | 2.1 | 1.8 | 1.8 | 2.0 | 2.0 | 2.3 | 1.8 |
| fors_node/z=12 | 1000 | 197875.0 / 198750.0 | 283.356 | 1.2 | 2.3 | 1.6 | 2.0 | 1.6 | 2.2 | 2.0 | 2.2 |
| fors_sign | 150 | 2811041.7 / 2805958.3 | 4414.668 | 2.1 | 2.0 | 2.1 | 3.1 | 1.4 | 1.6 | 1.9 | 2.3 |
| fors_pk_gen | 150 | 2793000.0 / 2790791.7 | 2982.463 | 1.7 | 1.4 | 1.5 | 1.3 | 2.4 | 1.5 | 2.6 | 1.5 |
| slh_keygen_internal | 500 | 3906291.7 / 3931500.0 | 2051.062 | 1.4 | 2.8 | 1.7 | 1.2 | 1.3 | 1.1 | 2.2 | 1.6 |
| CONTROL leaky_cmp (early-exit compare of secret) | 10000 | 0.9 / 0.9 | 2.992 | 2.6 | **75.7** | **1084.3** | **75.2** | 2.7 | **75.7** | **75.2** | **3427.0** |
| CONTROL leaky_loop (secret-dependent iteration count) | 10000 | 207.4 / 272.8 | 0.794 | 2.5 | **108.0** | **289.8** | **119.4** | 2.9 | **114.7** | **121.3** | **14202.8** |

### D2. Diagnostics on the flagged rows (`out/*/dudect_diag.md`, `dudect_diag_chain.md`)

Ten hash-level rows, default number of measurements (200k to 400k per row),
max |t|; 1-minute load average between 1.44 and 2.31 over the 13 runs (default) and 1-minute load average between 2.37 and 2.95 over the 13 runs (hw-sha2).
RR = random vs random, FF = two fixed pseudo-random secrets, FR = fixed vs
random (design B), FR/same = design F, FR/x8 = eight times the calls per
measurement, FZ = zero vs random (C), ZF = zero vs fixed (H), /DIT =
`PSTATE.DIT = 1`.

default build:

| function | RR (seed 1001) | FF (seed 1001) | FF (seed 1002) | FR (seed 1001) | FR/same (seed 1001) | FR/x8 (seed 1001) | FZ (seed 1001) | FR/DIT (seed 1001) | FZ/DIT (seed 1001) | FF/DIT (seed 1001) | RR (seed 1002) | ZF (seed 1001) | ZF/DIT (seed 1001) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | 1.7 | 2.4 | 3.0 | **17.9** | **22.4** | 4.0 | **25.0** | 0.9 | 2.1 | 1.9 | 1.8 | 3.0 | 3.3 |
| sha256/len=16 | 1.6 | 2.4 | 2.3 | 2.9 | 3.4 | **5.1** | **20.8** | 2.0 | 2.3 | 1.4 | 1.2 | **13.5** | 1.3 |
| sha256/len=119 | 2.7 | 1.3 | 2.1 | **5.9** | **6.8** | **14.4** | **72.0** | 2.0 | 2.2 | 2.0 | 2.0 | **59.5** | 1.8 |
| sha256/len=120 | 1.6 | 2.2 | 2.7 | 2.9 | **12.6** | 3.1 | **45.5** | 2.2 | 2.4 | 2.3 | 1.6 | **34.5** | 2.5 |
| compress (copy inlined into the wrapper) | 2.1 | 1.6 | 1.7 | **187.0** | **94.9** | **35.6** | **426.1** | 1.5 | 2.0 | 1.2 | 2.0 | **300.4** | 2.7 |
| thash_short/len=16 | 1.8 | 1.7 | 3.5 | 1.4 | 1.8 | **39.7** | 2.3 | 2.4 | 1.7 | 1.5 | 2.7 | 3.1 | 1.8 |
| thash_short/len=32 | 1.9 | 1.5 | 2.1 | **30.6** | **35.6** | **6.1** | **8.6** | 2.8 | 1.6 | 2.2 | 2.7 | **49.1** | 2.8 |
| chain_blocks/n=1,steps=0..15 | 1.8 | 2.4 | 1.7 | **78.7** | **83.4** | **22.9** | **80.7** | 2.9 | 1.5 | 1.5 | 2.2 | 3.7 | 2.3 |
| fors_sk_gen | 1.5 | 3.2 | 1.4 | 2.9 | **6.0** | **5.2** | 2.0 | 1.4 | 1.4 | 1.7 | 1.2 | **5.3** | 2.9 |
| fors_node/z=0 | 2.1 | 2.8 | 2.0 | **12.4** | **6.0** | 2.7 | **6.9** | 2.5 | 2.4 | 2.2 | 2.5 | 1.7 | 1.4 |

hw-sha2 build:

| function | RR (seed 1001) | FF (seed 1001) | FF (seed 1002) | FR (seed 1001) | FR/same (seed 1001) | FR/x8 (seed 1001) | FZ (seed 1001) | FR/DIT (seed 1001) | FZ/DIT (seed 1001) | FF/DIT (seed 1001) | RR (seed 1002) | ZF (seed 1001) | ZF/DIT (seed 1001) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | 1.2 | 1.9 | 1.8 | **8.9** | **13.1** | 2.5 | **9.3** | 2.2 | 1.9 | 1.5 | 1.8 | 1.1 | 1.7 |
| sha256/len=16 | 2.2 | 2.5 | 2.1 | 1.6 | 2.5 | 1.5 | **5.5** | 3.7 | 1.7 | 2.7 | 2.5 | **9.4** | 1.9 |
| sha256/len=119 | 2.3 | 1.6 | 2.1 | 2.7 | 1.4 | 1.4 | **21.3** | 1.4 | 1.7 | 1.4 | 2.1 | **37.1** | 2.6 |
| sha256/len=120 | 1.8 | 2.3 | 2.0 | 1.8 | 2.0 | 1.4 | 3.3 | 1.8 | 2.7 | 2.0 | 2.9 | **18.6** | 2.6 |
| compress (copy inlined into the wrapper) | 1.7 | 2.9 | 2.8 | 2.4 | 1.1 | 2.0 | 2.2 | 1.1 | 2.3 | 2.3 | 1.4 | 2.4 | 2.1 |
| thash_short/len=16 | 1.7 | 2.0 | 2.4 | 2.1 | 1.7 | 2.2 | **13.1** | 2.7 | 2.1 | 1.6 | 2.8 | **11.5** | 1.8 |
| thash_short/len=32 | 1.6 | 2.0 | 1.5 | 1.3 | 1.6 | 1.5 | 3.0 | 2.8 | 2.0 | 1.7 | 1.7 | 2.6 | 1.2 |
| chain_blocks/n=1,steps=0..15 | 1.4 | 1.7 | 2.4 | 1.7 | 1.8 | 2.5 | 2.4 | 2.1 | 1.7 | 1.8 | 1.9 | 2.1 | 2.7 |
| fors_sk_gen | 2.2 | 1.9 | 2.3 | 1.5 | 2.8 | 2.2 | **28.3** | 3.1 | 3.0 | 1.6 | 1.9 | **29.3** | 1.8 |
| fors_node/z=0 | 2.6 | 2.2 | 2.2 | 2.6 | 1.6 | 1.8 | 2.0 | 1.5 | 2.8 | 2.2 | 2.3 | 2.2 | 2.4 |

The multi-block `chain_blocks` rows, four times the default number of
measurements (80k to 400k per class); 1-minute load average between 1.30 and 2.44 over the 14 runs (default) and
1-minute load average between 1.43 and 2.81 over the 14 runs (hw-sha2).

default build:

| function | RR/DIT (seed 2001) | FF/DIT (seed 2001) | FR/DIT (seed 2001) | FR/same/DIT (seed 2001) | RR/DIT (seed 2002) | FF/DIT (seed 2002) | FR/DIT (seed 2002) | FR/same/DIT (seed 2002) | RR (seed 2001) | FF (seed 2001) | FR (seed 2001) | FR/same (seed 2001) | ZF (seed 2001) | ZF/DIT (seed 2001) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | 2.4 | 1.6 | 1.4 | 1.4 | 2.5 | 3.3 | 2.1 | 3.5 | 1.4 | 2.0 | 1.8 | 1.3 | **190.3** | 1.1 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | 1.7 | 3.2 | **8.9** | 3.1 | 3.3 | 1.9 | **9.1** | 1.4 | 2.4 | 2.2 | **26.2** | 2.2 | **114.1** | 1.4 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | 1.9 | 2.6 | **9.8** | 2.5 | 2.2 | 3.0 | **12.6** | 2.3 | 2.0 | 2.0 | **22.2** | 2.2 | **77.5** | 2.4 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | 1.4 | 2.2 | 3.5 | 2.3 | 1.9 | 2.9 | 2.7 | 1.6 | 2.4 | 1.3 | 2.4 | 2.8 | **115.1** | 2.9 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | 2.1 | 1.7 | **20.4** | 2.5 | 1.5 | 2.8 | **13.8** | 2.4 | 2.1 | 1.9 | **13.1** | 1.5 | **31.9** | 1.4 |

hw-sha2 build:

| function | RR/DIT (seed 2001) | FF/DIT (seed 2001) | FR/DIT (seed 2001) | FR/same/DIT (seed 2001) | RR/DIT (seed 2002) | FF/DIT (seed 2002) | FR/DIT (seed 2002) | FR/same/DIT (seed 2002) | RR (seed 2001) | FF (seed 2001) | FR (seed 2001) | FR/same (seed 2001) | ZF (seed 2001) | ZF/DIT (seed 2001) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | 2.2 | 1.1 | 2.0 | 2.6 | 2.4 | 1.3 | 2.3 | 1.8 | 1.9 | 3.0 | 2.8 | 2.9 | 1.6 | 1.1 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | 3.4 | 2.6 | **7.2** | 2.4 | 2.8 | 1.5 | **10.4** | 2.2 | 2.2 | 1.9 | **6.9** | 2.0 | 2.5 | 1.7 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | 2.1 | 1.9 | **10.2** | 2.1 | 1.3 | 1.1 | **7.4** | 2.0 | 1.2 | 1.7 | **8.7** | 2.7 | 2.4 | 3.3 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | 1.4 | 2.3 | 2.7 | 1.9 | 2.6 | 2.5 | 2.5 | 1.6 | 2.0 | 2.6 | 2.6 | 3.2 | 2.0 | 1.8 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | 1.8 | 1.6 | **6.8** | 2.3 | 1.9 | 2.2 | **7.7** | 2.3 | 2.5 | 2.1 | **6.8** | 2.5 | 2.4 | 1.4 |

### Timing finding: with DIT off, the CPU's timing depends on the data; with DIT on, no dependence was detected

This is the one non-clean result of the whole exercise, so it is spelled out.
It concerns the processor, not the instruction or address sequence: T1 shows
that the traces of all the functions below are identical across the values
of the varied bytes, and the all-zero value used here is the first pair of
every T1 row.

**What was measured, default build.**

1. *Fixed vs random is distinguishable with `PSTATE.DIT = 0`* (column B):
   11 of 50 rows above 4.5 --
   `sha256/len=1` (12.7), `sha256/len=55` (5.9), `sha256/len=56` (5.9), `sha256/len=119` (5.4), `compress` (129.6), `thash_short/len=32` (22.2), `thash/len=16` (5.5), `chain_blocks/n=1,steps=0..15` (57.7), `chain_blocks/n=35,steps=0..d_i` (5.8), `chain_blocks/n=128,steps=t_i..t_i+1` (6.1), `fors_node/z=0` (5.6). The varied bytes are, per row: the whole
   message (`sha256`), state and block (`compress`), the hashed value
   (`thash_short`, `thash`), bytes 16..64 of the blocks (`chain_blocks`),
   SK.seed (`fors_node`). The differences are small (the class means differ by
   0.01% to 0.25% of the call time) but far outside the noise of columns A
   and E.
2. *The all-zero secret against random ones* (column C) is distinguishable in
   24 of 50 rows, most strongly `compress` (all-zero
   state and block run about 1.7% faster than random ones).
3. *For the multi-block `chain_blocks` rows, the flags of the standard
   fixed-vs-random design come from the harness, not from the data.* Two of
   the rows flagged in B are such rows, and with `PSTATE.DIT = 1` the
   standard design still flagged `chain_blocks/n=128,steps=t_i..t_i+1` (7.9) (column D).
   The follow-up on these rows with four times the measurements shows why:
   with DIT on, fixed vs random in the standard design is flagged for the
   35-block and 128-block rows in both seeds, while random vs random, fixed
   vs fixed, and fixed vs random *with both classes prepared by the same code
   path* are not; without DIT the same. In the standard design the random
   class's 1.7 to 6 kilobytes of block bytes are written in small pieces
   after the buffer was copied, the fixed class's in one copy, and with one
   or two calls per measurement the timed region evidently still sees that.
   This is a defect of the standard preparation for rows with large inputs
   (the 2026-11-20 harness had the same preparation, and no row with
   kilobytes of varied bytes); columns F and G are the same runs without it.
4. *In the corrected design, with `PSTATE.DIT = 0`* (column F),
   8 of 50 rows remain above 4.5:
   `sha256/len=1` (12.9), `sha256/len=55` (7.3), `compress` (67.9), `thash_short/len=32` (16.6), `thash/len=16` (7.7), `thash/len=32` (13.2), `chain_blocks/n=1,steps=0..15` (65.2), `fors_node/z=0` (6.2). All of them are short hash-level calls
   (at most 15 compressions) repeated 8 to 256 times per measurement on one
   input. The other rows are not flagged, among them every row at the level
   of WOTS+, XMSS, FORS above the leaves and key generation, `prf_msg`,
   `fors_sk_gen`, `thash_short/len=16`, and the multi-block `chain_blocks`
   rows.
5. *It is the repetition, not the value, for generic values.* Two different
   fixed pseudo-random secrets are not distinguishable in any diagnostic row
   (FF: two pairs on the ten hash-level rows, one pair on the multi-block
   rows, and more with DIT on; none above 4.5). So column F does not say that the time depends on which
   secret is processed; it says that a class which keeps presenting the same
   value is processed slightly differently from one that never repeats one.
   Eight times as many calls per measurement (FR/x8) changes which rows are
   flagged and by how much, without a simple pattern; no conclusion is drawn
   from that column.
6. *But the all-zero value is special.* Against another fixed value (column
   H; ZF in the diagnostics), i.e. with both classes repeating one value and
   prepared alike, the all-zero secret is distinguishable in
   25 of 50 rows (`sha256/len=16` (8.3), `sha256/len=55` (9.8), `sha256/len=56` (8.4), `sha256/len=64` (29.5), `sha256/len=119` (38.3), `sha256/len=120` (16.4), `sha256/len=256` (56.3), `sha256/len=560` (57.8), `hmac_sha256/klen=16,mlen=32` (7.1), `hmac_sha256/klen=16,mlen=150` (4.9), `hmac_sha256/klen=32,mlen=1` (10.4), `compress` (238.4), `thash_short/len=32` (14.1), `thash/len=16` (6.0), `thash/len=32` (6.0), `thash/len=224` (8.0), `thash/len=560` (20.1), `thash_values` (34.5), `prf_msg/mlen=32` (5.0), `chain_blocks/n=1,steps=0..15` (4.8), `chain_blocks/n=4,steps=0..15` (34.6), `chain_blocks/n=35,steps=0..15` (39.0), `chain_blocks/n=35,steps=0..d_i` (24.7), `chain_blocks/n=14,steps=t_i..t_i+1` (40.3), `chain_blocks/n=128,steps=t_i..t_i+1` (13.2)):
   wherever the zeroed bytes are a bulk hash input -- `sha256` from 16 bytes
   up, `compress` (all-zero state and block about 0.5% to 1.1% faster),
   `thash`, `thash_values`, the `chain_blocks` rows (blocks whose bytes 16..64
   are zero run 0.2% faster to 1.1% slower; with four times the measurements
   max |t| is 32 to 190 on the multi-block rows). Where the zeroed secret is
   only SK.seed it is not distinguishable in column H (`wots_*`, `xmss_*`,
   `fors_*`, key generation; `fors_sk_gen` is at 5.3 in the diagnostics and
   below 4.5 in H), and `prf_msg` with SK.prf and addrnd zeroed is at the
   threshold in one of four rows. So with DIT off there is a dependence on
   the value itself, at least for this extreme value. Values between "all-zero"
   and "pseudo-random" (single zero words, low weight) were not tried.
7. *With `PSTATE.DIT = 1` none of this is there.* In the corrected design
   (column G) 0 of 50 rows exceed 4.5; in the
   diagnostics, with DIT on, fixed vs random, zero vs random, fixed vs fixed
   and zero vs fixed are all below 4.5 on the ten hash-level rows, and so are
   fixed vs random with the same preparation, fixed vs fixed and zero vs
   fixed on the multi-block rows. DIT costs 13% to 25% in speed on this machine
   (the two medians of each row).

**hw-sha2 build.** The same experiments show the same structure with
smaller effects.

* Fixed vs random (B): 2 of 50 rows
  (`sha256/len=1` (8.3), `chain_blocks/n=35,steps=0..15` (6.1)); in the corrected design (F)
  1 (`sha256/len=1` (6.7)). Of the
  hash-level rows only bare `sha256` on a one-byte message is flagged;
  `compress`, `thash_short`, `chain_blocks` and `fors_node`, which are flagged
  in the default build, are not (in the diagnostics FR and FR/same are below
  3 for every row but `sha256/len=1`).
* The all-zero value: zero vs random (C) 10 of 50
  rows; zero vs fixed (H) 6
  (`sha256/len=55` (12.3), `sha256/len=119` (22.2), `sha256/len=560` (8.0), `thash_short/len=16` (8.0), `thash/len=16` (5.7), `fors_sk_gen` (21.7)). Here the all-zero value is distinguishable
  also where it is a 16-byte value inside a PRF or F input: `fors_sk_gen`
  with an all-zero SK.seed is about 0.08% slower than with another fixed
  SK.seed (max |t| 22 in H, 29 in the diagnostics), `thash_short/len=16`
  likewise (8 and 12). At 27 ns per call and 1024 calls per measurement that
  is about 25 ns per measurement.
* With `PSTATE.DIT = 1`: the standard design (D) flags
  `chain_blocks/n=35,steps=0..d_i` (5.9), `chain_blocks/n=128,steps=t_i..t_i+1` (6.0), multi-block rows again; the follow-up
  shows the same harness artefact as in the default build (flagged in the
  standard design in both seeds, with and without DIT; not flagged with the
  same preparation, nor fixed vs fixed, nor random vs random). On these
  multi-block rows the all-zero value is *not* distinguishable from another
  fixed value in this build.
  The corrected design (G) flags 0 of 50 rows,
  and in the diagnostics every DIT column is below 4.5 except that
  standard-design one on the multi-block rows. DIT costs
  -4% to 25% in speed.

**Reading.** The mechanism inside the core was not identified. A processor
that predicts or caches values it has seen (and treats zeros specially), and
whose data-independent-timing mode switches that off, would produce exactly
this pattern: differences only when one class repeats a value or is all
zeros, none between two unrelated values, none with DIT on. That is an
inference from the observations above, not a measurement of the mechanism.

**What it means for the crate.**

* The compiled code of both builds is constant-time in the model the crate
  can control: instruction and address sequences do not depend on secrets.
* On this CPU, with DIT off, the time that code takes is nevertheless not
  independent of the data it processes. For the values that occur as secrets
  in SLH-DSA (uniformly random 16-byte strings, each hashed together with a
  different address) the tests above found a dependence only on whether a
  value repeats within a micro-benchmark, and none between different values;
  for an all-zero hash input (in the hw-sha2 build also an all-zero 16-byte
  secret inside one) they found a dependence on the value. Whole signing and
  the rows at the level of WOTS+, XMSS, FORS above the leaves and key
  generation showed no difference in any design (D1, D3).
* The crate does not set DIT, and its default build cannot (`msr DIT` needs
  `unsafe`). A caller that wants the platform's guarantee of
  data-independent timing has to enable DIT around secret-key operations
  (`msr DIT, #1` or the platform API). With DIT on, none of the 50 component
  rows of either build shows a difference in the corrected design. That is a
  deployment recommendation; nothing in `rust/src` can remove the effect.

### D3. Whole signing (`out/*/dudect_sign_*.md`)

default build:

| function | calls/meas. | n (class 0 / 1) | median class 0 (ns/call) | trimmed mean diff (ns) | rel. | t | max abs t | null abs t (cls 1 / cls 0) | std err of mean diff (ns) | > 4.5? |
|---|---|---|---|---|---|---|---|---|---|---|
| slh::slh_sign_internal (m, PK.seed fixed; honest keys) | 1 | 283 / 317 | 307267791.7 | +239144.603 | +0.0781% | +1.00 | 2.10 (crop 17) | 2.18 / 2.46 | 252374.614 | no |
| slh::slh_sign_internal (m, whole key fixed) | 1 | 297 / 303 | 305866875.0 | +8766.288 | +0.0029% | +0.05 | 1.41 (crop 16) | 2.19 / 1.93 | 239082.976 | no |
| slh::slh_sign_internal_checked (m, PK.seed fixed; honest keys) | 1 | 283 / 317 | 573686583.3 | +737015.701 | +0.1287% | +0.91 | 2.23 (crop 32) | 2.35 / 1.73 | 814661.539 | no |
| slh::slh_sign_internal_checked (m, whole key fixed) | 1 | 297 / 303 | 572233708.3 | -261608.982 | -0.0458% | -1.51 | 2.64 (crop 2) | 2.08 / 2.08 | 572542.718 | no |

hw-sha2 build:

| function | calls/meas. | n (class 0 / 1) | median class 0 (ns/call) | trimmed mean diff (ns) | rel. | t | max abs t | null abs t (cls 1 / cls 0) | std err of mean diff (ns) | > 4.5? |
|---|---|---|---|---|---|---|---|---|---|---|
| slh::slh_sign_internal (m, PK.seed fixed; honest keys) | 1 | 283 / 317 | 30761375.0 | +28206.181 | +0.0919% | +1.29 | 2.14 (crop 48) | 0.74 / 1.07 | 14555.785 | no |
| slh::slh_sign_internal (m, whole key fixed) | 1 | 297 / 303 | 30750833.3 | -1622.790 | -0.0053% | -0.23 | 1.82 (crop 10) | 2.22 / 1.09 | 8541.185 | no |
| slh::slh_sign_internal_checked (m, PK.seed fixed; honest keys) | 1 | 283 / 317 | 57533958.3 | +1947.301 | +0.0034% | -0.78 | 2.18 (crop 2) | 1.47 / 1.83 | 9643.644 | no |
| slh::slh_sign_internal_checked (m, whole key fixed) | 1 | 297 / 303 | 57543416.7 | -773.376 | -0.0013% | -0.14 | 2.82 (crop 10) | 1.32 / 1.46 | 10060.276 | no |

Class designs and what they show:

* *honest keys*: M and PK.seed shared; class 0 = one fixed honest key
  (SK.seed, SK.prf, PK.root = root of SK.seed) with one fixed addrnd; class 1
  = a fresh honest key and addrnd for every signature (key generation happens
  outside the timed region). Changing SK.seed necessarily changes PK.root and
  the whole public transcript, so the two classes differ in public data as
  well as in secrets. The test is still meaningful because T5 shows the
  amount of work is transcript-independent to within about 1e-6 (default)
  and 1e-5 (hw-sha2) of the instruction count: under the audit's claim total
  time has the same distribution in both classes, so a significant difference
  would indicate either a secret-dependent amount of work or a value-dependent
  timing effect at scale.
* *whole key fixed*: class 0 = fixed addrnd, class 1 = fresh addrnd (hedged
  signing randomness is secret until R is published; R itself is public).
* Outcome: no row above 4.5 in either build, for the plain and the checked
  signer (largest max |t| 2.64 in the default build,
  2.82 in the hw-sha2 build), all with
  `PSTATE.DIT = 0`.
* Resolution. default build: `slh::slh_sign_internal (m, PK.seed fixed; honest keys)`: standard error of the difference of class means 0.252 ms = 0.082% of the 307.3 ms signing time; `slh::slh_sign_internal (m, whole key fixed)`: standard error of the difference of class means 0.239 ms = 0.078% of the 305.9 ms signing time; `slh::slh_sign_internal_checked (m, PK.seed fixed; honest keys)`: standard error of the difference of class means 0.815 ms = 0.142% of the 573.7 ms signing time; `slh::slh_sign_internal_checked (m, whole key fixed)`: standard error of the difference of class means 0.573 ms = 0.100% of the 572.2 ms signing time. hw-sha2 build:
  `slh::slh_sign_internal (m, PK.seed fixed; honest keys)`: standard error of the difference of class means 0.015 ms = 0.047% of the 30.8 ms signing time; `slh::slh_sign_internal (m, whole key fixed)`: standard error of the difference of class means 0.009 ms = 0.028% of the 30.8 ms signing time; `slh::slh_sign_internal_checked (m, PK.seed fixed; honest keys)`: standard error of the difference of class means 0.010 ms = 0.017% of the 57.5 ms signing time; `slh::slh_sign_internal_checked (m, whole key fixed)`: standard error of the difference of class means 0.010 ms = 0.017% of the 57.5 ms signing time. A mean shift below roughly 4.5 times that
  would not reach the threshold. A pass here says nothing about leaks that
  reorder work without changing its amount; those are covered by T4, not by
  total time.

### What a timing pass does and does not mean

A row below 4.5 means: with this many samples on this machine under this
load, the *mean* (and cropped means) of the execution time did not differ
detectably between the two classes. It does not bound leakage observable by a
stronger adversary (per-instruction power/EM, cache-line probing from a
co-located process, speculative-execution gadgets), it only tests two
classes, and desktop timing noise can hide small effects (the "std err"
column is what each row could resolve). And as section D2 shows, a row above
4.5 in the fixed-vs-random design need not come from the code under test: it
can come from the CPU treating repeated data differently, or from the harness
preparing the two classes differently. The dudect results are therefore
supporting evidence; the trace comparison in section 1 is the primary
evidence for the code, and the timing section's main result is about the
platform.

## 4. Limitations

* **One compiler, one target, one profile, two feature sets.** rustc 1.100.0 /
  LLVM 23.1.5, `aarch64-apple-darwin`, default release profile. A different
  rustc/LLVM version, `opt-level`, LTO setting, `target-cpu`, or target
  (x86-64, other Arm cores, bare-metal) can compile the same source
  differently (e.g. turn a `csel` into a branch, vectorise, or call
  `memcmp`); the experiments must be rerun per configuration. The code traced
  is the native macOS build (object code verified identical to the main
  crate's release build), not a rebuild.
* **`#[inline]` functions.** `compress`, `compress_portable`, `short_block`,
  `pair_block`, `trunc`, `value` and the hw-sha2 kernels have no out-of-line
  copy; they are tested as inlined into the crate's out-of-line functions.
  The one row that calls `compress` directly traces a copy inlined into the
  harness wrapper.
* **Sampling, not exhaustion.** Dozens of secret pairs per row, a handful of
  public configurations per row (up to 16 for the scheduling rows), 8 to 16
  public configurations for whole signing. Trace equality on samples cannot
  exclude a divergence on rare inputs; for this code that would require a
  data-dependent branch or address that the static reading and the Lean
  argument say does not exist.
* **What the emulator does not see.** Caches, TLB, branch/value predictors,
  prefetchers, speculation and transient execution, micro-op timing of
  individual instructions (Unicorn is a functional emulator: all instructions
  "take" the same time, including the SHA-256 instructions, whose
  data-independent timing on real cores is a property of the CPU, see DIT
  below), frequency scaling, interrupts. The trace model is exactly: executed
  PC sequence + data addresses + sizes.
* **Stubbed library code.** `malloc/calloc/realloc/free/posix_memalign` are
  replaced by a deterministic size-class allocator in the tracer, and
  `memcpy/memmove/memset/bzero` by host-side stubs; the real libSystem
  implementations were not traced. Their behaviour is assumed to depend only
  on (pointers, lengths), which *are* recorded and compared (sizes and
  lengths were identical across secrets everywhere), and on allocator state
  driven by the same call sequence. `memcmp/bcmp` would have aborted the run;
  it is never reached from the tested functions and is not called by the
  crate's code at all. Rust's own allocation glue (`__rust_alloc`, `RawVec`
  growth) is inside the image and was traced.
* **Block granularity of control flow.** Unicorn reports translated blocks;
  the PC sequence inside a block is implied. Block boundaries come from
  Unicorn's translator, which cannot cause a missed divergence, only a
  different event count.
* **Declassification-pinned signing test.** Depends on locating five
  functions as out-of-line symbols and on the result-pointer return
  convention of this build; both are checked in every configuration against
  natively recomputed values. It tests "the trace depends on secrets only via
  the pinned values"; that the pinned values are public is checked for the
  honest run A by recomputing them the way a verifier does.
* **Unwinding paths** (bounds-check panics, allocation failure, `ctx` longer
  than 255 bytes returning `None`) are never taken with valid inputs and were
  not explored. The `None` result of the checked signer on a disagreement
  (a fault, or a key that key generation does not produce) was exercised only
  by the unpinned control runs, whose traces are not compared with anything.
* **Verification functions** (`slh_verify*`, `ht_verify`, which ends in a
  comparison of public values) handle only public data and were not tested as
  secret-handling code; `fors_pk_from_sig`/`xmss_pk_from_sig` are exercised
  inside signing (T4) and on their own (T1b).
* **The `hw-sha2` fallback.** On a CPU without the SHA-256 instructions the
  hw-sha2 build falls back to the portable code at run time; on
  `aarch64-apple-darwin` the test is a compile-time constant and the fallback
  is not reachable, so it was not traced (`chain_blocks_portable` of the
  hw-sha2 build was traced directly, with the hardware single-block
  compression inlined into it).
* **Zeroisation is out of scope.** Whether SK.seed/SK.prf copies, FORS/WOTS+
  secret values and intermediate buffers are wiped from the stack or from
  freed heap blocks is not tested by this harness.
* **DIT is not set by the crate**; see section 3.
* **Timing tests.** No core pinning, shared machine, 41.67 ns clock
  granularity (hence batching, which repeats one input up to 16384 times per
  measurement and so itself creates the repetition the CPU reacts to), two
  classes only, first-order (mean) test only, `max` over 101 croppings, half
  the default number of measurements in the component runs. Runs F-H (and the last two runs of the default build's multi-block
  follow-up) were measured while a second timing process of this harness (the
  end of the hw-sha2 run E, then the hw-sha2 diagnostics) was running on
  another core; nothing else of the harness ran during timing. The default build's runs A-E and its ten-row diagnostics were
  measured with a `dudect` binary built before a fix of the whole-signing mode
  (sha256 `3b99ae6f...`; the fix sets the context length of the input, which
  that mode had left random, and does not touch the component mode);
  `build.txt` lists the final binaries, which measured everything else. What
  the all-zero value has that other values lack, and at which granularity,
  was not investigated.

## 5. Reproduction

`./run.sh all` for the trace and static experiments of both builds, then the
timing steps on an idle machine (see README.md). Seeds are fixed (`cttrace`
default seed 0x5148445341, `dudect` default seed 0xD0DEC7), so the trace
experiments are exactly reproducible on the same toolchain; timing numbers
will vary run to run.

Wall-clock times of the runs recorded here (8 threads for the trace
experiments, one for timing): component traces 3 min (default) and 1 min (hw-sha2); pinned signing, eight
entry points, 35 min (default) and 40 min (hw-sha2, with more configurations
and memory tracing throughout); profiles about 1 min; disassembly seconds.
Timing, per build: runs A-E about 30 min, F-H 9 to 13 min, whole signing 19
min (default) and 2 min (hw-sha2), the ten-row diagnostics about 25 min, the
multi-block follow-up about 13 min.

## Historical note (2026-11-20)

The first version of this harness and of this file was made on 2026-11-20
for an earlier version of the crate (per-call `thash` on heap buffers,
`wots::chain`, HMAC through `hmac_sha256`, no checked signer, no `api` module,
no `hw-sha2` backend). Its results (43 component rows and 44 pinned
whole-signature pairs identical, all controls detected; a small timing effect
on bare SHA-256 with a repeated message that vanished with `PSTATE.DIT = 1`)
are in the git history of this directory (commit d2a5a9b) and say nothing
about the code tested here, which was compiled from different sources;
nothing in the sections above is carried over from them.
