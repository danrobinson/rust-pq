# Binary-level constant-time evidence for `slhdsa` (SLH-DSA-SHA2-128s): results

*This file is generated from `scripts/RESULTS.template.md` and the raw outputs
in `out/` by `scripts/make_results.py`. The prose describes the runs of
2026-11-20; if you rerun and regenerate, re-read the prose against the new
numbers.*

**Status: evidence, not proof.** Everything below is testing of one compiled
artefact on one machine. The source-level noninterference argument is the
separate Lean effort; this document only checks what rustc actually emitted.

## Environment

| | |
|---|---|
| Date | 2026-11-20 |
| Machine | Apple M5 Ultra (12 performance + 24 efficiency cores), 512 GB |
| OS | macOS 27.2 (26B118), Darwin 27.2.0, arm64 |
| Compiler | rustc 1.100.0 (0ef1bc386 2026-11-09), LLVM 23.1.5, host/target `aarch64-apple-darwin` |
| Flags | default cargo `release` profile: `opt-level=3`, no LTO, `codegen-units=16`, `panic=unwind`, no `RUSTFLAGS`, no `target-cpu` override |
| Emulator | Unicorn 2.1.4 (`libunicorn.2.dylib` from the PyPI wheel), CPU model `max` |
| Crate under test | `../src` as of 2026-11-20 (unmodified); `cargo test --release` in `..` passes (6/6 tests) and does not build this package |

**The traced code is the native code.** `cttrace` executes its own Mach-O
image inside the emulator, so no bare-metal rebuild is involved. In addition,
`scripts/disasm_check.py` compared the `slhdsa` object code inside this
package's dependency rlib with the rlib produced by `cargo test --release` in
`..`: **31 functions identical instruction-for-instruction (incl. relocation targets), 0 different, 0 present in only one; 4171 disassembly lines (instructions + relocation records) compared in A.**

## Summary

| # | Experiment | What was compared | Trials | Outcome |
|---|---|---|---|---|
| T1 | Component traces, secret varied (Unicorn; control flow + memory addresses + call-outs) | full event sequence between runs with identical public inputs and different secrets, 43 function/parameter rows | 2574 secret pairs | **all identical, 0 divergences** |
| T2 | Positive controls (leaky code in the harness) | same checker | 3 controls, 194 pairs | **all 3 detected** (145 pairs differ: control-flow and memory-address leaks; the remaining pairs are secrets that happen to take the same path) |
| T3 | Public-variation controls | same checker, a public input varied | 3 controls, 100 pairs | **100/100 differ**, as they must |
| T4 | Whole `slh_sign_internal`, declassified values pinned (control flow + memory addresses) | run B (fresh SK.seed, SK.prf, addrnd) vs run A, with R, PK_FORS and the 7 XMSS roots forced to A's values | 8 public configs x 4 secret sets = 32 pairs, ~1.6e10 instructions and ~3.9e9 events per run | **32/32 identical**; 16/16 unpinned controls differ |
| T5 | Whole `slh_sign` (with context), pinned, control flow only | as T4 | 4 x 3 = 12 pairs | **12/12 identical**; 8/8 unpinned controls differ |
| T6 | Whole-signature unconditioned profile | 24 honest random keys, fixed m and PK.seed | 24 runs | SHA-256/`thash`/allocator call counts constant; instruction count spread 44 out of 1.6e10 |
| S1 | Static disassembly | all 27 `slhdsa` functions in the binary | 3509 instructions | no integer division, no SHA/AES crypto-extension instruction, no indirect branch, SHA-256 rounds not vectorised, `K[i]`/`w[i]` indexed by the loop counter only |
| D1 | dudect timing, SLH-DSA-level components (`thash`, `prf_msg`, `chain`, `wots_*`, `xmss_*`, `fors_*`, keygen), secret = SK.seed / SK.prf / addrnd / chain value / hash input | fixed vs random secret, public inputs shared | 3 runs of 29 rows, 600 to 400k measurements per row | rows above 4.5 -- fixed pseudo-random secret: **none** (largest 3.04); same with DIT=1: **none** (largest 3.31); all-zero fixed secret: `thash/len=32` (7.58 (crop 12)), `thash/len=224` (9.84 (crop 14)) (multi-byte all-zero `thash` inputs only, intermittent; see D2) |
| D2 | dudect timing, bare `sha256` / `hmac_sha256` on fully secret messages | fixed vs random message | 13 rows x several runs | **|t| > 4.5 in many rows** when one message is repeated (strongest for the all-zero message); effect size <= 0.13% of the call time. Not present between two different fixed messages, not present with `PSTATE.DIT=1`. See "Timing finding" below |
| D3 | dudect timing, whole `slh_sign_internal` | fixed vs random (key, addrnd), and fixed key with fixed vs random addrnd | 2 x 600 signatures | no difference detected (weak: see resolution) |
| D4 | dudect positive controls | `leaky_cmp`, `leaky_loop` | 2 controls x 3 runs | detected every time (max |t| from 215 to 3313) |

**No secret-dependent divergence was found in the compiled code** (control
flow, memory addresses, allocation sizes, copy lengths). The one non-clean
result is a small, purely microarchitectural timing effect on bare SHA-256
that disappears when the CPU's data-independent-timing mode is enabled; it is
not something a source or compiler change in `rust/src` can remove.

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
the code faithfully.

For each row: the public inputs (PK.seed, ADRS, indices, lengths, public
messages) are pseudo-random but fixed per "public config"; the varied input is
redrawn for every pair. A pair = (reference run, run with a different secret);
the first pair of every public configuration uses the all-zero value for the
varied bytes, the others fresh pseudo-random values. (T4-T6 were run with the
harness binary as it was before that all-zero pair was added to T1-T3; the
`slhdsa` rlib linked in is the same.)

### T1-T3. Components and controls (`out/trace_components.md`)

| function (public params) | varied input | public configs | pairs | identical traces | differing | insns/run | blocks/run | mem accesses/run | call-outs/run | emu==native output | verdict |
|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 1 | 65 | 65 | 0 | 4195 | 368 | 875 | 6 | yes | PASS (all identical) |
| sha256/len=16 | all message bytes | 1 | 65 | 65 | 0 | 3991 | 322 | 790 | 5 | yes | PASS (all identical) |
| sha256/len=55 | all message bytes | 1 | 65 | 65 | 0 | 3548 | 231 | 608 | 4 | yes | PASS (all identical) |
| sha256/len=56 | all message bytes | 1 | 65 | 65 | 0 | 7435 | 547 | 1318 | 5 | yes | PASS (all identical) |
| sha256/len=64 | all message bytes | 1 | 65 | 65 | 0 | 7302 | 517 | 1260 | 4 | yes | PASS (all identical) |
| sha256/len=119 | all message bytes | 1 | 65 | 65 | 0 | 6752 | 408 | 1040 | 4 | yes | PASS (all identical) |
| sha256/len=120 | all message bytes | 1 | 65 | 65 | 0 | 10586 | 710 | 1724 | 4 | yes | PASS (all identical) |
| sha256/len=256 | all message bytes | 1 | 65 | 65 | 0 | 16914 | 1048 | 2556 | 4 | yes | PASS (all identical) |
| sha256/len=560 | all message bytes | 1 | 65 | 65 | 0 | 29250 | 1660 | 4092 | 4 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 1 | 65 | 65 | 0 | 16159 | 1399 | 3228 | 21 | yes | PASS (all identical) |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 1 | 65 | 65 | 0 | 22667 | 1773 | 4132 | 21 | yes | PASS (all identical) |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 1 | 65 | 65 | 0 | 19729 | 1686 | 3836 | 21 | yes | PASS (all identical) |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 1 | 65 | 65 | 0 | 16484 | 1476 | 3368 | 21 | yes | PASS (all identical) |
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 7275 | 501 | 1285 | 9 | yes | PASS (all identical) |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 7115 | 469 | 1221 | 9 | yes | PASS (all identical) |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 36506 | 2172 | 5332 | 10 | yes | PASS (all identical) |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 4 | 68 | 68 | 0 | 16802 | 1014 | 2548 | 10 | yes | PASS (all identical) |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 16445 | 1457 | 3359 | 23 | yes | PASS (all identical) |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 16207 | 1409 | 3264 | 25 | yes | PASS (all identical) |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 19371 | 1578 | 3680 | 25 | yes | PASS (all identical) |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 4 | 68 | 68 | 0 | 68031 | 4353 | 10400 | 25 | yes | PASS (all identical) |
| chain/i=0,s=15 | start value x | 4 | 68 | 68 | 0 | 108983 | 7505 | 19109 | 135 | yes | PASS (all identical) |
| chain/i=0,s=1 | start value x | 4 | 68 | 68 | 0 | 7315 | 505 | 1329 | 9 | yes | PASS (all identical) |
| chain/i=3,s=7 | start value x | 4 | 68 | 68 | 0 | 50887 | 3505 | 8949 | 63 | yes | PASS (all identical) |
| chain/i=15,s=0 | start value x | 4 | 68 | 68 | 0 | 47 | 5 | 54 | 0 | yes | PASS (all identical) |
| chain/i=0,s=0 | start value x | 4 | 68 | 68 | 0 | 47 | 5 | 54 | 0 | yes | PASS (all identical) |
| wots_pk_gen | SK.seed | 4 | 68 | 68 | 0 | 4102897 | 281796 | 716871 | 5058 | yes | PASS (all identical) |
| wots_sign | SK.seed (message m public, fixed) | 8 | 72 | 72 | 0 | 2653109 | 182979 | 464417 | 3303 | yes | PASS (all identical) |
| xmss_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 4102922 | 281800 | 716897 | 5058 | yes | PASS (all identical) |
| xmss_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 8213146 | 564108 | 1435078 | 10128 | yes | PASS (all identical) |
| xmss_node/z=2 | SK.seed | 4 | 68 | 68 | 0 | 16433594 | 1128724 | 2871440 | 20268 | yes | PASS (all identical) |
| xmss_node/z=3 | SK.seed | 2 | 34 | 34 | 0 | 32874490 | 2257956 | 5744164 | 40548 | yes | PASS (all identical) |
| xmss_node/z=4 | SK.seed | 2 | 34 | 34 | 0 | 65756282 | 4516420 | 11489612 | 81108 | yes | PASS (all identical) |
| xmss_sign | SK.seed (m, idx public, fixed) | 2 | 18 | 18 | 0 | 2102476069 | 144407798 | 367367034 | 2593425 | yes | PASS (all identical) |
| fors_sk_gen | SK.seed | 4 | 68 | 68 | 0 | 7294 | 502 | 1302 | 9 | yes | PASS (all identical) |
| fors_node/z=0 | SK.seed | 4 | 68 | 68 | 0 | 14578 | 1006 | 2587 | 18 | yes | PASS (all identical) |
| fors_node/z=1 | SK.seed | 4 | 68 | 68 | 0 | 36459 | 2520 | 6459 | 48 | yes | PASS (all identical) |
| fors_node/z=3 | SK.seed | 4 | 68 | 68 | 0 | 167745 | 11604 | 29691 | 228 | yes | PASS (all identical) |
| fors_node/z=6 | SK.seed | 4 | 68 | 68 | 0 | 1393081 | 96388 | 246523 | 1908 | yes | PASS (all identical) |
| fors_node/z=12 | SK.seed | 2 | 18 | 18 | 0 | 89617273 | 6200836 | 15858427 | 122868 | yes | PASS (all identical) |
| fors_sign | SK.seed (md public, fixed) | 2 | 18 | 18 | 0 | 1253313492 | 86719802 | 221780489 | 1718025 | yes | PASS (all identical) |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 2 | 26 | 26 | 0 | 2104427421 | 144541190 | 367707462 | 2595828 | yes | PASS (all identical) |
| slh_keygen_internal/all-inputs | SK.seed, SK.prf and PK.seed | 1 | 13 | 13 | 0 | 2104427421 | 144541190 | 367707462 | 2595828 | yes | PASS (all identical) |
| fors_sign, PUBLIC md varied (informational) | public digest md (SK.seed fixed) | 1 | 5 | 5 | 0 | 1253313492 | 86719802 | 221780489 | 1718025 | yes | PASS (all identical) |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 1 | 65 | 32 | 33 | 15 | 2 | 5 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_table (secret-indexed lookup) | secret index (leaky by construction) | 1 | 64 | 0 | 64 | 14 | 1 | 7 | 0 | yes | PASS (control: difference detected) |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 1 | 65 | 17 | 48 | 11331 | 827 | 2096 | 12 | yes | PASS (control: difference detected) |
| CONTROL wots_sign, PUBLIC m varied | public message m (chain lengths are public) | 2 | 34 | 0 | 34 | 2217388 | 152979 | 388277 | 2763 | yes | PASS (control: difference detected) |
| CONTROL chain, PUBLIC s varied | public step count s | 1 | 33 | 0 | 33 | 181603 | 12505 | 31809 | 225 | yes | PASS (control: difference detected) |
| CONTROL sha256, PUBLIC length varied | public message length (0..255) | 1 | 33 | 0 | 33 | 10246 | 642 | 1588 | 4 | yes | PASS (control: difference detected) |

Divergence details (first differing pair of each row):

- `CONTROL leaky_cmp (early-exit compare of secret)`: first divergence at event #5: last common event: read 0x50007ffefb (size/arg 1) in basic block ct_evidence::w_leaky_cmp+0x0; A: exec block ct_evidence::w_leaky_cmp+0x6c (size/arg 16) in basic block ct_evidence::w_leaky_cmp+0x6c | B: exec block ct_evidence::w_leaky_cmp+0x2c (size/arg 36) in basic block ct_evidence::w_leaky_cmp+0x2c
- `CONTROL leaky_table (secret-indexed lookup)`: first divergence at event #6: last common event: read 0x50007ffef8 (size/arg 8) in basic block ct_evidence::w_leaky_table+0x0; A: read 0x102764aa7 (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0 | B: read 0x102764a00 (size/arg 1) in basic block ct_evidence::w_leaky_table+0x0
- `CONTROL leaky_loop (secret-dependent iteration count)`: first divergence at event #12: last common event: write 0x50007ffeb8 (size/arg 8) in basic block ct_evidence::w_leaky_loop+0x0; A: exec block ct_evidence::w_leaky_loop+0x30 (size/arg 28) in basic block ct_evidence::w_leaky_loop+0x30 | B: exec block ct_evidence::w_leaky_loop+0x5c (size/arg 24) in basic block ct_evidence::w_leaky_loop+0x5c
- `CONTROL wots_sign, PUBLIC m varied`: first divergence at event #2551: last common event: write 0x50007ffdb8 (size/arg 8) in basic block slhdsa::wots::wots_sign+0x98; A: exec block slhdsa::wots::wots_sign+0xac (size/arg 44) in basic block slhdsa::wots::wots_sign+0xac | B: exec block slhdsa::wots::wots_sign+0xec (size/arg 24) in basic block slhdsa::wots::wots_sign+0xec
- `CONTROL chain, PUBLIC s varied`: first divergence at event #37: last common event: write 0x50007ffe18 (size/arg 8) in basic block slhdsa::wots::chain+0x0; A: exec block slhdsa::wots::chain+0x30 (size/arg 64) in basic block slhdsa::wots::chain+0x30 | B: exec block slhdsa::wots::chain+0x84 (size/arg 32) in basic block slhdsa::wots::chain+0x84
- `CONTROL sha256, PUBLIC length varied`: first divergence at event #23: last common event: write 0x50007ffd60 (size/arg 8) in basic block slhdsa::sha256::sha256+0x0; A: exec block slhdsa::sha256::sha256+0x904 (size/arg 28) in basic block slhdsa::sha256::sha256+0x904 | B: exec block slhdsa::sha256::sha256+0x40 (size/arg 16) in basic block slhdsa::sha256::sha256+0x40

overall: ALL ROWS AS EXPECTED

What this establishes, for the tested inputs: the control flow and the
addresses/sizes of all memory accesses of the compiled `sha256`,
`hmac_sha256`, `thash`, `prf_msg`, `chain`, `wots_pk_gen`, `wots_sign`,
`xmss_node` (z = 0..4), `xmss_sign`, `fors_sk_gen`, `fors_node` (z up to 12),
`fors_sign` and the whole `slh_keygen_internal` (which is `xmss_node` at
z = 9) did not depend on the secret bytes, exactly as the source-level audit
claims. `slh_keygen_internal` was additionally run with PK.seed varied too
(12 pairs): identical, i.e. its trace is independent of all three inputs.
Extra observation: `fors_sign`'s trace is identical even across different
*public* digests (the FORS indices only flow into ADRS contents, never into a
branch or an address).

Controls: the checker flags an early-exit comparison (control-flow leak, first
divergence = a different basic block inside `w_leaky_cmp`), a secret-indexed
table lookup (same control flow, different *read address*, i.e. only the
memory hook can see it) and a secret-dependent loop count; and it reports
different traces when a public WOTS message, a public chain length or a public
message length is changed.

### T4-T5. Whole signing with the declassified values pinned (`out/trace_sign.md`, `out/trace_sign_ctx.md`)

One cannot fix the signature and vary the key. The audit's claim is that the
trace of `slh_sign_internal(m, sk, addrnd)` is a function of
(m, PK.seed, PK.root, signature); more precisely that secrets reach branches
and addresses only through `R`, `PK_FORS` and the seven XMSS roots (which
determine the digest, the indices and all WOTS digits), all of which the
verifier recomputes. That claim is directly testable: run A signs honestly
and the tracer records these nine 16-byte values when the functions producing
them return; run B has the same m, PK.seed, PK.root but fresh SK.seed, SK.prf
and addrnd, and the tracer overwrites the nine results with A's values. All
other data in run B (every FORS secret and node, every WOTS secret and chain
value, every Merkle node, the 7840-byte signature body) differ from run A.

| public config (m, PK.seed, key A) | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|
| 0 | 4 | 4 | 0 | 2/2 | 15985708289 | 3947647395 | PASS |
| 1 | 4 | 4 | 0 | 2/2 | 15985704919 | 3947646675 | PASS |
| 2 | 4 | 4 | 0 | 2/2 | 15985714613 | 3947648565 | PASS |
| 3 | 4 | 4 | 0 | 2/2 | 15985705000 | 3947646726 | PASS |
| 4 | 4 | 4 | 0 | 2/2 | 15985708298 | 3947647403 | PASS |
| 5 | 4 | 4 | 0 | 2/2 | 15985704922 | 3947646673 | PASS |
| 6 | 4 | 4 | 0 | 2/2 | 15985714630 | 3947648580 | PASS |
| 7 | 4 | 4 | 0 | 2/2 | 15985705003 | 3947646736 | PASS |

`slh_sign` (context wrapper, 17-byte context), control flow only:

| public config (m, PK.seed, key A) | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|
| 0 | 3 | 3 | 0 | 2/2 | 15985712086 | 1151666849 | PASS |
| 1 | 3 | 3 | 0 | 2/2 | 15985708818 | 1151666670 | PASS |
| 2 | 3 | 3 | 0 | 2/2 | 15985718413 | 1151667192 | PASS |
| 3 | 3 | 3 | 0 | 2/2 | 15985708858 | 1151666665 | PASS |

Sanity checks performed in every configuration (all passed): exactly nine
values recorded and nine pinned; the first recorded value equals the
signature's `R`; replaying A's values into A leaves trace and output
unchanged; B's signature body differs from A's; emulated output of A equals
the native signature; without pinning, B's trace differs from A's (the
"unpinned control" column), so the pinning is what makes them equal.

What this establishes: for 32 (resp. 12) pairs of unrelated secret sets, once
the nine public intermediate values are equal, the entire 1.6e10-instruction
execution is identical in control flow and (T4) in every memory address,
allocation size and copy length. What it does not establish: (i) that those
nine values are public -- that is the audit's argument (R is in the signature;
PK_FORS and the roots are recomputed by `slh_verify`); (ii) anything about
inputs not sampled. In run B the key is not a valid key pair (PK.root is A's)
and the output is not a valid signature; that is irrelevant to the property
tested, which is about which data the trace depends on. The hook points were
located through the symbols `slhdsa::hash::thash` and `slhdsa::hash::prf_msg`
(both out-of-line in this build) and the ADRS type/height passed to `thash`;
a build that inlines them would make the experiment report INCONCLUSIVE, not
pass.

### T6. Unconditioned profile of whole signing (`out/trace_sign_profile.md`)

- runs: 24 (run 0 = base key, others = fresh honest (SK.seed, SK.prf, addrnd), PK.seed and m fixed)
- distinct full control-flow traces: 24 (expected: all distinct, the public transcript differs)
- distinct executed-instruction counts: 19 (min 15985708271, max 15985708315, spread 44)
- distinct basic-block counts: 18
- distinct call-out (malloc/realloc/free/memcpy) counts: [19891227]
- distinct `thash` call counts: [2186220]
- distinct `sha256` call counts: [2186224]
- distinct block-execution histograms (multiset of executed blocks, order ignored): 24

So over random honest keys the *amount* of work is essentially constant
(every signature performs exactly the same number of SHA-256 computations and
allocator calls; the instruction count varies by a few dozen instructions,
presumably from public-data-dependent paths such as the left/right choice in
`climb` and how the 15 chain steps per WOTS digit are split between signing
and public-key recomputation -- this was not broken down further), while the *order* of work differs with the public transcript. This is
what makes a total-time measurement of signing (D3) meaningful at all.

## 2. Static facts about the native code (`out/disasm.md`)

#### Static summary of slhdsa functions in target/release/cttrace

| function | insns | conditional branches | indirect br/blr | udiv/sdiv | crypto-ext insns | SIMD/FP-register insns | csel-family |
|---|---|---|---|---|---|---|---|
| `slhdsa::slh::with_context` | 86 | 6 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::slh::slh_sign` | 47 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::util::base_2b` | 87 | 8 | 0 | 0 | 0 | 2 | 1 |
| `slhdsa::wots::wots_digits` | 141 | 8 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::wots::wots_pk_from_sig` | 150 | 11 | 0 | 0 | 0 | 13 | 0 |
| `slhdsa::wots::chain` | 41 | 2 | 0 | 0 | 0 | 10 | 0 |
| `slhdsa::sha256::hmac_sha256` | 136 | 13 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::sha256::sha256` | 642 | 85 | 0 | 0 | 0 | 9 | 0 |
| `<alloc::raw_vec instantiation in slhdsa> h` | 34 | 2 | 0 | 0 | 0 | 0 | 3 |
| `<alloc::raw_vec instantiation in slhdsa> h` | 25 | 1 | 0 | 0 | 0 | 0 | 1 |
| `<alloc::raw_vec instantiation in slhdsa> h` | 44 | 5 | 0 | 0 | 0 | 0 | 1 |
| `slhdsa::ht::ht_sign` | 100 | 6 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::slh::slh_sign_internal` | 171 | 12 | 0 | 0 | 0 | 7 | 0 |
| `slhdsa::slh::slh_keygen_internal` | 35 | 0 | 0 | 0 | 0 | 10 | 0 |
| `slhdsa::fors::fors_sk_gen` | 21 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::fors::fors_pk_from_sig` | 259 | 16 | 0 | 0 | 0 | 23 | 0 |
| `slhdsa::fors::fors_node` | 65 | 1 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::fors::fors_sign` | 138 | 9 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::hash::h_msg` | 184 | 11 | 0 | 0 | 0 | 17 | 0 |
| `slhdsa::hash::thash` | 151 | 6 | 0 | 0 | 0 | 21 | 0 |
| `slhdsa::hash::prf_msg` | 75 | 4 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::wots::wots_pk_gen` | 286 | 4 | 0 | 0 | 0 | 32 | 0 |
| `slhdsa::wots::wots_sign` | 135 | 9 | 0 | 0 | 0 | 15 | 0 |
| `slhdsa::xmss::xmss_pk_from_sig` | 75 | 3 | 0 | 0 | 0 | 4 | 1 |
| `slhdsa::xmss::hash2` | 68 | 3 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::xmss::xmss_node` | 55 | 1 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::xmss::xmss_sign` | 258 | 10 | 0 | 0 | 0 | 20 | 0 |
| **total** | 3509 | 239 | 0 | 0 | 0 | 215 | 7 |

SIMD/FP-register instructions used in slhdsa code (mnemonic: count): str: 79, ldr: 77, stp: 20, ldur: 17, stur: 6, ldp: 5, mov.s: 3, movi.2d: 2, ushl.4s: 2, dup.4s: 1, zip1.4s: 1, uzp1.8h: 1, xtn.8b: 1

##### Conditional branches inside the compiled `sha256` (compress/schedule/pad are inlined into it)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.hs` | `cmp R, R` | forward | 64 |
| `b.ne` | `cmp R, R` | forward | 9 |
| `cbz` | `cbz R` | forward | 3 |
| `cbnz` | `cbnz R` | forward | 1 |
| `b.ne` | `cmp R, #0x38` | forward | 1 |
| `b.eq` | `cmp R, R` | forward | 1 |
| `b.eq` | `cmp R, #0x38` | forward | 1 |
| `b.ne` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `subs R, R, #0x1` | backward (loop) | 1 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 1 |
| `b.lo` | `cmp R, R` | backward (loop) | 1 |
| `b.eq` | `cmp R, R` | backward (loop) | 1 |

Register-indexed loads in `sha256` (base + index register):

- `ldr w10, [x20, x10]` x15
- `ldr w10, [x20, x0]` x1
- `ldr w30, [x9, x6]` x1
- `ldr w28, [x4, x6]` x1

#### Object-code comparison of slhdsa

- A: `target/release/build/slhdsa/71d522cffa462b8f/out/libslhdsa-71d522cffa462b8f.rlib`
- B: `../target/release/build/slhdsa/b5f420dc9e5ca955/out/libslhdsa-b5f420dc9e5ca955.rlib`


31 functions identical instruction-for-instruction (incl. relocation targets), 0 different, 0 present in only one; 4171 disassembly lines (instructions + relocation records) compared in A.

Reading of the compiled `sha256` (into which `pad`, `schedule` and `compress`
are inlined), 642 instructions:

* It is scalar code. The only SIMD-register instructions are 16-byte
  moves/zeroing (`movi`, `stp q0,q0` to clear `w`, `ldr/str q` copies); the
  crate's other SIMD uses are likewise 16-byte copies, plus one small
  vectorised shift-and-narrow sequence (`ushl.4s`, `uzp1`, `xtn`) in `thash`
  that serialises the public ADRS (`Adrs::compress`, inlined). No
  `sha256h`/`sha256su`
  (ARMv8 crypto extension) instructions are emitted, although the target has
  them; rustc does not pattern-match the portable code into them.
* The 64 forward `b.hs` after `cmp R, R` are the bounds checks of the 16
  unrolled big-endian word loads (index vs. padded length, both public; the
  branch targets are `panic_bounds_check`). The backward branches are the
  three loops: schedule expansion (`subs x11, x11, #1; b.ne`, 48 iterations),
  rounds (`cmp x6, #0x100; b.ne`, 64 iterations) and the per-block loop
  (`cmp x0, x1; b.lo`, offset vs. padded length), plus the padding loops
  (`cmp R, #0x38` is `len % 64 != 56`). No branch tests a message-derived or
  state-derived value.
* The round constant and schedule lookups are `ldr w30, [x9, x6]` (K) and
  `ldr w28, [x4, x6]` (w) with x6 the round counter times 4; the message loads
  are indexed by the public block offset. No table lookup is indexed by data.
* There is no integer division anywhere in the crate's code (`p.len() % 64`
  is an `and`), no indirect branch (no jump tables), and all `csel`-family
  uses (7) are in `base_2b`, `xmss_pk_from_sig`/`climb` and the `RawVec`
  growth code, on public digits/indices/capacities.

The T1 trace equality is the dynamic confirmation of these readings.

## 3. dudect-style timing tests

### Method and noise floor

Welch t-test between class 0 (one fixed secret) and class 1 (fresh
pseudo-random secret per measurement); all public inputs identical in both
classes; classes interleaved at random; inputs prepared outside the timed
region. Clock: `mach_absolute_time`, 41.67 ns per tick on this machine, so
short functions are called 4 to 8192 times per measurement (same input) to
make one measurement >= ~20 us; the "calls/meas." column gives the count and
all times are per call. Statistic: maximum |t| over the uncropped test and
the 100 dudect croppings (measurements above the pooled percentile
1 - 0.5^(10(i+1)/100) discarded). The conventional threshold is 4.5; because
it is a maximum over 101 correlated tests on up to 400k samples, values up to
about 3 occur under the null hypothesis: the two "null" columns give the same
statistic on label-shuffled splits *within* one class of the same data
(observed range over all component rows of the three runs: 0.50 to 3.03;
whole signing: up to 3.39), and the dedicated random-vs-random
experiments in `out/dudect_diag.md` do not exceed 3.60 in any of their
34 rows. "trimmed mean diff" is mean(class 0) -
mean(class 1) over the measurements below the pooled 90th percentile.

Nothing was pinned to a core (macOS offers no affinity API); the measuring
thread asks for `QOS_CLASS_USER_INTERACTIVE` to stay on performance cores.
The machine was otherwise lightly loaded but not idle (1-minute load average
between ~2 and ~9 during the day; other agents were working in the same
repository).

### D1/D2. Components, fixed class = one fixed pseudo-random secret (`out/dudect_components_fixed_random.md`)

`clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519`

| function | calls/meas. | n (class 0 / 1) | median class 0 (ns/call) | trimmed mean diff (ns) | rel. | t | max abs t | null abs t (cls 1 / cls 0) | > 4.5? |
|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | 128 | 199749 / 200251 | 201.5 | -0.107 | -0.0526% | -2.88 | 20.14 (crop 14) | 1.93 / 1.45 | **yes** |
| sha256/len=16 | 128 | 199758 / 200242 | 190.1 | -0.048 | -0.0251% | -0.74 | 6.28 (crop 4) | 1.04 / 1.36 | **yes** |
| sha256/len=55 | 128 | 200278 / 199722 | 166.3 | -0.066 | -0.0400% | -3.16 | 9.25 (crop 26) | 1.12 / 1.55 | **yes** |
| sha256/len=56 | 64 | 199812 / 200188 | 334.6 | +0.032 | +0.0094% | +1.07 | 2.57 (crop 7) | 0.95 / 1.71 | no |
| sha256/len=64 | 64 | 200507 / 199493 | 308.6 | +0.003 | +0.0009% | -0.34 | 7.12 (crop 10) | 1.86 / 2.20 | **yes** |
| sha256/len=119 | 64 | 200222 / 199778 | 304.0 | -0.037 | -0.0119% | -1.84 | 2.73 (crop 58) | 0.91 / 0.67 | no |
| sha256/len=120 | 64 | 200086 / 199914 | 454.4 | -0.040 | -0.0087% | +0.87 | 4.22 (crop 9) | 1.22 / 1.61 | no |
| sha256/len=256 | 32 | 199720 / 200280 | 785.2 | -0.321 | -0.0397% | -1.57 | 1.97 (crop 23) | 1.67 / 2.08 | no |
| sha256/len=560 | 16 | 199738 / 200262 | 1263.0 | -0.129 | -0.0099% | -0.07 | 1.84 (crop 8) | 1.07 / 1.34 | no |
| hmac_sha256/klen=16,mlen=32 | 32 | 100037 / 99963 | 804.7 | +0.054 | +0.0066% | +1.25 | 5.75 (crop 11) | 1.29 / 1.47 | **yes** |
| hmac_sha256/klen=16,mlen=150 | 8 | 100246 / 99754 | 1119.8 | -0.103 | -0.0091% | -0.21 | 2.24 (crop 0) | 1.56 / 0.90 | no |
| hmac_sha256/klen=64,mlen=64 | 32 | 100037 / 99963 | 950.5 | +0.146 | +0.0152% | +1.73 | 3.83 (crop 26) | 1.60 / 1.41 | no |
| hmac_sha256/klen=32,mlen=1 | 32 | 99718 / 100282 | 826.8 | +0.488 | +0.0584% | +0.60 | 3.30 (crop 22) | 0.94 / 2.61 | no |
| thash/len=16 | 64 | 199754 / 200246 | 378.9 | +0.020 | +0.0051% | +1.09 | 1.90 (crop 5) | 0.90 / 1.64 | no |
| thash/len=32 | 64 | 200044 / 199956 | 371.7 | -0.061 | -0.0168% | -1.61 | 2.65 (crop 0) | 1.83 / 1.23 | no |
| thash/len=560 | 16 | 200036 / 199964 | 1640.6 | +0.164 | +0.0099% | +0.70 | 1.68 (crop 67) | 2.34 / 1.93 | no |
| thash/len=224 | 32 | 200273 / 199727 | 799.5 | -0.071 | -0.0088% | -0.04 | 2.23 (crop 6) | 1.60 / 2.15 | no |
| prf_msg/mlen=0 | 32 | 100034 / 99966 | 890.6 | -0.203 | -0.0228% | -0.93 | 1.23 (crop 12) | 1.11 / 1.41 | no |
| prf_msg/mlen=32 | 32 | 99542 / 100458 | 833.3 | +0.163 | +0.0189% | +0.98 | 1.68 (crop 3) | 1.33 / 1.57 | no |
| prf_msg/mlen=100 | 32 | 100080 / 99920 | 979.2 | +0.037 | +0.0037% | +0.41 | 1.45 (crop 1) | 1.57 / 2.16 | no |
| prf_msg/mlen=1000 | 8 | 99874 / 100126 | 3072.9 | -0.272 | -0.0087% | -0.79 | 1.41 (crop 2) | 1.24 / 1.84 | no |
| chain/i=0,s=15 | 4 | 100153 / 99847 | 5364.6 | +0.996 | +0.0182% | +0.27 | 1.27 (crop 0) | 0.96 / 2.28 | no |
| chain/i=0,s=1 | 64 | 100553 / 99447 | 382.2 | -0.050 | -0.0128% | +0.06 | 2.68 (crop 3) | 1.76 / 0.85 | no |
| chain/i=3,s=7 | 8 | 100033 / 99967 | 2437.5 | -0.048 | -0.0020% | +2.05 | 2.52 (crop 99) | 1.45 / 2.20 | no |
| chain/i=15,s=0 | 8192 | 100283 / 99717 | 3.2 | -0.000 | -0.0104% | +0.81 | 2.15 (crop 36) | 1.44 / 1.65 | no |
| chain/i=0,s=0 | 8192 | 99782 / 100218 | 3.2 | +0.000 | +0.0093% | -0.76 | 1.73 (crop 37) | 1.60 / 1.50 | no |
| wots_pk_gen | 1 | 49955 / 50045 | 197958.3 | +51.151 | +0.0257% | -1.86 | 2.63 (crop 16) | 1.49 / 1.48 | no |
| wots_sign | 1 | 50105 / 49895 | 101000.0 | -21.772 | -0.0214% | -1.42 | 2.21 (crop 44) | 1.88 / 2.19 | no |
| xmss_node/z=0 | 1 | 10006 / 9994 | 199000.0 | -149.269 | -0.0745% | -0.79 | 2.15 (crop 5) | 1.12 / 1.13 | no |
| xmss_node/z=1 | 1 | 10033 / 9967 | 395250.0 | +222.135 | +0.0561% | +1.36 | 3.04 (crop 29) | 1.42 / 1.52 | no |
| xmss_node/z=2 | 1 | 3040 / 2960 | 787791.7 | -19.981 | -0.0025% | -0.28 | 1.90 (crop 23) | 1.13 / 1.95 | no |
| xmss_node/z=3 | 1 | 2947 / 3053 | 1579333.3 | +636.814 | +0.0403% | +0.28 | 1.65 (crop 32) | 1.17 / 1.41 | no |
| xmss_node/z=4 | 1 | 2988 / 3012 | 3169291.7 | -1089.811 | -0.0344% | +0.52 | 1.86 (crop 1) | 2.73 / 2.74 | no |
| xmss_sign | 1 | 492 / 508 | 102509875.0 | -4916.587 | -0.0048% | +0.38 | 1.51 (crop 1) | 3.03 / 2.16 | no |
| fors_sk_gen | 64 | 200547 / 199453 | 376.3 | +0.015 | +0.0039% | -0.64 | 1.28 (crop 7) | 1.43 / 1.44 | no |
| fors_node/z=0 | 32 | 100088 / 99912 | 707.0 | +0.221 | +0.0306% | +1.07 | 1.81 (crop 3) | 2.03 / 1.16 | no |
| fors_node/z=1 | 16 | 99737 / 100263 | 1815.1 | -0.112 | -0.0061% | -0.29 | 1.75 (crop 25) | 1.28 / 1.04 | no |
| fors_node/z=3 | 4 | 30094 / 29906 | 8395.8 | -5.221 | -0.0616% | -2.11 | 2.34 (crop 29) | 2.08 / 1.67 | no |
| fors_node/z=6 | 1 | 5083 / 4917 | 69000.0 | -4.499 | -0.0065% | -0.86 | 1.72 (crop 5) | 1.82 / 1.40 | no |
| fors_node/z=12 | 1 | 1985 / 2015 | 4473541.7 | -627.675 | -0.0140% | -0.93 | 2.36 (crop 16) | 1.65 / 2.93 | no |
| fors_sign | 1 | 299 / 301 | 62627416.7 | -120790.290 | -0.1920% | -1.90 | 2.39 (crop 53) | 1.92 / 1.67 | no |
| slh_keygen_internal | 1 | 1027 / 973 | 102588500.0 | -25677.032 | -0.0251% | -0.16 | 1.34 (crop 1) | 2.20 / 1.74 | no |
| CONTROL leaky_cmp (early-exit compare of secret) | 32 | 100383 / 99617 | 412.8 | +295.008 | +111.0316% | +216.33 | 875.00 (crop 6) | 0.89 / 1.19 | **yes** |
| CONTROL leaky_loop (secret-dependent iteration count) | 32 | 99785 / 100215 | 502.6 | -85.356 | -15.3730% | -215.06 | 215.34 (crop 99) | 1.99 / 1.06 | **yes** |

### D1/D2. Components, fixed class = all-zero secret (`out/dudect_components_fixed_zero.md`)

`clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = all-zero secret; seed 13688519`

| function | calls/meas. | n (class 0 / 1) | median class 0 (ns/call) | trimmed mean diff (ns) | rel. | t | max abs t | null abs t (cls 1 / cls 0) | > 4.5? |
|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | 128 | 199749 / 200251 | 206.4 | -0.122 | -0.0584% | -3.70 | 12.86 (crop 13) | 1.00 / 1.20 | **yes** |
| sha256/len=16 | 128 | 199758 / 200242 | 186.5 | -0.063 | -0.0333% | -1.23 | 25.56 (crop 12) | 1.44 / 1.55 | **yes** |
| sha256/len=55 | 128 | 200278 / 199722 | 163.1 | -0.211 | -0.1288% | -4.97 | 47.16 (crop 4) | 1.78 / 1.68 | **yes** |
| sha256/len=56 | 64 | 199812 / 200188 | 332.0 | -0.114 | -0.0338% | -1.14 | 38.14 (crop 10) | 1.72 / 1.01 | **yes** |
| sha256/len=64 | 64 | 200507 / 199493 | 308.6 | -0.161 | -0.0522% | -2.89 | 25.14 (crop 24) | 2.10 / 1.09 | **yes** |
| sha256/len=119 | 64 | 200222 / 199778 | 297.5 | -0.018 | -0.0060% | -0.56 | 20.95 (crop 20) | 0.97 / 1.34 | **yes** |
| sha256/len=120 | 64 | 200086 / 199914 | 451.2 | -0.209 | -0.0459% | -4.46 | 55.21 (crop 7) | 1.73 / 1.39 | **yes** |
| sha256/len=256 | 32 | 199720 / 200280 | 764.3 | -0.521 | -0.0675% | -2.60 | 24.23 (crop 6) | 1.38 / 1.62 | **yes** |
| sha256/len=560 | 16 | 199738 / 200262 | 1341.1 | -0.465 | -0.0347% | -3.53 | 20.68 (crop 3) | 0.96 / 0.93 | **yes** |
| hmac_sha256/klen=16,mlen=32 | 32 | 100037 / 99963 | 859.4 | +0.134 | +0.0154% | +1.18 | 1.61 (crop 25) | 1.55 / 1.51 | no |
| hmac_sha256/klen=16,mlen=150 | 8 | 100246 / 99754 | 1192.7 | -0.158 | -0.0131% | -1.88 | 4.89 (crop 21) | 0.73 / 1.33 | **yes** |
| hmac_sha256/klen=64,mlen=64 | 32 | 100037 / 99963 | 1028.6 | -0.736 | -0.0698% | +2.03 | 6.91 (crop 24) | 1.12 / 1.40 | **yes** |
| hmac_sha256/klen=32,mlen=1 | 32 | 99718 / 100282 | 885.4 | +0.031 | +0.0034% | -0.19 | 3.76 (crop 14) | 1.19 / 1.55 | no |
| thash/len=16 | 64 | 199754 / 200246 | 375.7 | +0.153 | +0.0392% | +1.76 | 3.29 (crop 14) | 0.71 / 1.29 | no |
| thash/len=32 | 64 | 200044 / 199956 | 371.7 | -0.250 | -0.0644% | -0.96 | 7.58 (crop 12) | 1.20 / 1.26 | **yes** |
| thash/len=560 | 16 | 200036 / 199964 | 1755.2 | +0.873 | +0.0493% | +1.16 | 2.84 (crop 30) | 0.94 / 1.40 | no |
| thash/len=224 | 32 | 200273 / 199727 | 809.9 | -0.038 | -0.0046% | -1.99 | 9.84 (crop 14) | 1.41 / 1.10 | **yes** |
| prf_msg/mlen=0 | 32 | 100034 / 99966 | 884.1 | -0.016 | -0.0018% | -0.43 | 2.50 (crop 6) | 0.92 / 0.59 | no |
| prf_msg/mlen=32 | 32 | 99542 / 100458 | 849.0 | -0.073 | -0.0085% | -0.96 | 1.49 (crop 15) | 0.95 / 1.50 | no |
| prf_msg/mlen=100 | 16 | 100080 / 99920 | 1000.0 | -0.292 | -0.0286% | -0.74 | 4.04 (crop 16) | 1.24 / 1.85 | no |
| prf_msg/mlen=1000 | 8 | 99874 / 100126 | 3109.4 | +0.019 | +0.0006% | -2.12 | 2.90 (crop 12) | 1.18 / 0.84 | no |
| chain/i=0,s=15 | 4 | 100153 / 99847 | 5197.9 | -0.492 | -0.0094% | -0.95 | 2.55 (crop 0) | 1.71 / 1.86 | no |
| chain/i=0,s=1 | 64 | 100553 / 99447 | 358.7 | -0.004 | -0.0011% | -0.80 | 1.44 (crop 64) | 1.06 / 1.35 | no |
| chain/i=3,s=7 | 8 | 100033 / 99967 | 2432.3 | -0.279 | -0.0113% | -0.31 | 2.62 (crop 28) | 1.19 / 1.89 | no |
| chain/i=15,s=0 | 8192 | 100283 / 99717 | 3.1 | +0.000 | +0.0019% | +0.47 | 0.81 (crop 1) | 1.78 / 2.38 | no |
| chain/i=0,s=0 | 8192 | 99782 / 100218 | 3.1 | +0.000 | +0.0048% | -0.36 | 2.16 (crop 2) | 1.49 / 2.04 | no |
| wots_pk_gen | 1 | 49952 / 50048 | 196541.7 | +59.110 | +0.0299% | +0.94 | 2.15 (crop 28) | 2.00 / 1.41 | no |
| wots_sign | 1 | 50105 / 49895 | 103000.0 | +7.411 | +0.0071% | -0.55 | 2.01 (crop 0) | 1.48 / 1.10 | no |
| xmss_node/z=0 | 1 | 10005 / 9995 | 195083.3 | -59.678 | -0.0305% | -1.76 | 2.10 (crop 47) | 2.05 / 1.70 | no |
| xmss_node/z=1 | 1 | 10033 / 9967 | 395083.3 | +45.993 | +0.0116% | +0.44 | 2.14 (crop 1) | 1.36 / 1.35 | no |
| xmss_node/z=2 | 1 | 3040 / 2960 | 803750.0 | -615.784 | -0.0762% | +0.21 | 2.10 (crop 0) | 2.40 / 2.19 | no |
| xmss_node/z=3 | 1 | 2947 / 3053 | 1581625.0 | +1225.936 | +0.0771% | -0.40 | 1.85 (crop 27) | 1.21 / 2.46 | no |
| xmss_node/z=4 | 1 | 2988 / 3012 | 3154958.3 | +197.999 | +0.0063% | -0.31 | 1.96 (crop 8) | 2.20 / 1.70 | no |
| xmss_sign | 1 | 492 / 508 | 106918666.7 | -221015.145 | -0.2093% | -2.05 | 2.18 (crop 71) | 1.67 / 1.24 | no |
| fors_sk_gen | 64 | 200547 / 199453 | 373.7 | -0.248 | -0.0659% | -2.65 | 4.10 (crop 28) | 1.78 / 1.25 | no |
| fors_node/z=0 | 32 | 100088 / 99912 | 714.8 | +0.253 | +0.0343% | +0.16 | 1.97 (crop 19) | 2.37 / 2.89 | no |
| fors_node/z=1 | 16 | 99737 / 100263 | 1895.8 | -0.215 | -0.0115% | -0.47 | 1.05 (crop 9) | 1.26 / 1.22 | no |
| fors_node/z=3 | 4 | 30094 / 29906 | 8218.8 | -1.537 | -0.0186% | +1.31 | 2.24 (crop 2) | 1.21 / 1.92 | no |
| fors_node/z=6 | 1 | 5083 / 4917 | 68291.7 | -43.622 | -0.0637% | -1.54 | 2.71 (crop 33) | 1.11 / 2.41 | no |
| fors_node/z=12 | 1 | 1985 / 2015 | 4477583.3 | +2111.909 | +0.0470% | -0.41 | 2.09 (crop 19) | 2.84 / 1.29 | no |
| fors_sign | 1 | 299 / 301 | 63818833.3 | +30177.487 | +0.0471% | -0.16 | 1.69 (crop 20) | 2.12 / 1.06 | no |
| slh_keygen_internal | 1 | 1027 / 973 | 103743000.0 | +152167.281 | +0.1461% | +1.54 | 2.13 (crop 4) | 1.80 / 1.54 | no |
| CONTROL leaky_cmp (early-exit compare of secret) | 32 | 100383 / 99617 | 3380.2 | +3181.536 | +176.3402% | +3136.25 | 3312.59 (crop 21) | 1.61 / 1.53 | **yes** |
| CONTROL leaky_loop (secret-dependent iteration count) | 32 | 99785 / 100215 | 1.3 | -616.934 | -198.8542% | -875.94 | 925.32 (crop 34) | 2.10 / 0.69 | **yes** |

### D1/D2. Components, fixed pseudo-random secret, `PSTATE.DIT = 1` (`out/dudect_components_fixed_random_DIT.md`)

`clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519`

| function | calls/meas. | n (class 0 / 1) | median class 0 (ns/call) | trimmed mean diff (ns) | rel. | t | max abs t | null abs t (cls 1 / cls 0) | > 4.5? |
|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | 64 | 199749 / 200251 | 242.8 | +0.006 | +0.0025% | +0.16 | 2.10 (crop 0) | 0.86 / 1.06 | no |
| sha256/len=16 | 128 | 199758 / 200242 | 228.5 | +0.019 | +0.0085% | -0.17 | 2.09 (crop 1) | 1.67 / 0.99 | no |
| sha256/len=55 | 128 | 200278 / 199722 | 196.0 | -0.013 | -0.0065% | -0.87 | 2.67 (crop 10) | 1.46 / 2.46 | no |
| sha256/len=56 | 64 | 199812 / 200188 | 404.3 | -0.027 | -0.0068% | +0.12 | 1.39 (crop 17) | 1.39 / 2.47 | no |
| sha256/len=64 | 64 | 200507 / 199493 | 380.9 | -0.001 | -0.0002% | -0.95 | 3.14 (crop 11) | 1.39 / 1.37 | no |
| sha256/len=119 | 64 | 200222 / 199778 | 371.7 | +0.037 | +0.0100% | -0.13 | 1.89 (crop 2) | 0.93 / 1.18 | no |
| sha256/len=120 | 64 | 200086 / 199914 | 554.7 | +0.034 | +0.0061% | -0.38 | 2.20 (crop 19) | 1.14 / 1.76 | no |
| sha256/len=256 | 32 | 199720 / 200280 | 910.2 | +0.102 | +0.0112% | +2.53 | 2.53 | 2.21 / 1.78 | no |
| sha256/len=560 | 16 | 199738 / 200262 | 1567.7 | -0.178 | -0.0114% | -0.79 | 2.18 (crop 0) | 0.78 / 1.05 | no |
| hmac_sha256/klen=16,mlen=32 | 32 | 100037 / 99963 | 967.4 | +0.060 | +0.0062% | +0.04 | 1.88 (crop 3) | 1.25 / 1.60 | no |
| hmac_sha256/klen=16,mlen=150 | 16 | 100246 / 99754 | 1398.4 | +0.312 | +0.0225% | +1.93 | 2.47 (crop 18) | 1.77 / 1.00 | no |
| hmac_sha256/klen=64,mlen=64 | 32 | 100037 / 99963 | 1156.2 | -0.016 | -0.0014% | +0.55 | 0.95 (crop 56) | 1.55 / 1.40 | no |
| hmac_sha256/klen=32,mlen=1 | 32 | 99718 / 100282 | 964.8 | +0.029 | +0.0030% | -0.51 | 2.10 (crop 40) | 1.43 / 1.53 | no |
| thash/len=16 | 64 | 199754 / 200246 | 416.0 | -0.008 | -0.0020% | -0.75 | 2.59 (crop 2) | 1.37 / 1.71 | no |
| thash/len=32 | 64 | 200044 / 199956 | 446.6 | +0.087 | +0.0198% | +1.38 | 1.95 (crop 87) | 0.50 / 0.97 | no |
| thash/len=560 | 8 | 200036 / 199964 | 1979.2 | -0.076 | -0.0038% | -0.58 | 2.24 (crop 0) | 1.37 / 1.41 | no |
| thash/len=224 | 32 | 200273 / 199727 | 946.6 | -0.060 | -0.0063% | -0.38 | 1.86 (crop 41) | 1.02 / 1.75 | no |
| prf_msg/mlen=0 | 32 | 100034 / 99966 | 985.7 | +0.044 | +0.0045% | +1.06 | 1.08 (crop 56) | 1.91 / 1.82 | no |
| prf_msg/mlen=32 | 32 | 99542 / 100458 | 987.0 | +0.106 | +0.0108% | +0.41 | 2.17 (crop 7) | 1.49 / 1.00 | no |
| prf_msg/mlen=100 | 32 | 100080 / 99920 | 1242.2 | +0.224 | +0.0182% | +0.98 | 1.93 (crop 63) | 0.65 / 0.96 | no |
| prf_msg/mlen=1000 | 8 | 99874 / 100126 | 3890.6 | +0.296 | +0.0078% | +0.05 | 1.77 (crop 15) | 1.39 / 1.31 | no |
| chain/i=0,s=15 | 4 | 100153 / 99847 | 6333.3 | +0.739 | +0.0117% | +0.37 | 2.36 (crop 0) | 1.73 / 2.14 | no |
| chain/i=0,s=1 | 64 | 100553 / 99447 | 419.3 | +0.008 | +0.0020% | +0.08 | 1.10 (crop 84) | 1.30 / 1.34 | no |
| chain/i=3,s=7 | 8 | 100033 / 99967 | 2906.2 | -0.073 | -0.0025% | -0.44 | 1.63 (crop 49) | 1.44 / 0.78 | no |
| chain/i=15,s=0 | 8192 | 100283 / 99717 | 4.0 | -0.000 | -0.0115% | -1.59 | 2.02 (crop 98) | 1.16 / 0.90 | no |
| chain/i=0,s=0 | 8192 | 99782 / 100218 | 3.7 | -0.000 | -0.0016% | -0.40 | 1.48 (crop 37) | 1.90 / 2.75 | no |
| wots_pk_gen | 1 | 49946 / 50054 | 238375.0 | -55.845 | -0.0233% | +0.26 | 1.55 (crop 35) | 0.92 / 1.01 | no |
| wots_sign | 1 | 50111 / 49889 | 121750.0 | -0.510 | -0.0004% | +1.64 | 1.95 (crop 53) | 1.53 / 1.49 | no |
| xmss_node/z=0 | 1 | 10002 / 9998 | 235333.3 | -19.227 | -0.0082% | -1.26 | 1.45 (crop 39) | 1.11 / 1.23 | no |
| xmss_node/z=1 | 1 | 10034 / 9966 | 480583.3 | +5.068 | +0.0011% | +0.15 | 1.29 (crop 16) | 1.58 / 1.93 | no |
| xmss_node/z=2 | 1 | 3039 / 2961 | 949583.3 | -728.555 | -0.0770% | -1.55 | 1.84 (crop 72) | 0.91 / 0.70 | no |
| xmss_node/z=3 | 1 | 2949 / 3051 | 1941375.0 | +385.012 | +0.0198% | -0.18 | 1.34 (crop 13) | 0.86 / 0.79 | no |
| xmss_node/z=4 | 1 | 2988 / 3012 | 3831375.0 | +18.942 | +0.0005% | +0.79 | 1.76 (crop 12) | 1.50 / 1.59 | no |
| xmss_sign | 1 | 492 / 508 | 123352375.0 | +10981.903 | +0.0089% | +0.35 | 1.75 (crop 15) | 1.98 / 1.68 | no |
| fors_sk_gen | 64 | 200547 / 199453 | 418.0 | +0.004 | +0.0010% | -1.61 | 1.61 | 1.63 / 1.48 | no |
| fors_node/z=0 | 32 | 100088 / 99912 | 845.1 | +0.059 | +0.0070% | -1.01 | 1.75 (crop 53) | 1.59 / 1.16 | no |
| fors_node/z=1 | 16 | 99737 / 100263 | 2127.6 | -0.058 | -0.0027% | -1.06 | 1.29 (crop 7) | 1.08 / 1.29 | no |
| fors_node/z=3 | 2 | 30094 / 29906 | 10104.2 | +0.887 | +0.0088% | +1.25 | 1.59 (crop 11) | 2.19 / 1.34 | no |
| fors_node/z=6 | 1 | 5083 / 4917 | 83875.0 | -2.921 | -0.0035% | +2.48 | 3.31 (crop 85) | 2.08 / 1.50 | no |
| fors_node/z=12 | 1 | 1985 / 2015 | 5353125.0 | -729.160 | -0.0136% | -0.80 | 1.66 (crop 2) | 1.30 / 2.08 | no |
| fors_sign | 1 | 299 / 301 | 74628291.7 | +224350.205 | +0.2999% | +0.70 | 3.28 (crop 31) | 1.24 / 1.16 | no |
| slh_keygen_internal | 1 | 1027 / 973 | 129771000.0 | -220856.496 | -0.1721% | -1.33 | 1.95 (crop 24) | 0.65 / 1.44 | no |
| CONTROL leaky_cmp (early-exit compare of secret) | 32 | 100383 / 99617 | 623.7 | +452.297 | +111.8098% | +223.72 | 839.87 (crop 6) | 1.81 / 2.85 | **yes** |
| CONTROL leaky_loop (secret-dependent iteration count) | 32 | 99785 / 100215 | 636.7 | -109.103 | -15.5798% | -220.19 | 220.19 | 1.93 / 1.04 | **yes** |

### Timing finding: bare SHA-256 on a repeated message (D2)

The SLH-DSA-level rows (everything from `thash` downwards, where the secret
is a 16- or 32-byte value inside a hash input that also contains PK.seed and
the address) show no detectable dependence, with one exception in the
all-zero run. The bare `sha256` rows (whole message secret), and some
`hmac_sha256` rows, do exceed 4.5. This was investigated with the class
designs in `scripts/dudect_diag.sh` (`out/dudect_diag.md`,
`out/dudect_diag_dit.md`; 2 seeds each, 200k-400k measurements per row):

| function family | class design | DIT | rows (2 seeds) | rows with max abs t > 4.5 | largest max abs t | trimmed mean diff, range (relative) |
|---|---|---|---|---|---|---|
| sha256 (9 lengths) | random vs random (null) | 0 | 18 | 0 | 3.60 | -0.0274% to +0.0405% |
| sha256 (9 lengths) | fixed A vs fixed B | 0 | 18 | 0 | 2.65 | -0.0266% to +0.0596% |
| sha256 (9 lengths) | fixed (pseudo-random) vs random | 0 | 18 | 9 | 27.62 | -0.0587% to +0.0200% |
| sha256 (9 lengths) | fixed (all-zero) vs random | 0 | 18 | 18 | 75.91 | -0.1173% to +0.1315% |
| hmac_sha256 (4 shapes) | random vs random (null) | 0 | 8 | 0 | 2.80 | -0.0144% to +0.0421% |
| hmac_sha256 (4 shapes) | fixed A vs fixed B | 0 | 8 | 0 | 2.41 | -0.0221% to +0.0235% |
| hmac_sha256 (4 shapes) | fixed (pseudo-random) vs random | 0 | 8 | 3 | 6.70 | -0.0182% to +0.0309% |
| hmac_sha256 (4 shapes) | fixed (all-zero) vs random | 0 | 8 | 4 | 16.90 | -0.0143% to +0.0536% |
| thash (4 lengths) | random vs random (null) | 0 | 8 | 0 | 3.15 | -0.0203% to +0.0204% |
| thash (4 lengths) | fixed A vs fixed B | 0 | 8 | 0 | 2.78 | -0.0323% to +0.0291% |
| thash (4 lengths) | fixed (pseudo-random) vs random | 0 | 8 | 0 | 2.95 | -0.0108% to +0.0236% |
| thash (4 lengths) | fixed (all-zero) vs random | 0 | 8 | 1 | 7.55 | -0.0221% to +0.0227% |
| sha256 (9 lengths) | fixed (pseudo-random) vs random | 1 | 18 | 0 | 2.76 | -0.0170% to +0.0182% |
| sha256 (9 lengths) | fixed (all-zero) vs random | 1 | 18 | 0 | 2.78 | -0.0121% to +0.0126% |
| hmac_sha256 (4 shapes) | fixed (pseudo-random) vs random | 1 | 8 | 0 | 2.93 | -0.0129% to +0.0321% |
| hmac_sha256 (4 shapes) | fixed (all-zero) vs random | 1 | 8 | 0 | 2.57 | -0.0130% to +0.0059% |

Interpretation:

* It is not a control-flow or address leak: T1 shows the instruction and
  address traces of `sha256` are identical across message values; the
  all-zero message used as fixed class here is included in T1 as the first
  pair of every row.
* It is not a dependence on *which* value is hashed in any way the test can
  see: two different fixed messages are indistinguishable (fixed-fixed rows).
  It appears only when one class repeats a single message tens of thousands
  of times while the other never repeats one, the repeated class being faster
  by 0.01%-0.13% (hundredths to tenths of a nanosecond per ~200-1300 ns call,
  i.e. a few nanoseconds per 32-128-call measurement). The all-zero message
  shows it most strongly.
* It vanishes with `PSTATE.DIT = 1`: 0 of the 52 diagnostic rows and 0 of
  the 13 `sha256`/`hmac_sha256` rows of the full DIT run exceed 4.5 (largest
  value 2.93 in the diagnostics). DIT costs roughly 25% in speed on this
  machine (e.g. `sha256/len=64` 309 -> 381 ns, keygen 103 -> 130 ms; compare
  the median columns).
* This pattern is what one expects from a data-dependent CPU optimisation
  that is trained by repeated data (load-value / store-value style
  prediction, data-dependent prefetching, or similar) and that the
  data-independent-timing mode switches off. The exact mechanism inside the
  M5 core was not identified; this is an inference from the three
  observations above, not a measurement of the mechanism.
* Relevance to SLH-DSA as used here. The hash inputs that contain secrets
  are fresh, uniformly random 16-byte values (SK.seed inside the PRF calls,
  FORS/WOTS secret values and chain values inside `F`), mixed with PK.seed and
  the address, and different at each of the ~2.2 million hash calls of a
  signature; an attacker does not get to make the signer hash one
  secret-dependent message tens of thousands of times and compare it with
  another. The rows that model the real usage (`thash/len=16`, `fors_sk_gen`,
  `prf_msg`, `chain`, `wots_*`, `xmss_*`, `fors_*`, keygen) never exceeded
  4.5 in any run. The `thash` rows across all runs (max |t|; bold = above
  4.5):

| row | fixed = pseudo-random: main run, diag seeds 1001/1002 | fixed = all-zero: main run, diag seeds 1001/1002 | fixed = pseudo-random, DIT=1 |
|---|---|---|---|
| thash/len=16 | 1.90, 1.40, 1.35 | 3.29, 2.44, 2.56 | 2.59 |
| thash/len=32 | 2.65, 1.55, 1.54 | **7.58**, 4.09, 2.91 | 1.95 |
| thash/len=224 | 2.23, 2.14, 1.67 | **9.84**, **7.55**, 4.43 | 1.86 |
| thash/len=560 | 1.68, 2.95, 2.07 | 2.84, 1.67, 2.56 | 2.24 |

  i.e. `thash` is flagged only with an *all-zero* fixed input of 32 or 224
  bytes, and not in every run -- the same repeated-input phenomenon as for
  bare SHA-256, at the edge of detectability. 32-byte and multi-block `thash`
  inputs are tree nodes, WOTS public-key chain ends and FORS roots, not
  SK.seed-level secrets, and an all-zero value there is not something that
  occurs.
* What it means for the claim under test: the compiled code is constant-time
  in the control-flow/address model, but, like any code on this CPU, it is
  not shielded from value-history-dependent microarchitectural timing unless
  DIT is enabled. The crate is `#![forbid(unsafe_code)]` and cannot set DIT
  itself; a caller that wants that guarantee has to enable DIT (e.g.
  `msr DIT, #1` / the platform API) around secret-key operations. That is a
  deployment recommendation, not a defect in the emitted code.

### D3. Whole signing (`out/dudect_sign_key.md`, `out/dudect_sign_addrnd.md`)

| function | calls/meas. | n (class 0 / 1) | median class 0 (ns/call) | trimmed mean diff (ns) | rel. | t | max abs t | null abs t (cls 1 / cls 0) | > 4.5? |
|---|---|---|---|---|---|---|---|---|---|
| slh_sign_internal (m, PK.seed fixed; honest keys) | 1 | 283 / 317 | 819893125.0 | -2594151.988 | -0.3179% | -1.29 | 1.83 (crop 7) | 2.30 / 1.28 | no |
| slh_sign_internal (m, whole key fixed) | 1 | 297 / 303 | 836570333.3 | -1649356.364 | -0.2000% | -0.64 | 2.01 (crop 3) | 3.39 / 1.31 | no |

Class designs and what they show:

* *sign-key*: m and PK.seed shared; class 0 = one fixed honest key
  (SK.seed, SK.prf, PK.root = root of SK.seed) with one fixed addrnd; class 1
  = a fresh honest key and addrnd for every signature (key generation happens
  outside the timed region). Changing SK.seed necessarily changes PK.root and
  the whole public transcript, so the two classes differ in public data as
  well as in secrets. The test is still meaningful because T6 shows the
  amount of work is transcript-independent to within ~3e-9 relative: under
  the audit's claim total time has the same distribution in both classes, so
  a significant difference would indicate either a secret-dependent amount of
  work or a value-dependent timing effect at scale. None was detected.
* *sign-addrnd*: the whole key fixed, class 0 = fixed addrnd, class 1 = fresh
  addrnd (hedged signing randomness is secret until R is published; R itself
  is public). None detected.
* Resolution: `slh_sign_internal (m, PK.seed fixed; honest keys)`: standard error of the difference of class means 2.52 ms = 0.308% of the 0.82 s signing time, so a mean shift below roughly 11.4 ms (1.39%) would not reach the threshold; `slh_sign_internal (m, whole key fixed)`: standard error of the difference of class means 2.14 ms = 0.255% of the 0.84 s signing time, so a mean shift below roughly 9.6 ms (1.15%) would not reach the threshold. A pass here says nothing about leaks that
  reorder work without changing its amount; those are covered by T4, not by
  total time.

### What a timing pass does and does not mean

A row below 4.5 means: with this many samples on this machine under this
load, the *mean* (and cropped means) of the execution time did not differ
detectably between one fixed secret and random secrets. It does not bound
leakage observable by a stronger adversary (per-instruction power/EM,
cache-line probing from a co-located process, speculative-execution gadgets),
it only tests two classes, and laptop/desktop timing noise can hide small
effects (sensitivity reached, as standard error of the uncropped mean
difference: 0.014%-0.043% of the call time for the sub-10-microsecond functions and 0.022%-0.197% for the longer ones (figures from the DIT=1 run, the one that printed this column), about 0.3% for whole signing; the cropped tests are somewhat more sensitive). The dudect results are therefore weak, supporting
evidence; the trace comparison in section 1 is the primary evidence.

## 4. Limitations

* **One compiler, one target, one profile.** rustc 1.100.0 / LLVM 23.1.5,
  `aarch64-apple-darwin`, default release profile. A different rustc/LLVM
  version, `opt-level`, LTO setting, `target-cpu`, or target (x86-64, other
  Arm cores, bare-metal) can compile the same source differently (e.g. turn a
  `csel` into a branch, vectorise, or call `memcmp`); the experiments must be
  rerun per configuration. The code traced is the native macOS build (object
  code verified identical to the main crate's release rlib), not a rebuild.
* **Sampling, not exhaustion.** Dozens of secret pairs per row (12-64; 32 for
  whole signing with addresses), a handful of public configurations. Trace
  equality on samples cannot exclude a divergence on rare inputs; for this
  code that would require a data-dependent branch or address that the static
  reading and the Lean argument say does not exist.
* **What the emulator does not see.** Caches, TLB, branch/value predictors,
  prefetchers, speculation and transient execution, micro-op timing of
  individual instructions (Unicorn is a functional emulator: all instructions
  "take" the same time), frequency scaling, interrupts. The trace model is
  exactly: executed PC sequence + data addresses + sizes. The timing section
  is the only part that touches real hardware timing, and it found the DIT
  effect above.
* **Stubbed library code.** `malloc/calloc/realloc/free/posix_memalign` are
  replaced by a deterministic size-class allocator in the tracer, and
  `memcpy/memmove/memset/bzero` by host-side stubs; the real libSystem
  implementations were not traced. Their behaviour is assumed to depend only
  on (pointers, lengths), which *are* recorded and compared (sizes and
  lengths were identical across secrets everywhere), and on allocator state
  driven by the same call sequence. `memcmp/bcmp` would have aborted the run;
  it is never reached from the tested functions. Rust's own allocation glue
  (`__rust_alloc`, `RawVec` growth) is inside the image and was traced.
* **Block granularity of control flow.** Unicorn reports translated blocks;
  the PC sequence inside a block is implied. Block boundaries come from
  Unicorn's translator (they changed between two builds of the harness while
  instruction counts stayed the same), which cannot cause a missed
  divergence, only a different event count.
* **Declassification-pinned signing test.** Depends on locating `thash` and
  `prf_msg` as out-of-line symbols and on the sret return convention of this
  build (self-checked, see T4). It tests "trace depends on secrets only via
  the nine pinned values", with the publicness of those values taken from the
  audit.
* **Unwinding paths** (bounds-check panics, allocation failure, `ctx` longer
  than 255 bytes returning `None`) are never taken with valid inputs and were
  not explored.
* **Verification functions** (`slh_verify*`, `*_pk_from_sig`, `ht_verify`,
  which ends in a non-constant-time array comparison on public values)
  handle only public data and were not tested as secret-handling code;
  `fors_pk_from_sig`/`xmss_pk_from_sig` are exercised inside signing (T4).
* **Timing tests.** No core pinning, shared machine, 41.67 ns clock
  granularity (hence batching, which averages over repeated calls on the same
  input), two classes only, first-order (mean) test only, `max` over 101
  croppings. See "What a timing pass does and does not mean".
* **Zeroisation is out of scope and not provided.** The crate does not wipe
  SK.seed/SK.prf copies, FORS/WOTS secret values, HMAC key pads or
  intermediate buffers from the stack or from freed heap blocks (`Vec`s are
  dropped without clearing), and neither does this harness test for it.
* **DIT is not set by the crate** (safe Rust cannot); see the timing finding.

## 5. Reproduction

`./run.sh all` (see README.md). Seeds are fixed (`cttrace` default seed
0x5148445341, `dudect` default seed 0xD0DEC7, diagnostics 1001/1002), so the
trace experiments are exactly reproducible on the same toolchain; timing
numbers will vary run to run.
