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
`..`: {{RLIB_COMPARE}}

## Summary

| # | Experiment | What was compared | Trials | Outcome |
|---|---|---|---|---|
| T1 | Component traces, secret varied (Unicorn; control flow + memory addresses + call-outs) | full event sequence between runs with identical public inputs and different secrets, {{N_COMPONENT_ROWS}} function/parameter rows | {{N_COMPONENT_PAIRS}} secret pairs | **all identical, 0 divergences** |
| T2 | Positive controls (leaky code in the harness) | same checker | 3 controls, {{T2_PAIRS}} pairs | **all 3 detected** ({{T2_DIFF}} pairs differ: control-flow and memory-address leaks; the remaining pairs are secrets that happen to take the same path) |
| T3 | Public-variation controls | same checker, a public input varied | 3 controls, {{T3_PAIRS}} pairs | **{{T3_DIFF}}/{{T3_PAIRS}} differ**, as they must |
| T4 | Whole `slh_sign_internal`, declassified values pinned (control flow + memory addresses) | run B (fresh SK.seed, SK.prf, addrnd) vs run A, with R, PK_FORS and the 7 XMSS roots forced to A's values | 8 public configs x 4 secret sets = 32 pairs, ~1.6e10 instructions and ~3.9e9 events per run | **32/32 identical**; 16/16 unpinned controls differ |
| T5 | Whole `slh_sign` (with context), pinned, control flow only | as T4 | 4 x 3 = 12 pairs | **12/12 identical**; 8/8 unpinned controls differ |
| T6 | Whole-signature unconditioned profile | 24 honest random keys, fixed m and PK.seed | 24 runs | SHA-256/`thash`/allocator call counts constant; instruction count spread 44 out of 1.6e10 |
| S1 | Static disassembly | all 27 `slhdsa` functions in the binary | 3509 instructions | no integer division, no SHA/AES crypto-extension instruction, no indirect branch, SHA-256 rounds not vectorised, `K[i]`/`w[i]` indexed by the loop counter only |
| D1 | dudect timing, SLH-DSA-level components (`thash`, `prf_msg`, `chain`, `wots_*`, `xmss_*`, `fors_*`, keygen), secret = SK.seed / SK.prf / addrnd / chain value / hash input | fixed vs random secret, public inputs shared | 3 runs of {{N_SLH_ROWS}} rows, 600 to 400k measurements per row | rows above 4.5 -- fixed pseudo-random secret: {{FLAG_FR}}; same with DIT=1: {{FLAG_DIT}}; all-zero fixed secret: {{FLAG_FZ}} (multi-byte all-zero `thash` inputs only, intermittent; see D2) |
| D2 | dudect timing, bare `sha256` / `hmac_sha256` on fully secret messages | fixed vs random message | 13 rows x several runs | **|t| > 4.5 in many rows** when one message is repeated (strongest for the all-zero message); effect size <= 0.13% of the call time. Not present between two different fixed messages, not present with `PSTATE.DIT=1`. See "Timing finding" below |
| D3 | dudect timing, whole `slh_sign_internal` | fixed vs random (key, addrnd), and fixed key with fixed vs random addrnd | 2 x 600 signatures | no difference detected (weak: see resolution) |
| D4 | dudect positive controls | `leaky_cmp`, `leaky_loop` | 2 controls x 3 runs | detected every time (max |t| from {{CTL_RANGE}}) |

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

{{TRACE_COMPONENTS}}

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

{{TRACE_SIGN}}

`slh_sign` (context wrapper, 17-byte context), control flow only:

{{TRACE_SIGN_CTX}}

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

{{TRACE_PROFILE}}

So over random honest keys the *amount* of work is essentially constant
(every signature performs exactly the same number of SHA-256 computations and
allocator calls; the instruction count varies by a few dozen instructions,
presumably from public-data-dependent paths such as the left/right choice in
`climb` and how the 15 chain steps per WOTS digit are split between signing
and public-key recomputation -- this was not broken down further), while the *order* of work differs with the public transcript. This is
what makes a total-time measurement of signing (D3) meaningful at all.

## 2. Static facts about the native code (`out/disasm.md`)

{{DISASM}}

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
(observed range over all component rows of the three runs: {{NULL_RANGE}};
whole signing: up to {{SIGN_NULL}}), and the dedicated random-vs-random
experiments in `out/dudect_diag.md` do not exceed {{RR_MAX}} in any of their
{{RR_ROWS}} rows. "trimmed mean diff" is mean(class 0) -
mean(class 1) over the measurements below the pooled 90th percentile.

Nothing was pinned to a core (macOS offers no affinity API); the measuring
thread asks for `QOS_CLASS_USER_INTERACTIVE` to stay on performance cores.
The machine was otherwise lightly loaded but not idle (1-minute load average
between ~2 and ~9 during the day; other agents were working in the same
repository).

### D1/D2. Components, fixed class = one fixed pseudo-random secret (`out/dudect_components_fixed_random.md`)

{{DUDECT_FR}}

### D1/D2. Components, fixed class = all-zero secret (`out/dudect_components_fixed_zero.md`)

{{DUDECT_FZ}}

### D1/D2. Components, fixed pseudo-random secret, `PSTATE.DIT = 1` (`out/dudect_components_fixed_random_DIT.md`)

{{DUDECT_DIT}}

### Timing finding: bare SHA-256 on a repeated message (D2)

The SLH-DSA-level rows (everything from `thash` downwards, where the secret
is a 16- or 32-byte value inside a hash input that also contains PK.seed and
the address) show no detectable dependence, with one exception in the
all-zero run. The bare `sha256` rows (whole message secret), and some
`hmac_sha256` rows, do exceed 4.5. This was investigated with the class
designs in `scripts/dudect_diag.sh` (`out/dudect_diag.md`,
`out/dudect_diag_dit.md`; 2 seeds each, 200k-400k measurements per row):

{{DIAG_SUMMARY}}

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

{{THASH_TABLE}}

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

{{DUDECT_SIGN}}

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
* Resolution: {{SIGN_RESOLUTION}} A pass here says nothing about leaks that
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
difference: {{SENS}}; the cropped tests are somewhat more sensitive). The dudect results are therefore weak, supporting
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
