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

{{default:BUILD}}

Build record of the hw-sha2 variant (`out/hw-sha2/build.txt`):

{{hw-sha2:BUILD}}

**The traced code is the native code.** `cttrace` executes its own Mach-O
image inside the emulator, so no bare-metal rebuild is involved. In addition,
`scripts/disasm_check.py` compared the `slhdsa` object code inside this
package's dependency rlib (A) with the rlib that `cargo build --release
--locked` produces from the main crate's own manifest (B; built into a target
directory inside this package, so `..` is not written to):

* default: {{default:RLIB_COMPARE}}
* hw-sha2: {{hw-sha2:RLIB_COMPARE}}

The constant tables are the same too; the only difference between A and B is
that the source-file paths in the panic-location records are absolute in A
and relative in B (section 2).

## Summary

| # | Experiment | default build | hw-sha2 build |
|---|---|---|---|
| T0 | Emulator check: SHA-256 instructions executed, emulated output = native output | {{default:HWCHECK_ROWS}} entry points, none executes a SHA-256 instruction, all outputs equal | {{hw-sha2:HWCHECK_ROWS}} entry points, all execute SHA-256 instructions, all outputs equal |
| T1 | Component traces with the secret varied (control flow + memory addresses + call-outs): full event sequence between runs with identical public inputs | {{default:COMP_SEC_ROWS}} function/parameter rows, {{default:COMP_SEC_CFGS}} public configurations, {{default:COMP_SEC_PAIRS}} pairs: **all identical, 0 divergences** | {{hw-sha2:COMP_SEC_ROWS}} rows, {{hw-sha2:COMP_SEC_CFGS}} public configurations, {{hw-sha2:COMP_SEC_PAIRS}} pairs: **all identical, 0 divergences** |
| T1b | The verifier's recomputation (`*_pk_from_sig`) with the signature bytes varied | {{default:COMP_VS_ROWS}} rows, {{default:COMP_VS_PAIRS}} pairs: all identical | {{hw-sha2:COMP_VS_ROWS}} rows, {{hw-sha2:COMP_VS_PAIRS}} pairs: all identical |
| T2 | Positive controls (leaky code in the harness), same checker | {{default:COMP_LEAKY}}: **all detected** | {{hw-sha2:COMP_LEAKY}}: **all detected** |
| T3 | Public-variation controls (a public input varied must change the trace) | {{default:COMP_PUBCTL}}: all detected | {{hw-sha2:COMP_PUBCTL}} (includes the `PREFIX` row): all detected |
| T4 | Whole signing with the declassified values pinned, 8 entry points: run B (fresh SK.seed, SK.prf, addrnd) vs run A with R, PK_FORS and the XMSS roots forced to A's values | {{default:SIGN_TOTAL_CFGS}} public configurations, {{default:SIGN_TOTAL_PAIRS}} pairs: **all identical**; every unpinned control differs | {{hw-sha2:SIGN_TOTAL_CFGS}} public configurations, {{hw-sha2:SIGN_TOTAL_PAIRS}} pairs: **all identical**; every unpinned control differs |
| T5 | Whole-signature unconditioned profile over honest random keys | {{default:PROFILE_internal_RUNS}} + {{default:PROFILE_internal-checked_RUNS}} runs; call counts of every function constant; instruction count spread {{default:PROFILE_internal_SPREAD}} (checked: {{default:PROFILE_internal-checked_SPREAD}}) | {{hw-sha2:PROFILE_internal_RUNS}} + {{hw-sha2:PROFILE_internal-checked_RUNS}} runs; call counts and SHA-256 instruction counts constant; instruction count spread {{hw-sha2:PROFILE_internal_SPREAD}} (checked: {{hw-sha2:PROFILE_internal-checked_SPREAD}}) |
| S1 | Static disassembly of the `slhdsa` functions in the binary | {{default:STATIC_TOTAL}}; no call of `memcmp`/`bcmp` | {{hw-sha2:STATIC_TOTAL}}; no call of `memcmp`/`bcmp` |
| D0 | Timing noise floor: random vs random before and after each series, 52 rows | no row above 4.5 (largest {{default:DUDECT_NULLB_MAX}} before, {{default:DUDECT_NULLA_MAX}} after): timing usable | no row above 4.5 (largest {{hw-sha2:DUDECT_NULLB_MAX}} before, {{hw-sha2:DUDECT_NULLA_MAX}} after): timing usable |
| D1 | dudect, 50 component rows, fixed vs random secret (both classes prepared alike), `PSTATE.DIT = 0` | **{{default:DUDECT_SAME_NFLAG}} rows above 4.5**, all short hash-level calls (largest {{default:DUDECT_SAME_MAX}}) | **{{hw-sha2:DUDECT_SAME_NFLAG}} row above 4.5**: {{hw-sha2:DUDECT_SAME_FLAGGED}} |
| D2 | the same with `PSTATE.DIT = 1` | no row above 4.5 (largest {{default:DUDECT_SAMEDIT_MAX}}) | no row above 4.5 (largest {{hw-sha2:DUDECT_SAMEDIT_MAX}}) |
| D3 | diagnostics, `PSTATE.DIT = 0`: two different fixed secrets; the all-zero secret vs another fixed one | not distinguishable; **distinguishable in {{default:DUDECT_ZF_NFLAG}} of 50 rows** (bulk hash inputs; largest {{default:DUDECT_ZF_MAX}}) | not distinguishable; **distinguishable in {{hw-sha2:DUDECT_ZF_NFLAG}} of 50 rows** (largest {{hw-sha2:DUDECT_ZF_MAX}}; includes an all-zero SK.seed in `fors_sk_gen`) |
| D4 | the same diagnostics with `PSTATE.DIT = 1` | not distinguishable | not distinguishable |
| D5 | dudect, whole signing, plain and checked signer, 4 x 600 signatures, `PSTATE.DIT = 0` | no row above 4.5 (largest {{default:DUDECT_SIGN_MAX}}) | no row above 4.5 (largest {{hw-sha2:DUDECT_SIGN_MAX}}) |
| D6 | dudect positive controls (`leaky_cmp`, `leaky_loop`) | detected in every fixed-vs-random run (max abs t {{default:DUDECT_FR_CTL}} in the first) | detected in every fixed-vs-random run ({{hw-sha2:DUDECT_FR_CTL}} in the first) |

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

{{default:HWCHECK}}

hw-sha2 build:

{{hw-sha2:HWCHECK}}

In the hw-sha2 build every hash goes through the instructions (for example a
15-step chain executes 15 x 15 + 1 = 226 `SHA256H`: fifteen four-round groups
per step, and the first group once for the whole chain), the emulator's
results equal the CPU's on every run of every experiment, and
`sha256::hw_active()` is true (on `aarch64-apple-darwin` the feature test is a
compile-time constant, so no detection code runs in the guest). The default
build contains and executes no SHA-256 instruction.

### T1-T3. Components and controls, default build (`out/default/trace_components.md`)

{{default:COMP}}

### T1-T3. Components and controls, hw-sha2 build (`out/hw-sha2/trace_components.md`)

{{hw-sha2:COMP}}

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
default: {{default:COMP_INFO}}; hw-sha2: {{hw-sha2:COMP_INFO}}.
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

{{default:SIGN_SUMMARY}}

hw-sha2 build (everything with control flow and memory addresses):

{{hw-sha2:SIGN_SUMMARY}}

Per-configuration tables, default build, `slh_sign_internal`:

{{default:SIGN_internal}}

default build, `slh_sign_internal_checked`:

{{default:SIGN_internal-checked}}

hw-sha2 build, `slh_sign_internal`:

{{hw-sha2:SIGN_internal}}

hw-sha2 build, `slh_sign_internal_checked`:

{{hw-sha2:SIGN_internal-checked}}

(The per-configuration tables of the six other entry points are in
`out/*/trace_sign_{slh,slh-checked,api,api-checked,api-det,api-det-checked}.md`.
Message lengths 32, 0, 100 and 1 bytes rotate over the configurations; the
entry points with a context use a 17-byte context; in the deterministic
entry points `addrnd` is PK.seed, so only SK.seed and SK.prf are varied.)

What this establishes: for {{default:SIGN_TOTAL_PAIRS}} (default) and
{{hw-sha2:SIGN_TOTAL_PAIRS}} (hw-sha2) pairs of unrelated secret sets, once the
public intermediate values are equal, the entire execution
({{default:SIGN_internal_INSN}} instructions per signature in the default
build, {{default:SIGN_internal-checked_INSN}} checked;
{{hw-sha2:SIGN_internal_INSN}} and {{hw-sha2:SIGN_internal-checked_INSN}} in
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

{{default:PROFILE_internal}}

default build, `slh_sign_internal_checked`:

{{default:PROFILE_internal-checked}}

hw-sha2 build, `slh_sign_internal`:

{{hw-sha2:PROFILE_internal}}

hw-sha2 build, `slh_sign_internal_checked`:

{{hw-sha2:PROFILE_internal-checked}}

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

{{default:DISASM}}

### hw-sha2 build

{{hw-sha2:DISASM}}

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

{{DUDECT_NOISE}}

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

{{default:DUDECT_MATRIX}}

hw-sha2 build:

{{hw-sha2:DUDECT_MATRIX}}

### D2. Diagnostics on the flagged rows (`out/*/dudect_diag.md`, `dudect_diag_chain.md`)

Ten hash-level rows, default number of measurements (200k to 400k per row),
max |t|; {{default:DIAG_LOAD}} (default) and {{hw-sha2:DIAG_LOAD}} (hw-sha2).
RR = random vs random, FF = two fixed pseudo-random secrets, FR = fixed vs
random (design B), FR/same = design F, FR/x8 = eight times the calls per
measurement, FZ = zero vs random (C), ZF = zero vs fixed (H), /DIT =
`PSTATE.DIT = 1`.

default build:

{{default:DIAG}}

hw-sha2 build:

{{hw-sha2:DIAG}}

The multi-block `chain_blocks` rows, four times the default number of
measurements (80k to 400k per class); {{default:DIAGC_LOAD}} (default) and
{{hw-sha2:DIAGC_LOAD}} (hw-sha2).

default build:

{{default:DIAGC}}

hw-sha2 build:

{{hw-sha2:DIAGC}}

### Timing finding: with DIT off, the CPU's timing depends on the data; with DIT on, no dependence was detected

This is the one non-clean result of the whole exercise, so it is spelled out.
It concerns the processor, not the instruction or address sequence: T1 shows
that the traces of all the functions below are identical across the values
of the varied bytes, and the all-zero value used here is the first pair of
every T1 row.

**What was measured, default build.**

1. *Fixed vs random is distinguishable with `PSTATE.DIT = 0`* (column B):
   {{default:DUDECT_FR_NFLAG}} of 50 rows above 4.5 --
   {{default:DUDECT_FR_FLAGGED}}. The varied bytes are, per row: the whole
   message (`sha256`), state and block (`compress`), the hashed value
   (`thash_short`, `thash`), bytes 16..64 of the blocks (`chain_blocks`),
   SK.seed (`fors_node`). The differences are small (the class means differ by
   0.01% to 0.25% of the call time) but far outside the noise of columns A
   and E.
2. *The all-zero secret against random ones* (column C) is distinguishable in
   {{default:DUDECT_FZ_NFLAG}} of 50 rows, most strongly `compress` (all-zero
   state and block run about 1.7% faster than random ones).
3. *For the multi-block `chain_blocks` rows, the flags of the standard
   fixed-vs-random design come from the harness, not from the data.* Two of
   the rows flagged in B are such rows, and with `PSTATE.DIT = 1` the
   standard design still flagged {{default:DUDECT_DIT_FLAGGED}} (column D).
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
   {{default:DUDECT_SAME_NFLAG}} of 50 rows remain above 4.5:
   {{default:DUDECT_SAME_FLAGGED}}. All of them are short hash-level calls
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
   {{default:DUDECT_ZF_NFLAG}} of 50 rows ({{default:DUDECT_ZF_FLAGGED}}):
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
   (column G) {{default:DUDECT_SAMEDIT_NFLAG}} of 50 rows exceed 4.5; in the
   diagnostics, with DIT on, fixed vs random, zero vs random, fixed vs fixed
   and zero vs fixed are all below 4.5 on the ten hash-level rows, and so are
   fixed vs random with the same preparation, fixed vs fixed and zero vs
   fixed on the multi-block rows. DIT costs {{default:DIT_COST}} in speed on this machine
   (the two medians of each row).

**hw-sha2 build.** The same experiments show the same structure with
smaller effects.

* Fixed vs random (B): {{hw-sha2:DUDECT_FR_NFLAG}} of 50 rows
  ({{hw-sha2:DUDECT_FR_FLAGGED}}); in the corrected design (F)
  {{hw-sha2:DUDECT_SAME_NFLAG}} ({{hw-sha2:DUDECT_SAME_FLAGGED}}). Of the
  hash-level rows only bare `sha256` on a one-byte message is flagged;
  `compress`, `thash_short`, `chain_blocks` and `fors_node`, which are flagged
  in the default build, are not (in the diagnostics FR and FR/same are below
  3 for every row but `sha256/len=1`).
* The all-zero value: zero vs random (C) {{hw-sha2:DUDECT_FZ_NFLAG}} of 50
  rows; zero vs fixed (H) {{hw-sha2:DUDECT_ZF_NFLAG}}
  ({{hw-sha2:DUDECT_ZF_FLAGGED}}). Here the all-zero value is distinguishable
  also where it is a 16-byte value inside a PRF or F input: `fors_sk_gen`
  with an all-zero SK.seed is about 0.08% slower than with another fixed
  SK.seed (max |t| 22 in H, 29 in the diagnostics), `thash_short/len=16`
  likewise (8 and 12). At 27 ns per call and 1024 calls per measurement that
  is about 25 ns per measurement.
* With `PSTATE.DIT = 1`: the standard design (D) flags
  {{hw-sha2:DUDECT_DIT_FLAGGED}}, multi-block rows again; the follow-up
  shows the same harness artefact as in the default build (flagged in the
  standard design in both seeds, with and without DIT; not flagged with the
  same preparation, nor fixed vs fixed, nor random vs random). On these
  multi-block rows the all-zero value is *not* distinguishable from another
  fixed value in this build.
  The corrected design (G) flags {{hw-sha2:DUDECT_SAMEDIT_NFLAG}} of 50 rows,
  and in the diagnostics every DIT column is below 4.5 except that
  standard-design one on the multi-block rows. DIT costs
  {{hw-sha2:DIT_COST}} in speed.

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

{{default:DUDECT_SIGN}}

hw-sha2 build:

{{hw-sha2:DUDECT_SIGN}}

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
  signer (largest max |t| {{default:DUDECT_SIGN_MAX}} in the default build,
  {{hw-sha2:DUDECT_SIGN_MAX}} in the hw-sha2 build), all with
  `PSTATE.DIT = 0`.
* Resolution. default build: {{default:DUDECT_SIGN_RES}}. hw-sha2 build:
  {{hw-sha2:DUDECT_SIGN_RES}}. A mean shift below roughly 4.5 times that
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
