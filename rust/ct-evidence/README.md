# ct-evidence: binary-level constant-time evidence for `slhdsa`

This is a standalone cargo package (own `[workspace]`, own target
directories) that collects **evidence, not proof**, that the machine code
rustc emits for the `slhdsa` crate (SLH-DSA-SHA2-128s, `../src`) has
secret-independent control flow, memory-access addresses and timing. It does
not modify the crate under test and is not built by `cargo build/test` in
`..`.

The crate has two builds and everything here is done for both:

* **default**: portable SHA-256, safe Rust only;
* **hw-sha2**: `--features hw-sha2`, SHA-256 on the ARMv8 SHA-256 instructions,
  four hash chains at a time (`../src/sha256.rs`, module `hw`).

The package has a feature `hw-sha2` that forwards to the crate's. `./run.sh`
builds the default variant into `target/` and the other into `target-hw/`.

Results of the runs performed on 2026-11-21 on the crate as it was that day
are in [RESULTS.md](RESULTS.md); the raw outputs are in `out/default/` and
`out/hw-sha2/`. (The harness was first written on 2026-11-20 for an earlier
version of the crate; those results are in the git history of this
directory and are not reproduced here.)

## Threat model being tested

* Secret: `SK.seed`, `SK.prf`, `addrnd`, and everything derived from them
  before publication (FORS/WOTS secret values, unrevealed chain values, tree
  nodes that are not on a published path).
* Public: `PK.seed`, `PK.root`, message, context, the signature, and
  everything the verifier recomputes: `R`, the message digest and all indices,
  the FORS public key, every XMSS root, hence all WOTS+ digits (the `start` /
  `end` step ranges of `hash::chain_blocks`), and all hash addresses.
* Leakage: sequence of executed instruction addresses, sequence of memory
  addresses read/written, and time.

## Three kinds of evidence

### 1. Deterministic trace comparison (`src/bin/cttrace.rs`)

`cttrace` links the `slhdsa` rlib compiled with the default cargo release
profile for `aarch64-apple-darwin` (no profile overrides, i.e. the flags
`cargo build --release` uses in `..`), then **maps its own Mach-O image into a
Unicorn AArch64 emulator at the same addresses** and executes the harness
entry points (`src/lib.rs`, one thin `extern "C" fn(input, output)` wrapper per
function under test) instruction by instruction. So the code that is traced
is the native release machine code, not a rebuild for another target. The
emulator's CPU model is `max`, which implements the SHA-256 instructions the
`hw-sha2` build uses.

Recorded per run (values are never recorded, only addresses and sizes):

* every executed basic block: (address, size);
* every memory read and write: (address, size) -- stack, heap, I/O buffers,
  constants;
* every call that leaves the image, serviced by a host-side stub and recorded
  with its arguments: `malloc/calloc/realloc/free/posix_memalign` (a
  deterministic size-class allocator with a fixed guest heap base, so no
  address normalisation is needed), `memcpy/memmove/memset/bzero` (recorded as
  (dst, src, len)). `memcmp/bcmp` is treated as a failure if it is ever
  reached (libSystem's is not constant-time); it never is.

Guest stack, heap and I/O buffers live at fixed guest addresses and are reset
before every run, so two runs have the same trace iff the event sequences are
bit-for-bit identical. Sequences are compared via a 128-bit running hash plus
event counts and per-65536-event checkpoints; on a mismatch the diverging
chunk is re-executed in capture mode and the first differing event is printed
with the symbol of its basic block. Each emulated run's output is also checked
against a native call of the same wrapper (emulation fidelity).

Experiments:

* `cttrace hwcheck` -- runs a selection of entry points once with block
  profiling, decodes the executed blocks and counts the SHA-256 instructions
  executed (`SHA256H`, `SHA256H2`, `SHA256SU0`, `SHA256SU1`), and compares the
  emulated output with the native one. With the `hw-sha2` build every row
  must execute SHA-256 instructions, with the default build none may.
* `cttrace components` -- for each function, several public configurations
  (public inputs pseudo-random but fixed), and for each several fresh values
  of the varied bytes, the first of them all-zero; all traces within a
  configuration must be identical. Rows:
  * the SHA-256 layer: `sha256`, `hmac_sha256` (no longer called by the crate
    itself), `compress` (which is `#[inline]`: the row traces the copy inlined
    into the wrapper);
  * the tweakable hashes: `thash_short` (F, PRF, H), `thash`, `thash_values`
    (T_len over 35 blocks), `prf_msg`;
  * `chain_blocks`, the function nearly every hash of the crate goes through:
    bytes 16..64 of every block varied, with the step ranges and the 16-byte
    block prefixes public and fixed, in thirteen shapes (one to 128 blocks;
    full, partial, empty and single-step ranges as WOTS+ and FORS produce
    them; pseudo-random ranges; one, two or all-distinct prefixes), plus two
    shapes of `chain_blocks_portable`;
  * `wots_pk_gen`, `wots_sign`, `xmss_node` (z = 0..4), `xmss_sign`,
    `fors_sk_gen`, `fors_node` (z = 0..12, both the batched and the recursive
    path), `fors_sign`, `fors_pk_gen`, `slh_keygen_internal` (also with
    PK.seed varied) and `api::keygen`, with `SK.seed` (and `SK.prf`) varied;
  * `wots_pk_from_sig`, `xmss_pk_from_sig`, `fors_pk_from_sig` with the
    signature bytes varied: the recomputation a verifier does, which the
    signer runs on its own signature before publishing it;
  * one row where a public input is varied and the outcome is only reported
    (`INFO`: the public digest of `fors_sign`);
  * positive controls (`leaky_cmp`, `leaky_table`, `leaky_loop`, defined in
    this crate only), which must be detected, and public-variation controls
    (varying a public WOTS+ message, a public step count of `chain_blocks`,
    a public message length must change the trace);
  * `PREFIX`: the `hw-sha2` backend of `chain_blocks` keeps the first four
    rounds of the last block it entered and reuses them when the next block
    starts with the same 16 bytes (an address prefix, public). The row varies
    one public bit, whether one block shares the prefix of the others. With
    `hw-sha2` this must change the trace (a control: the tracer sees the
    reuse); with the default build the row is informational.
* `cttrace sign --entry E` -- whole signing. One cannot hold the signature
  fixed while varying the key, so this is a *declassification-pinned*
  comparison. Run A signs honestly and the tracer records the 16-byte results
  of the calls that produce the values the audit says are the only channel
  from secrets to control flow and addresses:
  `R` = result of `hash::prf_msg`; `PK_FORS` = result of
  `fors::fors_pk_from_sig`; the seven XMSS roots = results of
  `xmss::xmss_pk_from_sig`; and in the checked signer, which computes each of
  these (except the top root, which it compares with `PK.root`) a second time
  from the secret seed, also the result of `fors::fors_pk_gen` and of the six
  calls `xmss::xmss_node(.., i = 0, z = 9, ..)`. That is 9 values per
  signature, 16 in the checked signer. Run B uses the same public inputs
  (M, ctx, PK.seed, PK.root) and *different* `SK.seed`, `SK.prf`, `addrnd`, and
  the tracer overwrites those results with run A's values (through the
  emulator API, when the call returns; nothing else is touched). All other
  intermediate values in run B -- every FORS secret, every WOTS+ secret and
  chain value, every Merkle node, the signature body -- differ from run A.
  Identical traces then show that the secrets influence the trace only
  through those values.
  Checks in every configuration: the emulated output of A equals the native
  one and verifies natively; **the recorded values are exactly, in order, the
  values a verifier computes from (M, PK, signature of A)** (recomputed
  natively with `h_msg`, `fors_pk_from_sig` and `xmss_pk_from_sig`, the
  second-route values of the checked signer being equal to the first-route
  ones), which also confirms the hook points and the return convention;
  replaying A's values into A is a no-op; in B every value is pinned, B
  returns a signature with A's `R` and a different body; and without pinning
  B's trace must differ from A's.
  The hook points are located through the symbols of the five functions,
  which are out-of-line in both builds; the entry of `xmss_node` counts only
  when its third integer argument (z) is 9. A build that inlines one of them
  makes the experiment report INCONCLUSIVE, not pass.
  Entry points: `internal` (`slh_sign_internal`), `internal-checked`
  (`slh_sign_internal_checked`), `slh`, `slh-checked` (`slh_sign`,
  `slh_sign_checked`, 17-byte context), `api`, `api-checked` (`api::sign`,
  `api::sign_checked`), `api-det`, `api-det-checked`
  (`api::sign_deterministic(_checked)`, where `addrnd` is `PK.seed`).
* `cttrace sign-profile --entry E` -- unconditioned signing runs over random
  honest keys with M and PK.seed fixed; reports which coarse quantities are
  invariant (instruction count, call-out count, SHA-256 instruction counts,
  calls of each out-of-line function of the crate, block histogram).

### 2. dudect-style timing test (`src/bin/dudect.rs`)

Fixed-vs-random Welch t-test on native execution time
(`mach_absolute_time`). Both classes share all public inputs and differ only
in the secret bytes; class of each measurement is random; inputs are prepared
outside the timed region; short functions are called in a loop so that one
measurement is >= ~20 us (the clock ticks at ~42 ns). Statistic: max |t| over
the uncropped test and the 100 dudect percentile croppings; threshold 4.5.
Also reported: the difference of the 10%-trimmed class means (effect size)
and the standard error of the difference of class means (resolution).
Noise floor: the same statistic on null splits (class-1 samples split by
arrival parity, and likewise class 0), and the whole experiment with both
classes random (`--classes random-random`). Positive controls: `leaky_cmp`,
`leaky_loop`.

Options:

* `--fixed-zero`: the fixed class is the all-zero secret instead of one fixed
  pseudo-random secret;
* `--classes fixed-fixed|random-random`: two different fixed secrets (with
  `--fixed-zero`: all-zero against a fixed pseudo-random one); or both classes
  fresh random, a true null experiment;
* `--dit`: set the Arm `PSTATE.DIT` data-independent-timing bit on the
  measuring thread before measuring (the crate itself never sets it);
* `--same-prep`: prepare both classes by the same code path. In the standard
  design the fixed class's input is one copy of a buffer and the random
  class's is a copy that is then partly overwritten; on rows with kilobytes
  of varied bytes and one or two calls per measurement that difference is
  itself measurable (RESULTS.md, section 3). With this option both classes
  are drawn like the random one and the fixed class's secret bytes are then
  overwritten with the fixed value;
* `--reps-mul K`: K times the calibrated number of calls per measurement;
* `--filter A|B|C`: rows whose name contains one of the alternatives;
  `--scale F`, `--seed S`.

`./run.sh dudect` runs, per build: random vs random (null), fixed vs random,
zero vs random, fixed vs random with DIT = 1, random vs random again, then
fixed vs random with `--same-prep` without and with DIT, and zero vs fixed.
`./run.sh dudect-diag` runs the class-design diagnostics of
`scripts/dudect_diag.sh` (ten hash-level rows) and
`scripts/dudect_diag_chain.sh` (the multi-block `chain_blocks` rows).

`dudect sign-key` / `sign-addrnd` (`--entry internal|internal-checked`) time
whole signing; see RESULTS.md for what the class design can and cannot show.

Timing is only meaningful on a quiet machine. `./run.sh dudect-null` runs the
random-vs-random experiment and the two leaky controls; look at it before
trusting any other timing row, and do not run the trace experiments at the
same time. A row above 4.5 in the fixed-vs-random design is not by itself a
finding about the code: on this CPU, with DIT off, the processor reacts to
repeated and to all-zero data (RESULTS.md, "Timing finding").

### 3. Static facts (`scripts/disasm_check.py`)

Disassembly summary of every `slhdsa` function in the linked binary (integer
division, crypto-extension and SIMD instructions, indirect branches, calls
that leave the crate, and the conditional branches of the functions that
contain the SHA-256 compression code), and an instruction-by-instruction
comparison of the `slhdsa` object code inside this package's dependency rlib
against the rlib produced by `cargo build --release` from the main crate's
own manifest (built into `target*/parent`, so `..` is not written to), plus a
comparison of the constant-data sections.

## How to rerun

Requirements: macOS on Apple Silicon, rustc/cargo (tested 1.100.0), Xcode
command line tools (`objdump`, `nm`, `otool`), `python3` with `venv`, network
access once to `pip install unicorn==2.1.4` (the wheel ships
`libunicorn.2.dylib`; no cmake needed).

```sh
./run.sh <step> [default|hw-sha2|both]     # default: both; THREADS=8 by default
./run.sh setup        # .venv + libunicorn + build, toolchain/source hashes, hwcheck
./run.sh trace        # component trace comparison
./run.sh sign         # whole-signature pinned trace comparison, 8 entry points
./run.sh profile      # whole-signature unconditioned profile
./run.sh disasm       # static facts + rlib comparison
./run.sh dudect-null  # timing noise floor (random-vs-random) and positive controls
./run.sh dudect       # timing, components, eight runs per build (SCALE=0.5 for the recorded runs)
./run.sh dudect-sign  # timing, whole signing
./run.sh dudect-diag  # timing, class-design diagnostics
./run.sh results      # regenerate RESULTS.md from out/ + scripts/RESULTS.template.md
./run.sh all          # setup, trace, sign, profile, disasm, results (no timing)
```

Rough times on the machine of RESULTS.md with 8 threads: see the end of
RESULTS.md.

Outputs go to `out/<variant>/` (the files there are the raw outputs quoted in
RESULTS.md; rerunning overwrites them). Direct invocations (`target-hw/` for
the `hw-sha2` build):

```sh
export UNICORN_LIB_DIR=$(.venv/bin/python -I -c 'import unicorn,os;print(os.path.join(os.path.dirname(unicorn.__file__),"lib"))')
cargo build --release                                            # default build of the crate
cargo build --release --features hw-sha2 --target-dir target-hw  # hw-sha2 build
./target/release/cttrace list
./target/release/cttrace hwcheck
./target/release/cttrace components [--filter SUBSTR] [--scale F] [--threads N] [--seed S]
./target/release/cttrace sign --entry internal-checked [--pubs P] [--secrets K] [--no-mem] [--threads N]
./target/release/cttrace sign-profile --entry internal --pubs N
./target/release/dudect components [--filter A|B] [--scale F] [--fixed-zero] [--dit] [--same-prep] [--reps-mul K] [--classes fixed-random|fixed-fixed|random-random] [--seed S]
./target/release/dudect sign-key --entry internal --n 300   |   ./target/release/dudect sign-addrnd --n 300
```

`cttrace` exits non-zero if any row is not as expected (a secret-varied row
with a divergence, or a control that is not detected). All experiments are
seeded and deterministic except the timing measurements themselves.

## Reading a divergence report

```
first divergence at event #N: last common event: ...; A: <event> | B: <event>
```

An event is `exec block <symbol+off>`, `read/write <address>` (attributed to
the basic block it occurs in; Unicorn only synchronises the guest PC at block
boundaries), or `call-out stub #k` (0 malloc, 1 calloc, 2 realloc, 3 free,
4 posix_memalign, 5 memcpy, 6 memmove, 7 memset, 8 bzero, 9 memcmp). Addresses
`0x40_xxxx_xxxx` are guest heap, `0x50_xxxx_xxxx` guest stack, `0x60_xxxx_xxxx`
I/O buffers. Blocks inside the linker's import-stub section have no symbol of
their own and are attributed by `dladdr` to the nearest preceding symbol.

## Files

* `src/lib.rs` -- wrappers, target table (public/secret byte ranges, trial
  counts), whole-signing entry points, leaky controls, PRNG.
* `src/bin/cttrace.rs` -- Unicorn FFI, image mapping, hooks, stubs, experiments.
* `src/bin/dudect.rs` -- timing harness and statistics.
* `scripts/disasm_check.py`, `scripts/dudect_diag.sh`,
  `scripts/dudect_diag_chain.sh`, `run.sh`, `build.rs` (links `cttrace` to
  libunicorn).
* `scripts/make_results.py`, `scripts/RESULTS.template.md` -- generate
  RESULTS.md from `out/`. The generator computes every quoted number from the
  raw files and refuses to write RESULTS.md if a raw file contradicts an
  outcome the template's prose states; the prose itself was written for the
  2026-11-21 runs.
* `out/default/`, `out/hw-sha2/` -- raw outputs of the recorded runs
  (`build.txt` records the toolchain and the SHA-256 of every source file of
  the crate under test at build time).
