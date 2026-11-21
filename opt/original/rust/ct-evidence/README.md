# ct-evidence: binary-level constant-time evidence for `slhdsa`

This is a standalone cargo package (own `[workspace]`, own `target/`) that
collects **evidence, not proof**, that the machine code rustc emits for the
`slhdsa` crate (SLH-DSA-SHA2-128s, `../src`) has secret-independent control
flow, memory-access addresses and timing. It does not modify the crate under
test and is not built by `cargo build/test` in `..`.

Results of the runs performed on 2026-11-20 are in [RESULTS.md](RESULTS.md).

## Threat model being tested

* Secret: `SK.seed`, `SK.prf`, `addrnd`, and everything derived from them
  before publication (FORS/WOTS secret values, unrevealed chain values).
* Public: `PK.seed`, `PK.root`, message, context, the signature, and
  everything the verifier recomputes: `R`, the message digest and all indices,
  the FORS public key, every XMSS root, hence all WOTS digits/chain lengths.
* Leakage: sequence of executed instruction addresses, sequence of memory
  addresses read/written, and time.

## Two kinds of evidence

### 1. Deterministic trace comparison (`src/bin/cttrace.rs`)

`cttrace` links the `slhdsa` rlib compiled with the default cargo release
profile for `aarch64-apple-darwin` (no profile overrides, i.e. the flags
`cargo build --release` uses in `..`), then **maps its own Mach-O image into a
Unicorn AArch64 emulator at the same addresses** and executes the harness
entry points (`src/lib.rs`, one thin `extern "C" fn(input, output)` wrapper per
function under test) instruction by instruction. So the code that is traced
is the native release machine code, not a rebuild for another target.

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

* `cttrace components` -- for each function, several public configurations
  (public inputs pseudo-random but fixed), and for each several fresh secrets;
  all traces within a configuration must be identical. Includes positive
  controls (`leaky_cmp`, `leaky_table`, `leaky_loop`, defined in this crate
  only) and public-variation controls (varying a *public* input must change
  the trace).
* `cttrace sign` / `sign-ctx` -- whole `slh_sign_internal` / `slh_sign`.
  One cannot hold the signature fixed while varying the key, so this is a
  *declassification-pinned* comparison: run A signs honestly and the tracer
  records the nine 16-byte values that the audit says are the only channel
  from secrets to control flow/addresses, at the instant they are produced
  (`R` = result of `prf_msg`; `PK_FORS` = result of `thash` with ADRS type
  FORS_ROOTS; the seven XMSS roots = results of `thash` with ADRS type TREE at
  height 9). Run B uses the same public inputs (m, PK.seed, PK.root) and
  *different* `SK.seed`, `SK.prf`, `addrnd`, and the tracer overwrites those
  nine results with run A's values (through the emulator API, at function
  return; nothing else is touched). All other intermediate values in run B --
  every FORS secret, every WOTS secret and chain value, every Merkle node,
  the signature body -- differ from run A. Identical traces then show that the
  secrets influence the trace only through those nine values, each of which
  is recomputed by the verifier from (m, pk, signature), i.e. is public.
  Controls: replaying A's values into A must be a no-op; exactly nine values
  must be recorded/pinned; the first recorded value must equal the signature's
  `R`; B's signature body must differ from A's; and without pinning B's trace
  must differ from A's.
* `cttrace sign-profile` -- unconditioned signing runs over random honest keys
  with m and PK.seed fixed; reports which coarse quantities are invariant
  (instruction count, call counts, block histogram).

### 2. dudect-style timing test (`src/bin/dudect.rs`)

Fixed-vs-random Welch t-test on native execution time
(`mach_absolute_time`). Both classes share all public inputs and differ only
in the secret bytes; class of each measurement is random; inputs are prepared
outside the timed region; short functions are called in a loop so that one
measurement is >= ~20 us (the clock ticks at ~42 ns). Statistic: max |t| over
the uncropped test and the 100 dudect percentile croppings; threshold 4.5.
Also reported: the difference of the 10%-trimmed class means (effect size).
Noise floor: the same statistic on null splits (class-1 samples split by
arrival parity, and likewise class 0). Positive controls: `leaky_cmp`,
`leaky_loop`.

Options: `--fixed-zero` (fixed class = all-zero secret instead of one fixed
pseudo-random secret), `--classes fixed-fixed|random-random` (diagnostic class
designs: two different fixed secrets; or both classes fresh random = a true
null experiment), `--dit` (set the Arm `PSTATE.DIT` data-independent-timing
bit on the measuring thread before measuring; the crate itself never sets it).
`scripts/dudect_diag.sh` runs the class-design diagnostics for bare
SHA-256/HMAC/thash without and with DIT.

`dudect sign-key` / `sign-addrnd` time whole `slh_sign_internal`; see
RESULTS.md for what the class design can and cannot show.

### 3. Static facts (`scripts/disasm_check.py`)

Disassembly summary of every `slhdsa` function in the linked binary (integer
division, crypto-extension and SIMD instructions, indirect branches, the
conditional branches inside the compiled `sha256`), and an
instruction-by-instruction comparison of the `slhdsa` object code inside this
package's dependency rlib against the rlib produced by `cargo build --release`
in `..`.

## How to rerun

Requirements: macOS on Apple Silicon, rustc/cargo (tested 1.100.0), Xcode
command line tools (`objdump`), `python3` with `venv`, network access once to
`pip install unicorn==2.1.4` (the wheel ships `libunicorn.2.dylib`; no cmake
needed).

```sh
./run.sh setup        # .venv + libunicorn + cargo build --release        ~1 min
./run.sh trace        # component trace comparison                        ~6 min (12 threads)
./run.sh sign         # whole-signature pinned trace comparison           ~40 min (12 threads)
./run.sh profile      # whole-signature unconditioned profile             ~2 min
./run.sh disasm       # static facts + rlib comparison                    seconds
./run.sh dudect       # timing, components: fixed=random value, fixed=zero, DIT=1   ~35 min, idle machine
./run.sh dudect-diag  # class-design diagnostics (sha256/hmac/thash), +DIT    ~25 min
./run.sh dudect-sign  # timing, whole signing (2 x 600 signatures)        ~20 min
./run.sh results      # regenerate RESULTS.md from out/ + scripts/RESULTS.template.md
./run.sh all          # everything, ~2.5 h
```

Outputs go to `out/` (the files there are the raw outputs of the 2026-11-20
runs quoted in RESULTS.md; rerunning overwrites them). Direct invocations:

```sh
export UNICORN_LIB_DIR=$(.venv/bin/python -c 'import unicorn,os;print(os.path.join(os.path.dirname(unicorn.__file__),"lib"))')
cargo build --release
./target/release/cttrace list
./target/release/cttrace components [--filter SUBSTR] [--scale F] [--threads N] [--seed S]
./target/release/cttrace sign [--pubs P] [--secrets K] [--no-mem] [--threads N]
./target/release/cttrace sign-ctx ...   |   ./target/release/cttrace sign-profile --pubs N
./target/release/dudect components [--filter SUBSTR] [--scale F] [--fixed-zero] [--dit] [--classes fixed-random|fixed-fixed|random-random] [--seed S]
./target/release/dudect sign-key --n 300   |   ./target/release/dudect sign-addrnd --n 300
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
  counts), leaky controls, PRNG.
* `src/bin/cttrace.rs` -- Unicorn FFI, image mapping, hooks, stubs, experiments.
* `src/bin/dudect.rs` -- timing harness and statistics.
* `scripts/disasm_check.py`, `scripts/dudect_diag.sh`, `run.sh`, `build.rs`
  (links `cttrace` to libunicorn).
* `scripts/make_results.py`, `scripts/condense.py`,
  `scripts/RESULTS.template.md` -- generate RESULTS.md from `out/`. The
  template's prose was written for the 2026-11-20 numbers; the generator
  asserts the trace outcomes but does not re-check the prose.
* `out/` -- raw outputs of the recorded runs.
