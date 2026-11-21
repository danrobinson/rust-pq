# Constant-time status (2026-11-20)

**Nothing about side channels is proven in Lean.** The workstream was stopped
before any Lean leakage tooling was written. What exists is a source audit, a
design for the Lean proof, and binary-level evidence. The Rust code and the
existing Lean proofs are unchanged.

## Threat model

- **Secret:** SK.seed, SK.prf, `addrnd`, and everything derived from them
  before publication (WOTS/FORS secret values, unrevealed chain values).
- **Public:** PK.seed, PK.root, message, context, the signature, and everything
  a verifier recomputes from (message, public key, signature): R, the digest
  and its FORS/tree/leaf indices, the FORS public key, each layer's XMSS root,
  hence the WOTS digits and chain lengths.
- **Leakage:** branch decisions, loop iteration counts, indices and lengths of
  every array/slice/vec access, allocation and copy sizes, panics, operands of
  checked `+ - *` and of `/ %`, and shift amounts.
- **Property:** key generation's trace is the same for all inputs. Signing's
  trace is a function of (message, PK.seed, PK.root, output signature);
  equivalently, two signing runs that agree on those have the same trace.
  Signing cannot have a trace independent of the secret given public *inputs*
  alone, because R and the WOTS chain lengths depend on the key and are then
  published.

## Source audit (by reading, not machine-checked)

No violation found under the model above, so no Rust change was made.

- All secret bytes enter through `thash`'s message, the HMAC key in `prf_msg`,
  and `chain`'s start value. They are only copied into buffers and hashed.
- SHA-256 uses wrapping adds, rotates and constant shifts on data; its loop
  bounds and indices depend only on message length; `K[i]` is indexed by the
  round counter.
- All checked arithmetic, all branches and all indices are on counters,
  lengths, or declassified values (digest indices, WOTS digits, `idx`).
- The only `==` on arrays is in `ht_verify`, which handles public data.
- Not provided by the crate: zeroisation of secrets; any control over the
  allocator. Buffers holding secrets are freed without wiping.

## Binary-level evidence (evidence, not proof)

In `rust/ct-evidence/` (`RESULTS.md`, `README.md`, `run.sh`). Apple arm64,
macOS 27.2, rustc 1.100.0, default release profile.

- **Trace comparison** of the native release code under Unicorn (basic blocks,
  memory access addresses and sizes, allocator/copy arguments): 2574 secret
  pairs over `sha256`, `hmac_sha256`, `thash`, `prf_msg`, `chain`, `wots_*`,
  `xmss_*`, `fors_*` and full key generation, all identical. Three leaky
  positive controls were all detected.
- **Whole signing:** 32 pairs with fresh secrets and the nine declassified
  values (R, FORS public key, seven XMSS roots) pinned to the first run's: all
  identical. This shows secrets reach the trace only through those nine values;
  that they are public is the audit's argument.
- **Disassembly:** no division, no indirect branches, scalar SHA-256.
- **Timing (dudect-style):** SLH-level components and whole signing show no
  difference with a pseudo-random fixed secret. Bare `sha256` on fully secret
  messages does exceed the threshold (at most 0.13% of call time); it
  disappears with the CPU's data-independent-timing mode (`PSTATE.DIT=1`). The
  cause was not identified. The crate forbids `unsafe` and cannot set DIT.
- Limits: one compiler, target and profile; sampled, not exhaustive; the
  emulator sees no caches, speculation or per-instruction timing; libSystem's
  malloc/memcpy are stubbed (arguments compared, internals not traced).

## Lean proof: designed, not built

No file exists for any of this. The intended design:

1. **Leak monad.** `Leak α := Result (α × Trace)`, with `Trace` a list of
   events (branch tag, index + length, copy/alloc length, arithmetic operands,
   shift amount).
2. **Derivation metaprogram.** For each definition in `Funs.lean`, transform
   its elaborated term into `f_leak`: binds become `Leak.bind`; each
   alternative of every `if`/multi-way `match` is prefixed with a tag event;
   `loop` becomes `Leak.loop`; calls to crate functions become their `_leak`
   versions; each Aeneas primitive stays the same term wrapped as
   `Leak.prim (events args) (prim args)`, with `events` taken from a small
   hand-written table (the trusted leakage model). Unknown fallible primitives
   and branching in pure position are errors. A checker confirms the output
   mentions only whitelisted constants.
3. **Erasure.** A generated theorem per function,
   `Leak.erase (f_leak x) = f x`, so the instrumented code is tied to the
   extracted code by the kernel. Loops and the two recursive functions need a
   lemma that `Result` is a flat order (`ITree.le_ret_cases` is available).
4. **Relational logic.** `CT R x x'`: if both runs return, traces are equal
   and results are related by `R`. Rules for bind, branch, loop, primitives
   (length-equal for secret buffers, equal for public values), plus a tactic.
   One lemma per function; `ht_sign` and `slh_sign_internal` need a manual
   argument that uses equality of the final signatures.
5. **Totality** comes from the existing refinement theorems (no panic under
   `Room`), so the final theorems would be unconditional under `Room`.

Known trust base of that model, had it been built: Charon, Aeneas, rustc; the
primitive event table; pure machine operations (bitwise, casts, wrapping add,
rotates) assumed constant-time; no view of compiler-introduced branches,
caches, allocator internals, or zeroisation.

## Build state

- `rust/src`, `lean/Slhdsa`, `lean/Spec`, `lean/lakefile.toml`: unchanged.
- `cargo test --release` in `rust/`: 6 passed.
- `lake build` in `lean/`: succeeds; the six refinement theorems depend on
  `propext`, `Classical.choice`, `Quot.sound` only.
- `security/` and `scripts/check.sh` were not re-run; nothing they read changed.
