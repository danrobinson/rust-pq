# opt — seed midstate and allocation-free F/H/PRF, still fully verified

An optimised copy of `rust/` + `lean/`. The headline theorems, their
statements, the specification `lean/Spec` and the axioms are unchanged. Every
proof was redone against the new Aeneas translation. Keygen, sign and verify
each run about **2.4×** faster, and a signature needs **half the SHA-256
compressions** (4,404,707 → 2,218,488).

Layout, set up like `multi/`:

- `opt/rust/` is the crate. Only `src/` differs from `rust/`; `Cargo.toml` and the tests are the same.
- `opt/lean/` is an APFS clone of `lean/`. Its `aeneas` path dependency points at `../../.tools/...` (in `lakefile.toml` and `lake-manifest.json`), and it is a separate lake workspace.
- `opt/scripts/extract.sh` runs Charon in `opt/rust` and Aeneas with `-dest opt/lean/Slhdsa`.
- `opt/vectors` is a symlink to `../vectors`.
- `opt/difftest/` holds the differential check (`run.sh`) and the timing harness (`bench.sh`).

## What changed in the Rust (per file)

| file | change |
|---|---|
| `sha256.rs` | `H0` and `compress` are now `pub`. `pad(msg, pre)` writes the bit length of `pre + msg.len()`, so it can pad the tail of a message whose first `pre` bytes (a multiple of 64) are already compressed. New `sha256_from(state, pre, msg)` hashes from any state. New `digest(state)` is the old output loop, moved out. `sha256(msg)` is `sha256_from(&H0, 0, msg)`. `hmac_sha256` is unchanged. |
| `hash.rs` | New `struct Seed { pk_seed: [u8; 16], state: [u32; 8] }`. New `seed_ctx(pk_seed)` builds `PK.seed ‖ 0^48` in a stack `[u8; 64]` and does one `compress(H0, ·)` (**A**). New `thash_short(seed, adrs, m)` for \|m\| ≤ 33 builds `ADRSc ‖ m ‖ 0x80 ‖ 0… ‖ bitlen` in a stack `[u8; 64]` and does one compression from `seed.state`, with no heap allocation (**B**). `thash(seed, adrs, m)` is the general path for `T_len`/`T_k`: it starts from the midstate and calls `sha256_from(&seed.state, 64, ADRSc ‖ m)`. `prf_msg` and `h_msg` are unchanged. |
| `wots.rs` | `pk_seed: &[u8;16]` becomes `seed: &Seed`. `chain` and the PRF calls use `thash_short`. The `T_len` compressions of the public key still use `thash`. |
| `xmss.rs` | `seed: &Seed`. `hash2` builds `left ‖ right` in a stack `[u8; 32]` instead of a `Vec` and calls `thash_short`. |
| `fors.rs` | `seed: &Seed`. `fors_sk_gen` (PRF) and the leaf `F` calls use `thash_short`. `T_k` uses `thash`. |
| `ht.rs` | `seed: &Seed`. Nothing else. |
| `slh.rs` | `slh_keygen_internal`, `slh_sign_internal` and `slh_verify_internal` each call `seed_ctx(pk_seed)` once and pass `&seed` down. The public API (names, signatures, behaviour) is unchanged. |

All compressions still go through the single `sha256::compress(state, data, off)`.
There is no `unsafe`, no new dependency, and `Cargo.toml` is unchanged.

**Profiling note.** After A and B, `compress` takes about 95% of signing time
(2.2 M bare compressions take 325 ms; one signature takes 345 ms). I tried
removing bounds checks in the message schedule and saw no measurable gain, so
I made no further changes. Any further speed-up would have to come from
restructuring `compress` itself, which is not proof-cheap.

## Constant time

Nothing I changed adds secret-dependent control flow.

- `seed_ctx` and the midstate depend only on `PK.seed` (public).
- In `thash_short`, the only length-dependent quantities are `m.len()` (always 16 or 32, fixed by the call site), the indices `22 + len` and `62`/`63`, and the constant bit length.
- Secret inputs (`SK.seed` in PRF, WOTS/FORS chain values) are only copied (`copy_from_slice`) and compressed, exactly as before.
- The removed `Vec` growth was data-independent anyway.
- The loops and branches of `pad`, `sha256_from` and `digest` depend only on lengths.

## How the proofs were adapted (per layer)

`lean/Spec/**` is byte-identical. `Theorems.lean` is byte-identical (see below).
`Types.lean` and `Funs.lean` are regenerated only. Proofs went from 2,353 to
2,553 lines.

- **Sha256**
  - New definitions: `padFrom pre m` (padding of a tail with total length `pre + |m|`) and `hashFrom st p` (fold `compress` over the blocks of `p` from `st`).
  - `pad_spec` is generalised to `pad msg pre ↦ padFrom pre`.
  - `sha256_from_loop_spec` replaces `sha256_loop0_spec`; the initial state is now arbitrary.
  - `digest_spec` (from `digest_loop_spec`, the old `sha256_loop1_spec`) and `sha256_from_spec ↦ ser (hashFrom (wv state) (padFrom pre msg))` are new. `sha256_spec` follows from them via `padFrom_zero`.
  - Spec-level lemmas: `pad_append64`, `hashFrom_append64`, and `sha256_prefix64`, which says SHA-256 of `B ‖ m` with \|B\| = 64 equals `ser (hashFrom (compress H0 B) (padFrom 64 m))`.
- **Hash**
  - `SeedOk s := wv s.state = compress H0 (bytes s.pk_seed ++ 0^48)`.
  - `seed_ctx_spec`: `r.pk_seed = pk ∧ SeedOk r`.
  - `thash_eq` restates `Spec.thash` via the midstate. `thash_spec` now takes `(pk : hash.Seed) (hpk : SeedOk pk)` and keeps the old conclusion with `bytes pk.pk_seed.val`.
  - `thash_short_spec` has the same conclusion under `|m| ≤ 33`. It rests on the new lemmas `toByte8_small`, `padFrom_short` (for \|ADRSc ‖ m\| ≤ 55 the padded tail is exactly that one 64-byte block), `hashFrom_one`, `set_mid` and `setSlice!_mid`, which track the block built on the stack step by step.
- **Wots, Xmss, Fors, Ht**
  - Mechanical: every `(pk : Array U8 16)` became `(pk : hash.Seed) (hpk : SeedOk pk)`, and `bytes pk.val` became `bytes pk.pk_seed.val`. The conclusions still name the same `Spec` functions.
  - Explicit applications pass `hpk`. Inside `step*` it is discharged by assumption.
  - The calls in `Wots` that the Rust now routes through `thash_short` use `thash_short_spec`.
  - `hash2_spec` was re-proved for the stack buffer with `setSlice!_mid`.
- **Slh**: `seed_ctx_spec` supplies `SeedOk` and `seed.pk_seed = pk_seed`. The latter is rewritten into the existing keygen/sign/verify proofs (3 small edits).
- **Basic, Util**: unchanged.

No `sorry`, `admit`, `axiom`, `native_decide` or `bv_decide` anywhere.

## Theorems.lean

```
$ diff lean/Slhdsa/Theorems.lean opt/lean/Slhdsa/Theorems.lean
$                                    # (identical)
```

`cd opt/lean && lake build` ends with:

```
'slhdsa.keygen_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'slhdsa.sign_internal_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'slhdsa.verify_internal_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'slhdsa.sign_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'slhdsa.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'slhdsa.sha256_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3643 jobs).
```

`lake build spectest` also builds (14 jobs). Re-running `opt/scripts/extract.sh`
reproduces `Types.lean` and `Funs.lean` byte for byte.

## Tests

- `cd opt/rust && cargo test --release` passes all 6 tests, including all NIST ACVP vectors (10 keygen, 28 signing, 28 verification).
- `opt/difftest/run.sh [N]` builds one dump program twice, against `rust/` (`difftest/orig`) and against `opt/rust/` (`difftest/new`), and `cmp`s the two transcripts. A transcript contains:
  - every output on all 66 vector cases (keys, signatures and verdicts, not just pass/fail);
  - `sha256`/`hmac_sha256` on 300 lengths;
  - N random keygen + `slh_sign_internal` + `slh_sign` runs, the last with ctx lengths up to 256 to cover the `None` case;
  - 9 verification verdicts per random case: valid; flipped signature bit, internal and external; altered message; altered key; length − 1; length + 1; random junk.

  With N = 40 the transcripts are **identical** (486 lines).

## Timings

Measured with `opt/difftest/bench.sh 5 5`: the same harness built against each
crate, release build, the two alternating, 25 runs each, on the busy machine
(load average about 4–5). The figures are medians in ms and approximate.

| op | `rust/` | `opt/rust/` | speed-up |
|---|---|---|---|
| keygen | 108.5 (102.6–117.5) | 45.1 (43.1–50.8) | 2.41× |
| sign (32-byte message) | 834.2 (794.4–861.5) | 346.0 (333.4–360.7) | 2.41× |
| verify | 0.772 (0.733–0.797) | 0.324 (0.308–0.381) | 2.38× |

SHA-256 compressions were counted with a throwaway instrumented copy of each
crate in a scratch directory, not in the repo:

| op | before | after |
|---|---|---|
| keygen | 580,094 | 292,352 |
| sign | 4,404,707 | 2,218,488 |
| verify | 4,086 | 2,079 |

The speed-up (2.4×) exceeds the compression ratio (1.99×) because the two heap
allocations and copies per call are gone.

## Swap: files to copy

```
opt/rust/src/*.rs              → rust/src/        (fors hash ht sha256 slh wots xmss changed; others identical)
opt/lean/Slhdsa/Types.lean     → lean/Slhdsa/
opt/lean/Slhdsa/Funs.lean      → lean/Slhdsa/
opt/lean/Slhdsa/Proofs/*.lean  → lean/Slhdsa/Proofs/   (Sha256 Hash Wots Xmss Fors Ht Slh changed)
opt/lean/Slhdsa/Theorems.lean  → lean/Slhdsa/      (identical; copying is a no-op)
optionally rust/slhdsa.llbc   ← regenerated by extract.sh
```

Do **not** copy `opt/lean/lakefile.toml`, `opt/lean/lake-manifest.json`
(different relative `aeneas` path), or `lean/Spec` (unchanged).

Effect on other code:

- **`security/E2E`** uses only the six headline theorems, `slhdsa.bytes`, `slhdsa.ht_bytes_injective` and the public `slh.*` functions. All keep their names and statements. I could not build E2E against `opt/` (no `lake` in `security/`), so that is checked by inspection only.
- **`bench/src/bin/profile.rs`** calls *internal* functions whose signatures changed. After the swap it needs `let seed = slhdsa::hash::seed_ctx(&pk_seed);`, then `&seed` in place of `&pk_seed` for `fors_sign`, `ht_sign`, `wots_pk_gen` and `hash::thash`. Use `hash::thash_short` to time the new F/H path. The public-API benchmarks are unaffected.
- **`multi/`** is a separate copy and is unaffected.
