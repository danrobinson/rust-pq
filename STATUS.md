# SLH-DSA-SHA2, all six parameter sets: status of `rust/`, `lean/`, `lean-hw/`

The single-set crate and proofs (SLH-DSA-SHA2-128s) extended to
SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}. `scripts/check.sh` re-runs every
check (below). This file was written while this tree lived in a subdirectory
`multi` beside the single-set tree, which it replaced on 2026-11-22 (last
section). Throughout, "the single-set crate" / "the single-set tree" is that
tree, git commit `26aa3d8`. Constant time: `lean/CT_STATUS.md`; security:
`security/STATUS.md`, `security-hw/README.md`.

## State (2026-11-22): optimised Rust for six sets, proved correct (default and `hw-sha2` builds)

`rust/` is the optimised implementation of the single-set crate for all six SHA-2
parameter sets, and the Aeneas translations of its default build and of its
`hw-sha2` build are proved to compute FIPS 205 (`lean/Spec`) for every function
the crate exports, in every set (the `hw-sha2` one relative to `lean-hw`'s model of the
processor instructions, taken unchanged from the single-set tree's `lean-hw`).

| Item | State |
|---|---|
| Same modules and public functions as the single-set tree's `rust/src` (`api`, `encoding`, `no_std` + alloc, `hw-sha2` with the same runtime detection), six sets | done (generic functions, plus per-set typed wrappers with the single-set crate's signatures) |
| `chain_blocks`, seed-state precomputation, `sha256_from`, in-place `H_msg`, stack HMAC key blocks, FORS batches and joint climbing, on the SHA-256 paths of every set | done |
| SHA-512 for `H`, `T_l`, `H_msg`, `PRF_msg` (n = 24, 32) | done, portable |
| `PRF_msg`'s inner HMAC digest | kept on the stack (this stage; see "Secrets and constant time") |
| `hw-sha2` chain kernel for n = 24 and 32 | done (one kernel, generic in `N`; the wrappers are unchanged); proved |
| Hardware SHA-512 (FEAT_SHA512) | part of `hw-sha2` since 2026-11-22 (own run-time test), translated and **proved** (section "Hardware SHA-512") |
| Tests, two builds | all pass: 87 default, 90 `hw-sha2` |
| Charon/Aeneas, default build | no opaque function, no axiom, no `External` file |
| Charon/Aeneas, `hw-sha2` build | only `sha256::hw::arm` and `sha512::hw::arm` left out (32 declarations, defined by the model in `lean-hw/Slhdsa/{Types,Funs}External.lean` over `lean-hw/Arm.lean`; the SHA-256 part is the single-set tree's, unchanged) |
| **Refinement proofs, default build** | **done**: `lean/Slhdsa/Proofs` (18 files, about 8,500 lines); headline files `Theorems.lean` (37 theorems), `ApiTheorems.lean` (66), `EncodingTheorems.lean` (72), `Compat128.lean` (12); every one depends only on `propext`, `Classical.choice`, `Quot.sound` (checked by `scripts/check.sh`); no `sorry`, `axiom`, `native_decide`, `bv_decide` |
| Correctness of the specification (`lean/Spec/Keys.lean`, `Correctness.lean`) | done, generically for every `p` with `p.Valid` |
| 128s against the single-set specification | done: `lean/Spec/Compat128.lean` proves `Spec.f Spec.sha2_128s = Spec128.f` for every function, where `Spec128` (`lean/Spec/Old128.lean`) is a verbatim copy of the single-set tree's specification; `Slhdsa/Compat128.lean` restates the 128s headlines against it |
| **Refinement proofs, `hw-sha2` build** | **done**: `lean-hw/` proves the same 187 headline theorems (the four headline files are links to `lean/`'s) about the `hw-sha2` translation, all six sets, on the three standard axioms; new proofs only for the chain kernel generic in `N` and the hand-off (`lean-hw/Slhdsa/Proofs/ChainTop.lean`, `Hw/{ChainModel,ChainLane,ChainRun,ChainLoop,ChainMain,ChainAll,Chain,Guard}.lean`, about 2,400 lines); guard theorems for `Arm.haveSha2 = false`; since 2026-11-22 also the SHA-512 kernel (`Hw512/{Rounds,Wrappers,Compress,Guard}.lean`, `Compress512Top.lean`) and guards for `Arm.haveSha512 = false`; the wrapper model passes `ArmTest` (2,961 cases, 0 mismatches) |
| The adapter's decisions (`rust/src/adapter.rs`, 2026-11-22) | translated in both builds; proved in `lean/Slhdsa/Proofs/Adapter.lean`, headline list `AdapterTheorems.lean` (14); `compat/` only forwards (its remaining surface: `compat/README.md`) |
| Constant-time proofs, security link | both builds (later stages, not described here): `lean/CT_STATUS.md`, `security/STATUS.md`, `security-hw/README.md` |

## Design, and why

**Mechanism: the hash length `n` is a const generic `N`; everything else is a
runtime `p: &Params`.** Every function of the scheme takes `N`, and `p`
where it needs more of the parameter set than `n`, e.g.
`wots_pk_gen::<N>(sk_seed: &[u8; N], seed: &Seed<N>, adrs)` and
`fors_sign::<N>(p, md, sk_seed, seed, adrs)`; callers pass `N = p.n` (the
per-set modules do, and a test checks it). Chosen by experiment, on the
criteria in order:

1. *Translation.* A scratch crate with a const-generic struct (`Seed<N>`),
   `[u8; N]` arguments and results, `if N == 16` branches and slices of
   fixed-size block arrays translated with no opaque item and typechecked;
   so did the full crate in both builds (below). Rust's stable const generics
   cannot write `[u8; 2 * N]`, so the derived sizes (`len = 2n + 3`, `k`) are
   runtime values and the arrays that depend on them are sized for the largest
   set (`params::LEN_MAX = 67`, `params::K_MAX = 35`) and used through
   `&mut blocks[0..len]` — the pattern the single-set crate's FORS batch already uses.
2. *Proofs.* With `[u8; N]` the Lean types are `Array U8 N`, so hash values
   keep their length in the type, as the optimised proofs of the single-set tree's `lean` have
   it with `16#usize`; the generalisation of those proofs replaces the
   literal 16 by `N` (with `N ∈ {16, 24, 32}`) rather than switching to
   slices with length side conditions. The treatment of
   `Params`, `Valid` and SHA-512 carries over, since `Params` is unchanged. A
   runtime `n` with `[u8; 32]` buffers would have put "the first `n` bytes"
   into every statement; per-set instantiation of shared source would have
   given six copies of every definition to prove. One kernel, generic in `N`,
   is translated once (Aeneas keeps const generics as parameters).
3. *Speed.* Monomorphisation gives each set code specialised to its `n`;
   `if N == 16` branches fold away. For 128s the generated code is the same
   algorithm as the single-set crate's, and measures within 2.5%.

Other decisions:
- **Hash selection** branches on `N` (a parameter): `N == 16` is SHA-256
  everywhere; otherwise `H` is one SHA-512 block from the SHA-512 seed state
  (`hash::thash_pair`), `T_len` hashes a stack buffer (640 bytes for SHA-256,
  2304 for SHA-512), `T_k` (FORS roots) goes through `sha512_from`, `PRF_msg`
  is HMAC-SHA-512 with both key blocks on the stack, and `H_msg` hashes a long
  message in place with SHA-512 and MGF1-SHA-512. F and PRF are SHA-256 with
  the SHA-256 seed state for every set, so all chain and FORS-leaf work goes
  through `chain_blocks::<N>`.
- **`Seed<N>`** holds `PK.seed`, the SHA-256 state after
  `PK.seed ‖ 0^(64−n)`, and for `n > 16` the SHA-512 state after
  `PK.seed ‖ 0^(128−n)` (zero and unused for 128s; not computed there).
- **FORS for n > 16**: the leaves are still two `chain_blocks` steps; the
  levels above, and the climbs in `fors_pk_from_sig`, call `thash_pair` node
  by node (one SHA-512 block each), since SHA-512 has no chain kernel.
- **`hw-sha2` kernel, generic in `N`.** The value occupies block bytes
  22..22 + N, starting and ending in the middle of a word. For N > 16 a
  second vector `xb` carries the value's words 4.. (for N = 24 with its upper
  two words kept zero), the rebuilt message words extend to W11 (N = 24) or
  W13 (N = 32) by the same shift/extract pattern, the fixed words are masked
  per `N`, N/4 words of the result are kept (so the last `SHA256H2` is done
  for N > 16), and for N = 24 the block bytes 46..54 that follow the value
  are written back from a saved `tail`. The eighteen wrappers of `hw::arm`
  are unchanged, so the trusted model of the single-set tree's `lean-hw` still describes them;
  the kernel is proved for the three values of `N` (section "The proofs
  (`hw-sha2` build)").
- **Keys** are slices in the generic functions (`sk: &[u8]` of 4n bytes;
  key generation writes into `sk: &mut [u8]`, `pk: &mut [u8]`), so nothing
  secret is returned by value from the generic code; the per-set modules give
  the single-set crate's array signatures.
- **Per-set modules** `sha2_128s` … `sha2_256f` (generated by one macro in
  `sets.rs`) hold `params` (`N`, `PK_BYTES`, `SK_BYTES`, `SEED_BYTES`,
  `SIG_BYTES`, `PKCS8_BYTES`, `SPKI_BYTES`, `PARAMS`), the internal and pure
  functions (`slh_keygen_internal`, `slh_sign_internal`,
  `slh_verify_internal`, `slh_sign`, `slh_verify`), the interface functions
  (`keygen`, `public_key`, `sign`, `sign_deterministic`, `verify`) and the encodings
  (`PKCS8_PREFIX`, `SPKI_PREFIX`, `secret_key_from`, `public_key_from`,
  `signature_len_ok`, `secret_keys_equal`, `pkcs8_encode`/`decode`,
  `spki_encode`/`decode`), with re-export modules `api` and `encoding` so the
  paths are the single-set crate's (`slhdsa::sha2_128s::api::keygen`, …). The functions
  are defined at the level of the set's module because submodules named
  `api` and `encoding` gave Lean names (`sets.sha2_128s.api.keygen`) that
  shadow the generic `api.keygen` they call: the first translation failed to
  typecheck for exactly that reason.
- **Encodings**: the DER prefixes are literal per set (20 bytes for n = 16,
  24; 22 for n = 32, whose lengths need the long form). The generic code is
  `encoding::der_encode` / `der_decode` with the prefix as an argument. The
  OIDs were taken from `const_oid::db::fips205` (…3.4.3.20–25 for 128s, 128f,
  192s, 192f, 256s, 256f), and a test compares each set's PKCS#8 and SPKI
  bytes with RustCrypto's `to_pkcs8_der` / `to_public_key_der`.
- `#[inline(never)]` as in the single-set crate on the functions that handle the seed
  (generic `slh_keygen_internal`, `slh_sign_internal`, `api::keygen`, and the per-set wrappers of
  the same names).

## Files changed

`rust/`: `Cargo.toml` (features `hw-sha2`, `hw-sha512`; dev-dependencies
`slh-dsa =0.2.0-rc.5`, `signature`, `pkcs8`, `sha2` with `compress`);
`src/` all files rewritten (`address.rs` and the portable part of
`sha256.rs` are copies of the single-set crate's), new `api.rs`, `encoding.rs`;
`tests/acvp.rs` rewritten, new `tests/api.rs`, `tests/compress.rs`,
`tests/rustcrypto.rs`. `lean/Slhdsa/{Types,Funs}.lean` regenerated. New
`lean-hw/` (lakefile, manifest, generated `Slhdsa/{Types,Funs}.lean`, links to
the single-set tree's `lean-hw/Slhdsa/{Types,Funs}External.lean`). `scripts/check.sh`
rewritten, new `scripts/extract-hw.sh`.

This stage (proofs): `rust/src/hash.rs` (`prf_msg`: stack outer block),
`rust/src/sha256.rs` (hardware test no longer writes the record);
`lean/Slhdsa/{Types,Funs}.lean` and `lean-hw/Slhdsa/{Types,Funs}.lean`
regenerated; `lean/Slhdsa/Proofs/*` rewritten for the new code (new
`Sha256Core`, `CompressTop`, `ChainTop`, `HashMsg`, `Api`,
`Encoding`); `lean/Slhdsa/Theorems.lean` regenerated, new
`ApiTheorems.lean`, `EncodingTheorems.lean`, `Compat128.lean`;
`lean/Slhdsa.lean`; new `lean/Spec/{Keys,Correctness,Old128,Compat128}.lean`,
`lean/Spec.lean` imports `Keys`; `scripts/check.sh`; this file.

Stage `hw-sha2` proofs: `lean-hw/lakefile.toml` (`Spec` compiled in place
from `../lean`; the `Slhdsa` library with its default root); new links
`lean-hw/Slhdsa.lean`, `lean-hw/Slhdsa/{Theorems,ApiTheorems,EncodingTheorems,Compat128}.lean`,
`lean-hw/Slhdsa/Proofs/*.lean` (16 files now, to `../lean/Slhdsa/Proofs`),
`lean-hw/Slhdsa/Proofs/CompressTop.lean` and
`lean-hw/Slhdsa/Proofs/Hw/{Model,Rounds,Compress,Wrappers}.lean` (to
the single-set tree's `lean-hw/Slhdsa/Proofs`), `lean-hw/ArmTest.lean` (to
the single-set tree's `lean-hw/ArmTest.lean`); new files `lean-hw/Slhdsa/Proofs/ChainTop.lean`,
`lean-hw/Slhdsa/Proofs/Hw/{ChainModel,ChainLane,ChainRun,ChainLoop,ChainMain,ChainAll,Chain,Guard}.lean`;
`scripts/check.sh`; this file. No Rust change, no change outside the six-set tree;
the translations were not changed (re-extracted by `scripts/check.sh`, same
output).

## Tests

All pass, run on this machine (Apple M5 Ultra) in two builds: default and
`--features hw-sha2`; and `hw-sha2` again with
`RUSTFLAGS="-C target-feature=-sha2,-sha3"` (the runtime-detection path Linux
takes). (Until 2026-11-22 the unproved SHA-512 backend was a separate feature
`hw-sha512`, tested in two more builds.)

| file | tests | what |
|---|---|---|
| `acvp.rs` | 29 | per set (×6): ACVP keyGen 10/10 (also through `keygen`, `public_key`), sigGen 28/28 (each also through the `api` functions), sigVer 28/28, round trip and tampering; Table 2 sizes and `N = PARAMS.n`; SHA-256, SHA-512 (also `sha512_from`), HMAC-SHA-256/512 against `sha2`/`hmac`; `PRF_msg` and `H_msg` of all six sets against HMAC and MGF1 written with `sha2`/`hmac`, message lengths 0..140 and others; until 2026-11-22 also 128s byte-identical to the single-set crate (keygen, both `api::keygen`, `public_key`, `slh_sign_internal`, `slh_sign`, the `api` signers, verdicts on 10 signature variants through three verifiers, both prefixes, PKCS#8/SPKI encode and decode, byte conversions, `secret_keys_equal`; test removed with that crate) |
| `api.rs` | 30 | from the single-set tree's `rust/tests/api.rs`, 5 tests ×6 sets: `keygen` is the internal function on the three seeds; the interface signers return the signature of `slh_sign` / `slh_sign_internal`, which verifies; contexts over 255 bytes refused; a damaged key (bytes in SK.seed, PK.seed, PK.root) gives a signature that does not verify, while a changed SK.prf does not matter; the top tree's root is `PK.root` |
| `compress.rs` | 10 (11 with `hw-sha2`, 12 with both) | the single-set tree's `rust/tests/compress.rs` ported: `compress` on 200,000 random and 2,565 edge cases; `chain_blocks::<N>` for N = 16, 24, 32 against a reference on random blocks with uniform, mixed, single-step, empty, reversed and carry-crossing ranges, batch sizes 0..41, 64, 70, 128, 140, equal and unequal block heads; chain independence; panics; SHA-512 `compress` on 50,000 random cases; the backends are active where the CPU has them |
| (unit) | 0 (1 with `hw-sha2`) | `sha256::hw::vectors`: the wrappers against the record `vectors/arm-wrappers.txt` |
| `rustcrypto.rs` | 18 | per set (×6) against `slh-dsa` 0.2.0-rc.5: same keys from the same seeds; byte-identical signatures (internal hedged and deterministic, pure with context hedged and deterministic, through `api`); each verifies the other's; both reject the same tampering; PKCS#8 and SPKI bytes identical, each decodes the other's; OID equals `const_oid::db::fips205`'s; encoder/decoder/conversion edge cases |

Also run, outside the repository: the single-set tree's `compat`'s whole test suite (including
the 86-result drop-in comparison with RustCrypto, `wipe.rs` and `heap.rs`)
against this crate's 128s, through a scratch shim crate that exposes
`sha2_128s` under the single-set crate's paths: all pass, default and `hw-sha2`. The
unscrubbed stack depth of keygen plus signing (twice) was 14,024 bytes
(the single-set crate: 14,136); the adapter run left 0 of 208 searched secret forms.
And `cargo build --target aarch64-unknown-none` for the library: default,
`hw-sha2`, `hw-sha2` with `+sha2` (and, on 2026-11-22, default, `hw-sha2` and `hw-sha2` with
`+sha2,+sha3` again).

## Translation (Charon + Aeneas)

- `scripts/extract.sh` (default build) → `lean/Slhdsa/{Types,Funs}.lean`
  (54 + 6,862 lines): 0 `axiom`, 0 `opaque`, no `External` template, no
  `sorry`.
- `scripts/extract-hw.sh` (`--features hw-sha2`, `--opaque
  'slhdsa::sha256::hw::arm'`) → `lean-hw/Slhdsa/{Types,Funs}.lean`: 0 `axiom`
  or `opaque` in the generated files; Aeneas left out 21 declarations (the
  vector type, its `clone`, `panic_bounds_check`, and the eighteen wrappers),
  every one defined in the single-set tree's `lean-hw/Slhdsa/{Types,Funs}External.lean`, which
  `lean-hw` holds. `lake build` there builds it and its proofs
  (3,711 jobs).
- Since 2026-11-22 the `hw-sha2` build includes the SHA-512 backend: Aeneas leaves out 32
  declarations (the 21 above, the SHA-512 vector type and the ten wrappers of
  `sha512::hw::arm`), all defined in `lean-hw/Slhdsa/{Types,Funs}External.lean`.

## Measurements

Apple M5 Ultra, release builds, scratch harness (not in the repository)
calling the per-set `api` functions and RustCrypto's `slh-dsa` 0.2.0-rc.5 on
a 32-byte message with an empty context: keygen and sign are medians of 5
single calls, verify of 5 batches of 20, each run 3 times in alternating
order of the three builds; the tables give the median of the 3 runs. Load
average 1.4–1.8 during the runs (another agent's Lean builds); the spread of
signing time between runs was at most 2.7% (portable) and 1.3% (hardware).

**128s against the single-set crate** (same harness, the two crates interleaved, 7 rounds
each run; median over runs of the per-run difference, range in brackets):

| build | keygen | sign | verify |
|---|---|---|---|
| portable | +2.2% (+1.1 … +2.5) | +1.0% (+0.9 … +1.2) | −0.3% (−0.6 … +1.3) |
| `hw-sha2` | +0.8% (+0.5 … +1.0) | +0.6% (+0.5 … +0.8) | +1.0% (+0.4 … +1.1) |

Absolute, `hw-sha2`: keygen 3.93 ms, sign 30.29 ms, verify 34.9 µs
(the single-set crate in the same runs: 3.90 ms, 30.11 ms, 34.5–34.8 µs; the reference
numbers 3.91 ms / 30.20 ms / 35.35 µs). Portable: 40.2–40.7 ms, 309–310 ms,
309–311 µs (the single-set crate: 39.7 ms, 306–308 ms, 307–312 µs). Where the portable
keygen excess comes from is not isolated: the N = 16 instance of
`chain_blocks_portable` is the same instruction sequence as the single-set crate's up
to register allocation (310 against 306 lines of disassembly, `compress`
inlined in both, no extra calls), and the extra work of the `LEN_MAX` arrays
(about 2 KB more zeroing per WOTS+ key, against ≈ 78 µs per key) is two
orders of magnitude too small to explain 2%. Code placement is the likely
cause; that is a guess.

**All six sets.** "RC" is RustCrypto in the same binary. In the portable
build RustCrypto was compiled with `--cfg sha2_backend="soft"` (portable
SHA-2, as the single-set tree's `bench` does); in the two hardware builds it uses `sha2` 0.11's
own run-time choice (hardware SHA-256 and SHA-512 on this CPU).

Portable (this crate: no features):

| set | keygen | sign | verify | RC keygen | RC sign | RC verify |
|---|---|---|---|---|---|---|
| 128s | 40.85 ms | 310.9 ms | 322.8 µs | 29.37 ms | 225.7 ms | 233.7 µs |
| 128f | 619.8 µs | 14.77 ms | 943.4 µs | 463.0 µs | 10.80 ms | 660.0 µs |
| 192s | 58.35 ms | 550.6 ms | 451.5 µs | 43.36 ms | 399.7 ms | 328.6 µs |
| 192f | 915.0 µs | 24.42 ms | 1.28 ms | 677.2 µs | 17.71 ms | 935.3 µs |
| 256s | 38.69 ms | 494.6 ms | 667.5 µs | 28.59 ms | 354.5 ms | 484.6 µs |
| 256f | 2.42 ms | 50.29 ms | 1.33 ms | 1.80 ms | 36.69 ms | 974.8 µs |

`--features hw-sha2` as it was before 2026-11-22 (SHA-512 portable):

| set | keygen | sign | verify | RC keygen | RC sign | RC verify |
|---|---|---|---|---|---|---|
| 128s | 3.93 ms | 30.29 ms | 36.4 µs | 8.30 ms | 62.55 ms | 64.5 µs |
| 128f | 61.0 µs | 1.51 ms | 99.3 µs | 128.7 µs | 2.99 ms | 180.5 µs |
| 192s | 6.88 ms | 115.5 ms | 119.2 µs | 12.53 ms | 124.6 ms | 109.0 µs |
| 192f | 105.5 µs | 4.41 ms | 241.1 µs | 192.4 µs | 5.41 ms | 288.0 µs |
| 256s | 4.74 ms | 126.6 ms | 170.2 µs | 8.32 ms | 114.5 ms | 156.5 µs |
| 256f | 291.7 µs | 9.40 ms | 271.7 µs | 513.5 µs | 11.15 ms | 299.6 µs |

`--features hw-sha2,hw-sha512` before 2026-11-22 (the same SHA-512 kernel as today's `hw-sha2`, then a separate, unproved feature):

| set | keygen | sign | verify | RC keygen | RC sign | RC verify |
|---|---|---|---|---|---|---|
| 128s | 3.93 ms | 30.37 ms | 36.0 µs | 8.30 ms | 62.64 ms | 64.2 µs |
| 128f | 60.5 µs | 1.50 ms | 98.7 µs | 127.9 µs | 3.01 ms | 180.6 µs |
| 192s | 6.15 ms | 67.86 ms | 65.5 µs | 12.50 ms | 124.5 ms | 108.1 µs |
| 192f | 94.8 µs | 2.94 ms | 161.3 µs | 192.4 µs | 5.39 ms | 288.2 µs |
| 256s | 4.10 ms | 65.26 ms | 94.6 µs | 8.43 ms | 114.6 ms | 156.7 µs |
| 256f | 255.0 µs | 6.01 ms | 172.1 µs | 514.5 µs | 11.21 ms | 300.7 µs |

(The 128s rows of the six-set tables come from separate calls and differ
slightly from the interleaved comparison above, e.g. verify 36.4 against
34.9 µs.)

Reading: portable, this crate is 1.33–1.43× slower than RustCrypto's
portable build in every set, the same ratio as the single-set crate (its portable
SHA-256 compression is slower per block than the `sha2` crate's). With
`hw-sha2` it is faster than RustCrypto in every operation of the 128 and f
sets and in 192s keygen and signing, and slower in 192s verification and all
of 256s except keygen — because SHA-512 was still portable there.

`--features hw-sha2` since 2026-11-22 (verified SHA-512 backend), `compat/examples/timing.rs`
(through the adapter, deterministic signing of a 31-byte message, medians of 7 runs, 31 for
verify; RustCrypto in the same binary), two runs, load average 1.8–2.7, second run within 1.5%
of the first; first run:

| set | keygen | sign | verify | RC keygen | RC sign | RC verify |
|---|---|---|---|---|---|---|
| 128s | 3.95 ms | 30.39 ms | 34 µs | 8.29 ms | 62.61 ms | 57 µs |
| 128f | 75 µs | 1.53 ms | 95 µs | 129 µs | 2.99 ms | 171 µs |
| 192s | 6.13 ms | 67.68 ms | 66 µs | 12.54 ms | 124.8 ms | 111 µs |
| 192f | 109 µs | 2.92 ms | 163 µs | 193 µs | 5.40 ms | 292 µs |
| 256s | 4.11 ms | 65.10 ms | 92 µs | 8.40 ms | 115.6 ms | 156 µs |
| 256f | 269 µs | 6.05 ms | 168 µs | 535 µs | 11.19 ms | 291 µs |

So the verified backend signs 192s in 67.7 ms and 256s in 65.1 ms, the times of the unproved
one (67.9 and 65.3 ms above; it is the same kernel, restructured only in that its store wrapper
writes two vectors and the caller joins the halves).

**How much SHA-512 takes in the 192/256 sets** (`hw-sha2` build). Counted
with an instrumented scratch copy: SHA-512 compressions per keygen / sign /
verify are 5,632 / 317,940 / 379 (192s), 88 / 10,344 / 561 (192f), 4,864 /
399,344 / 526 (256s), 304 / 23,054 / 703 (256f) — nearly all of signing's
are the `H` of the FORS trees (one block per node) and the `T_len` of the
WOTS+ keys. A portable compression costs 179.6 ns (median of 7 runs of 10^6
calls). So SHA-512 is about 15–19% of key generation, 42–57% of signing and
42–57% of verification in these sets:

| set | keygen | sign | verify | measured saving with hardware SHA-512 (keygen / sign / verify) |
|---|---|---|---|---|
| 192s | 15% | 49% | 57% | 11% / 41% / 45% |
| 192f | 15% | 42% | 42% | 10% / 33% / 33% |
| 256s | 18% | 57% | 56% | 13% / 48% / 44% |
| 256f | 19% | 44% | 47% | 13% / 36% / 37% |

(Share = count × 179.6 ns / measured time; the measured saving is what the
hardware backend actually removed, at about 30 ns per compression.) More
would need what the SHA-256 path has, several independent hashes
interleaved in the unit (the `H` of one FORS level, and the climbs of the k
trees, are independent); that was not tried.

## Hardware SHA-512 (part of `hw-sha2` since 2026-11-22)

`rust/src/sha512.rs`, module `hw`, built with `hw-sha2`: ten wrappers in `hw::arm` around the
FEAT_SHA512 intrinsics (`available`, `load_words`, `store_words`, `load_be`, `add`, `ext1`,
`sha512h`, `sha512h2`, `sha512su0`, `sha512su1`; each one to three intrinsics), and a forty-step
`compress_block` in the Aeneas subset, entered by `sha512::compress` after its own run-time test
(`std::arch::is_aarch64_feature_detected!("sha3")`, or the build's target features where the
target guarantees them or has no operating system), with the portable `compress_portable` as
the fallback. One block at a time, no multi-lane kernel. A CPU with the SHA-256 and without the
SHA-512 instructions gets hardware SHA-256 and portable SHA-512. Until 2026-11-22 this kernel was
a separate, untranslated feature `hw-sha512`; folding it into `hw-sha2` keeps one hardware
translation (`lean-hw`) and one proof tree.

Proved (`lean-hw/Slhdsa/Proofs/Hw512`, `Compress512Top.lean`): `hw_compress_block512_spec`
(with `Arm.haveSha512 = true`, `compress_block` is FIPS 180-4's SHA-512 compression function on
the block), `hw_compress512_spec` (whenever `hw::compress` returns a state it is that function on
`data[off..off + 128]`), `S512.compress_spec` (the default build's statement of
`sha512::compress`, whichever the feature test answers), and the guards
`compress_block512_undef`, `compress_block512_no_spec` (without the instructions the kernel
fails, so no postcondition holds of it). The model of the four instructions is in
`lean-hw/Arm.lean` (`SHA512H`, `SHA512H2`, `SHA512SU0`, `SHA512SU1`, `ADD2`, `EXT1`, from the
Arm ARM pseudocode); `ArmTest` checks it against 1,216 recorded calls of the ten wrappers
(`vectors/arm-wrappers.txt`, lines 1,746–2,961). Constant time: `lean-hw/Ct/Compress512Top.lean`.

## Secrets and constant time

No branch, index or length depends on a secret beyond those of the single-set crate. The
new branches are on `N` (a const generic), on parameters (`p.k`, `p.a`,
`p.d`, `p.hp`), on message, context and buffer lengths, on public digest
digits and tree indices, and in the hardware kernel on `N` and the slot
schedule (step ranges, which are public). The kernel's cache of the first
rounds is keyed on the first 16 block bytes, an address prefix, as before.
`der_decode` returns early on a prefix mismatch, like the single-set crate's
`pkcs8_decode` (the prefix is not secret). Secret values are on the stack in the
same places as in the single-set crate; the SHA-512 key blocks of `PRF_msg` are on the
stack too. Nothing of this has been checked by the constant-time machinery of
the single-set tree's `lean/Ct` (at the time it had not been run on this tree; it has since, `lean/CT_STATUS.md`); the compat stack and heap
searches above were run for 128s only.

`PRF_msg` (this stage): the HMAC inner digest `H((K ⊕ ipad) ‖ opt_rand ‖ M)`,
which depends on `SK.prf`, no longer reaches the heap. `sha256_from` /
`sha512_from` copy the tail of their message into a heap `Vec` for padding,
and the outer hash used to go through them; now `prf_msg` writes the final
outer block on the stack (digest ‖ `0x80` ‖ zeros ‖ the bit length of key
block + digest: `0x0300` for SHA-256, `0x0600` for SHA-512) and calls
`compress` on it directly. The single-set crate kept the old form to the end, so its documentation's "nothing derived from the secret seed is
written to the heap" is still not literally true of it.

## The proofs (default build)

`cd lean && lake build` builds everything below (the default target is
`Slhdsa`, which imports all of it). The statements are about the Aeneas
translation of `rust/` without features (`lean/Slhdsa/Funs.lean`,
regenerated at this stage) and the generic FIPS 205 transcription `lean/Spec`.

### Headline statements, SLH-DSA-SHA2-128s (verbatim)

`lean/Slhdsa/Theorems.lean`, lines 94–137 (the other five sets follow at
lines 143–404 with their key sizes, and with `Room m.length 304` / `561` for
the n = 24, 32 sets):

```lean
theorem keygen_correct (sk_seed sk_prf pk_seed : Array U8 16#usize) :
    ∃ sk pk, sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (bytes sk.val, bytes pk.val) =
        Spec.slhKeygenInternal Spec.sha2_128s (bytes sk_seed.val) (bytes sk_prf.val)
          (bytes pk_seed.val)

theorem sign_internal_correct (m : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 152) :
    ∃ sig, sets.sha2_128s.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val =
        Spec.slhSignInternal Spec.sha2_128s (bytes m.val) (bytes sk.val) (bytes addrnd.val)

theorem verify_internal_correct (m sig : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 152) :
    sets.sha2_128s.slh_verify_internal m sig pk =
      ok (Spec.slhVerifyInternal Spec.sha2_128s (bytes m.val) (bytes sig.val) (bytes pk.val))

theorem sign_correct (m ctx : Slice U8) (sk : Array U8 64#usize)
    (addrnd : Array U8 16#usize) (hm : Room m.length 409) :
    ∃ r, sets.sha2_128s.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.sha2_128s (bytes m.val) (bytes ctx.val) (bytes sk.val)
          (bytes addrnd.val)

theorem verify_correct (m sig ctx : Slice U8) (pk : Array U8 32#usize)
    (hm : Room m.length 409) :
    sets.sha2_128s.slh_verify m sig ctx pk =
      ok (Spec.slhVerify Spec.sha2_128s (bytes m.val) (bytes sig.val) (bytes ctx.val)
        (bytes pk.val))
```

`bytes` maps machine bytes to the specification's; `Room len slack` is
`len + slack ≤ Usize.max ∧ len + slack < 2 ^ 61` (`Proofs/Basic.lean`), the
only hypothesis. Also in `Theorems.lean`: `sha256_correct`, `sha512_correct`
(hypothesis `msg.length + 144 ≤ Usize.max`), and `generic.*`, the five
statements for the generic functions at any `p : params.Params` with
`PN p N` (`(paramsS p).Valid ∧ p.n = N`), key slices of length `4N` / `2N`,
and `Room m.length (msgSlack N)` (`msgSlack n = if n = 16 then 152 else 304`;
`+ 257` for the pure functions). The per-set theorems discharge `PN` from
`Spec.sha2_*_valid` and the set's `PARAMS`.

`lean/Slhdsa/ApiTheorems.lean`: for each set 11 statements of
the single-set tree's `lean/Slhdsa/ApiTheorems.lean` (completeness of signing with generated
keys; `keygen`, `public_key`, `sign`, `sign_deterministic`, `verify`), on top of the generic
`Spec.slh_complete_internal`, `Spec.slh_complete`, `Spec.keygen_keyOk` of
`lean/Spec/Correctness.lean` (all for any `p` with `p.Valid`).
`lean/Slhdsa/EncodingTheorems.lean`: for each set the 12 statements of
the single-set tree's `lean/Slhdsa/EncodingTheorems.lean`, with that set's DER prefixes written
out as literal byte lists (OIDs 2.16.840.1.101.3.4.3.20–25; 20-byte prefixes
for n = 16, 24, 22-byte for n = 32).

### Against the 128s tree

The per-set statements have the shape and the hypotheses of the single-set tree's `lean` (for
128s the same `Room` constants 152 / 409; no new hypothesis). Two
differences are forced: the Rust function is this crate's
(`sets.sha2_128s.slh_sign` rather than `slh.slh_sign`), and the
specification is the generic one at a parameter set. For the latter,
`lean/Spec/Old128.lean` is a verbatim copy of the single-set tree's `lean/Spec/SlhDsa.lean` and
of its definitions `KeyOk`, `skPk`, in namespace `Spec128` (only the definitions that do not
depend on the parameter set, which are character-for-character the same, are
shared with `Spec`), `lean/Spec/Compat128.lean` proves
`Spec.f Spec.sha2_128s = Spec128.f` for every function (`slhSignInternal_eq`,
`slhSign_eq`, `KeyOk_eq`, …), and
`lean/Slhdsa/Compat128.lean` restates all 12 128s theorems of `Theorems.lean`
and `ApiTheorems.lean` that mention the specification against `Spec128`, i.e.
literally the single-set tree's `lean` statements up to the name of the Rust function. The
remaining 4 `ApiTheorems` and all `EncodingTheorems` mention no
specification function and have the single-set tree's `lean` statements as they are.

### Files

`lean/Slhdsa/Proofs`: `Basic`, `Params`, `Sha256Core` / `CompressTop` /
`Sha256` (copied from the single-set tree's `lean`: the portable SHA-256 is the same code),
`Sha512` (`compress`, `pad` with a prefix, `sha512_from`, `digest`, HMAC),
`Util`, `Hash` (addresses, the SHA-256 and SHA-512 seed states, `thash` /
`thash_pair` / `thash_short` / `thash_values` for n = 16 and n > 16, the
`chain_blocks` model generic in `N`), `ChainTop`, `HashMsg` (`PRF_msg`
with the stack outer block, `H_msg`, MGF1 for both hashes), `Wots`, `Xmss`,
`Fors` (both the `N == 16` batch paths and the `N > 16` node-by-node paths),
`Ht`, `Slh`, `Api`, `Encoding`, `Sets` (the 18 per-set wrappers × 6).
The per-set files (`Sets`, `Theorems`, `ApiTheorems`, `EncodingTheorems`,
`Compat128`) are generated by the scripts in `scripts/gen/`; they are
plain Lean and are checked like the rest.

## The proofs (`hw-sha2` build)

`cd lean-hw && lake build` builds them (default target `Slhdsa`). The
statements are about the Aeneas translation of `rust/` with
`--features hw-sha2` (`lean-hw/Slhdsa/{Types,Funs}.lean`, generated by
`scripts/extract-hw.sh`), in which the eighteen wrappers of `sha256::hw::arm`
(and the vector type, its `clone`, `panic_bounds_check`) are the single-set tree's
hand-written model, `lean-hw/Slhdsa/{Types,Funs}External.lean` over
`lean-hw/Arm.lean` (until 2026-11-22 links to the single-set tree's files, now copies of
them; not changed). The
translation calls no wrapper the model lacks.

### Headline statements

`lean-hw/Slhdsa/{Theorems,ApiTheorems,EncodingTheorems,Compat128}.lean` are
symbolic links to `lean/Slhdsa/`'s: the same 187 statements, word for word
(for 128s, `Theorems.lean` lines 94–137, quoted above), now elaborated against
the `hw-sha2` translation. As in the single-set tree's `lean-hw`, no headline statement carries a
hypothesis about the processor: the hand-offs are proved for both values of
`Arm.haveSha2`. Every `#print axioms` there reports `propext`,
`Classical.choice`, `Quot.sound` (checked by `scripts/check.sh`).

### What is shared and what is new

- Linked from `lean/Slhdsa/Proofs`: every proof file that does not depend on
  the build (`Basic`, `Params`, `Sha256Core`, `Sha256`, `Sha512`, `Util`,
  `Hash`, `HashMsg`, `Wots`, `Xmss`, `Fors`, `Ht`, `Slh`, `Api`,
  `Encoding`, `Sets`), and `Slhdsa.lean`.
- From the single-set tree's `lean-hw/Slhdsa/Proofs`, unchanged (links until
  2026-11-22, now copies): `CompressTop.lean` and
  `Hw/{Model,Rounds,Compress,Wrappers}.lean` — `sha256::compress`,
  `sha256::hw::compress` and `compress_block` are the same functions in both
  translations (checked by `diff` of the generated definitions); and
  `ArmTest.lean`.
- New, `lean-hw/Slhdsa/Proofs/`:
  - `ChainTop.lean`: `chain_blocks_spec`, the default build's statement word
    for word (`N : Usize`, `N.val ≤ 32`), by cases on the hand-off
    `sha256::hw::chain_blocks::<N>`: the kernel when `N` ∈ {16, 24, 32} and
    `available()` answered yes (which gives `Arm.haveSha2 = true`), the
    portable loops otherwise.
  - `Hw/ChainModel.lean`: the chain model generic in `n` ∈ {16, 24, 32}
    (`KN`): the value as two vectors (`x`: bytes 22..38; `xb`: bytes 38..54,
    first `n − 16` bytes value, last two words zero for n = 24, `Norm`),
    `setBlk n`, one hash step `hval n` (= `stepBlock n`), the words the kernel
    rebuilds (`mkM1`, `mkM2 n`, `mkM3 n`) and the masks per `n` (`k2V`, `k3V`,
    `kbV`, `ktV`) checked bit by bit against the block, `hashV_eq` (fifteen
    kernel steps plus the cached first four rounds are one step of the chain,
    for each `n`).
  - `Hw/ChainLane.lean` (`lane_step_spec` for each `N`, including the last
    `SHA256H2` and the masked second half for N > 16), `Hw/ChainRun.lean`
    (`run_spec`: each lane makes exactly `steps` hash steps, `xb` carried),
    `Hw/ChainLoop.lean` (`enter`: masks and saved `tail` per `N`; `leave`:
    writes `xb ∨ tail` at bytes 38..54 for N > 16, which gives back the value
    and, for N = 24, the bytes 46..54 that follow it), `Hw/ChainMain.lean`,
    `Hw/ChainAll.lean` (the loop invariant), `Hw/Chain.lean`
    (`hw_chain_all_spec hw N (hN : KN N.val)`: block `i` ends as
    `runBlock N.val … start[i] end[i]`, the portable model).
  - `Hw/Guard.lean`: `compress_block_undef`, `chain_all_undef` (for every
    `N`), `compress_block_no_spec`, `chain_all_no_spec`, for
    `Arm.haveSha2 = false`.

The kernel files are the single-set tree's `lean-hw/Slhdsa/Proofs/Hw/Chain*.lean` generalised
(copied and edited, not linked): the N = 16 kernel there has no `xb`, `tail`
or `N`-dependent branch.

## Not done / caveats

- **The `hw-sha2` proofs are relative to the instruction model** of
  `lean-hw/Arm.lean` and `FunsExternal.lean` (trusted, transcribed from the
  Arm ARM, tested against one Apple M5 by `ArmTest`), as for the single-set tree's `lean-hw`.
  The model covers 17 of the 18 wrappers on in-bounds inputs only in the
  record. The n = 24, 32 kernel paths add no wrapper and no instruction.
- **Constant-time proofs and the security link**: done for both builds after
  this file's main text was written; see `lean/CT_STATUS.md`,
  `security/STATUS.md`, `security-hw/README.md`.
- **Hypotheses of the generic statements** (not of the per-set ones, which
  discharge them): `PN p N`, i.e. `(paramsS p).Valid` and `p.n = N` — the two
  sources of `n` must agree; key slices of length `4N` / `2N`; the generic
  `der_encode` needs an output of the prefix's plus the key's length,
  `der_decode` that prefix and key lengths together fit in a `usize`, and
  `secret_keys_equal` equal lengths. A caller of the generic Rust functions
  with a mismatched `N` and `p.n` is not covered.
- **`LEN_MAX` arrays**: the WOTS+ block arrays are sized for n = 32 (67 × 64
  bytes) in every set, i.e. 128s zeroes about 2 KB more stack per WOTS+ key
  than the single-set crate. It is part of the 128s overhead measured above.
- **Stack and heap searches** (the single-set tree's `compat/tests/{wipe,heap}.rs`) were run for
  128s only, before this stage's `PRF_msg` change, through a scratch shim;
  there is no RustCrypto-style adapter for the other five sets.
- **Not tested**: a CPU without the SHA-2 instructions running the `hw-sha2`
  build (as for the single-set crate), a CPU with the SHA-256 and without the SHA-512
  instructions, any non-Apple AArch64 machine.
- **The public root of `slhdsa`** no longer has `keygen`, `sign`, … for
  128s: they are `slhdsa::sha2_128s::…` (`compat/` and `bench/` use those).
- `rust/src/sha256.rs`'s hardware test checks the processor against
  `vectors/arm-wrappers.txt`; with `ARM_VECTORS_WRITE=1` it rewrites the record.

## Build

```
scripts/check.sh          # Rust tests (2 builds), both extractions + checks, proofs of both builds + placeholder and axiom checks, ArmTest, spec sigVer ×6, constant time, security, compat
scripts/check.sh full     # also the slow spec keygen/signing vectors
cd lean && lake build     # the proofs of the default build alone
cd lean-hw && lake build  # the proofs of the hw-sha2 build alone
cd lean-hw && lake build Slhdsa.Proofs.Hw.Wrappers Slhdsa.Proofs.Hw512.Wrappers && lake env lean --run ArmTest.lean ../vectors/arm-wrappers.txt
cd rust && cargo test --release [--features hw-sha2]
```

`lean-hw` uses the dependency checkouts of `lean/.lake/packages`
(`packagesDir`) and compiles `Spec` in place from the single-set tree's `lean`.

## The swap (2026-11-22)

This tree was developed in a subdirectory `multi` beside the single-set tree and replaced it on
2026-11-22 (the single-set tree is git commit `26aa3d8`):

1. Its `rust`, `lean`, `lean-hw`, `security-hw`, `compat` became the top-level `rust/`, `lean/`,
   `lean-hw/`, `security-hw/`, `compat/`; its `security` was merged into `security/` (see
   `security/STATUS.md`); its `scripts`, `vectors` into `scripts/`, `vectors/`. The files
   `lean/`, `lean-hw/` had borrowed from the single-set tree by symbolic link or in-place
   compilation (`lean/Ct/{Arith,Attr,CheckTest,CompressTop,Do,Facts,Heads,Leak,Model,Rel,Sha256,
   Sha256Core,Sim}.lean`; `lean-hw/Arm.lean`, `ArmTest.lean`, `Slhdsa/{Types,Funs}External.lean`,
   `Slhdsa/Proofs/CompressTop.lean`, `Slhdsa/Proofs/Hw/{Model,Rounds,Compress,Wrappers}.lean`,
   `Ct/CompressTop.lean`) are now real files there, unchanged.
2. `rust/`: the dev-dependency `slhdsa_ref` on the single-set crate and the test
   `cross_128s_against_original_crate` (128s byte-identical to the single-set crate in every
   function; it passed at `26aa3d8`) were removed; the record-writing mode of the wrapper test
   (`ARM_VECTORS_WRITE=1`) was ported from the single-set crate.
3. Rust API, for code written against the single-set crate: `slhdsa::keygen` etc. are
   `slhdsa::sha2_128s::keygen` (same signatures for 128s); `slhdsa::encoding::pkcs8_encode` is
   `slhdsa::sha2_128s::encoding::pkcs8_encode`; `slhdsa::params::SK_BYTES` is
   `slhdsa::sha2_128s::params::SK_BYTES`; the internal modules (`hash`, `wots`, `fors`, …) take
   `::<N>` and, where they need more than `n`, `&Params`. `bench/` was repointed; `ct-evidence/`
   (the binary timing harness) was not (see its README).
4. Lean: spec names take the parameter set (`Spec.slhSign Spec.sha2_128s`, equal to the
   single-set `Spec.slhSign` by `Spec/Compat128.lean`); the Rust names are `sets.sha2_128s.…`;
   `Room` slack constants are 152 / 409 for the n = 16 sets and 304 / 561 for the others.
