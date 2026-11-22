# multi/ — SLH-DSA-SHA2, all six parameter sets: status

Copy of `rust/` and `lean/` extended from SLH-DSA-SHA2-128s to
SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}. Nothing outside `multi/` was
modified. `multi/scripts/check.sh` re-runs every check that holds at this
stage (below).

## State (2026-11-22): optimised Rust for six sets; the proofs are stale

This stage made `multi/rust` the optimised implementation of `../rust` for all
six SHA-2 parameter sets. It is Rust only.

| Item | State |
|---|---|
| Same modules and public functions as `../rust/src` (`api`, `encoding`, checked signer, `no_std` + alloc, `hw-sha2` with the same runtime detection), six sets | done (generic functions, plus per-set typed wrappers with `../rust`'s signatures) |
| `chain_blocks`, seed-state precomputation, `sha256_from`, in-place `H_msg`, stack HMAC key blocks, FORS batches and joint climbing, on the SHA-256 paths of every set | done |
| SHA-512 for `H`, `T_l`, `H_msg`, `PRF_msg` (n = 24, 32): seed state after `PK.seed ‖ 0^(128−n)`, one-block `H`, `T_len` on the stack, `sha512_from` | done, portable |
| `hw-sha2` chain kernel for n = 24 and 32 | done (one kernel, generic in `N`; the wrappers are unchanged) |
| Hardware SHA-512 (FEAT_SHA512) | done as a separate, experimental, **unverified** feature `hw-sha512` (last section) |
| Tests, both builds | all pass (counts below) |
| Charon/Aeneas, default build | no opaque function, no axiom, no `External` file; the translation typechecks |
| Charon/Aeneas, `hw-sha2` build | only `sha256::hw::arm` left out (21 declarations, all defined by `../lean-hw`'s model, linked); the translation typechecks |
| 128s speed against `../rust` | within 2.5% everywhere (table below) |
| Refinement proofs (`lean/Slhdsa/Proofs`, `Theorems.lean`) | **stale**: they are about the previous Rust code. Against the new translation `Basic.lean` and `Params.lean` still build; `Sha256.lean` (12 errors) and `Util.lean` (1 error) fail, so nothing above them is reached. Per-file assessment below. |
| Constant-time proofs, hardware proofs, security link | not started for this tree |

The previous stage (generic but unoptimised Rust, with complete refinement
proofs: 37 headline theorems on the three standard axioms) is in git history
before this change.

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
   `&mut blocks[0..len]` — the pattern `../rust`'s FORS batch already uses.
2. *Proofs.* With `[u8; N]` the Lean types are `Array U8 N`, so hash values
   keep their length in the type, as the optimised proofs of `../lean` have
   it with `16#usize`; the generalisation of those proofs replaces the
   literal 16 by `N` (with `N ∈ {16, 24, 32}`) rather than switching to
   slices with length side conditions. The multi proofs' treatment of
   `Params`, `Valid` and SHA-512 carries over, since `Params` is unchanged. A
   runtime `n` with `[u8; 32]` buffers would have put "the first `n` bytes"
   into every statement; per-set instantiation of shared source would have
   given six copies of every definition to prove. One kernel, generic in `N`,
   is translated once (Aeneas keeps const generics as parameters).
3. *Speed.* Monomorphisation gives each set code specialised to its `n`;
   `if N == 16` branches fold away. For 128s the generated code is the same
   algorithm as `../rust`'s, and measures within 2.5%.

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
  are unchanged, so the trusted model of `../lean-hw` still describes them;
  the kernel's proofs are not done.
- **Keys** are slices in the generic functions (`sk: &[u8]` of 4n bytes;
  key generation writes into `sk: &mut [u8]`, `pk: &mut [u8]`), so nothing
  secret is returned by value from the generic code; the per-set modules give
  `../rust`'s array signatures.
- **Per-set modules** `sha2_128s` … `sha2_256f` (generated by one macro in
  `sets.rs`) hold `params` (`N`, `PK_BYTES`, `SK_BYTES`, `SEED_BYTES`,
  `SIG_BYTES`, `PKCS8_BYTES`, `SPKI_BYTES`, `PARAMS`), the internal and pure
  functions and the checked signer (`slh_keygen_internal`, `slh_sign_internal`,
  `slh_sign_internal_checked`, `slh_verify_internal`, `slh_sign`,
  `slh_sign_checked`, `slh_verify`), the interface functions (`keygen`,
  `public_key`, `sign`, `sign_deterministic`, `sign_checked`,
  `sign_deterministic_checked`, `verify`) and the encodings
  (`PKCS8_PREFIX`, `SPKI_PREFIX`, `secret_key_from`, `public_key_from`,
  `signature_len_ok`, `secret_keys_equal`, `pkcs8_encode`/`decode`,
  `spki_encode`/`decode`), with re-export modules `api` and `encoding` so the
  paths are `../rust`'s (`slhdsa::sha2_128s::api::keygen`, …). The functions
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
- `#[inline(never)]` as in `../rust` on the functions that handle the seed
  (generic `slh_keygen_internal`, `slh_sign_internal`,
  `slh_sign_internal_checked`, `api::keygen`, and the per-set wrappers of
  the same names).

## Files changed

`rust/`: `Cargo.toml` (features `hw-sha2`, `hw-sha512`; dev-dependencies
`slh-dsa =0.2.0-rc.5`, `signature`, `pkcs8`, `sha2` with `compress`);
`src/` all files rewritten (`address.rs` and the portable part of
`sha256.rs` are copies of `../rust`'s), new `api.rs`, `encoding.rs`;
`tests/acvp.rs` rewritten, new `tests/api.rs`, `tests/compress.rs`,
`tests/rustcrypto.rs`. `lean/Slhdsa/{Types,Funs}.lean` regenerated. New
`lean-hw/` (lakefile, manifest, generated `Slhdsa/{Types,Funs}.lean`, links to
`../../lean-hw/Slhdsa/{Types,Funs}External.lean`). `scripts/check.sh`
rewritten, new `scripts/extract-hw.sh`.

## Tests

All pass, run on this machine (Apple M5 Ultra) in four builds: default,
`--features hw-sha2`, `--features hw-sha2,hw-sha512`, `--features hw-sha512`;
and `hw-sha2,hw-sha512` again with `RUSTFLAGS="-C target-feature=-sha2,-sha3"`
(the runtime-detection path Linux takes).

| file | tests | what |
|---|---|---|
| `acvp.rs` | 30 | per set (×6): ACVP keyGen 10/10 (also through `keygen`, `public_key`), sigGen 28/28 (each also through the checked signer and the `api` functions), sigVer 28/28, round trip and tampering; Table 2 sizes and `N = PARAMS.n`; SHA-256, SHA-512 (also `sha512_from`), HMAC-SHA-256/512 against `sha2`/`hmac`; `PRF_msg` and `H_msg` of all six sets against HMAC and MGF1 written with `sha2`/`hmac`, message lengths 0..140 and others; 128s byte-identical to `../rust` (keygen, both `api::keygen`, `public_key`, `slh_sign_internal(_checked)`, `slh_sign(_checked)`, all four `api` signers, damaged-key refusal, verdicts on 10 signature variants through three verifiers, both prefixes, PKCS#8/SPKI encode and decode, byte conversions, `secret_keys_equal`) |
| `api.rs` | 31 | `../rust/tests/api.rs` ported, 5 tests ×6 sets: `keygen` is the internal function on the three seeds; the checked signers return the plain signature on honest keys; contexts over 255 bytes refused; a damaged key (bytes in SK.seed, PK.seed, PK.root) gives no checked signature while a changed SK.prf still does; a wrong value from either route is caught by `ht_sign_checked`. Plus the cost of the check (128s, printed) |
| `compress.rs` | 10 (11 with `hw-sha2`, 12 with both) | `../rust/tests/compress.rs` ported: `compress` on 200,000 random and 2,565 edge cases; `chain_blocks::<N>` for N = 16, 24, 32 against a reference on random blocks with uniform, mixed, single-step, empty, reversed and carry-crossing ranges, batch sizes 0..41, 64, 70, 128, 140, equal and unequal block heads; chain independence; panics; SHA-512 `compress` on 50,000 random cases; the backends are active where the CPU has them |
| (unit) | 0 (1 with `hw-sha2`) | `sha256::hw::vectors`: the wrappers against the main tree's record `../vectors/arm-wrappers.txt` |
| `rustcrypto.rs` | 18 | per set (×6) against `slh-dsa` 0.2.0-rc.5: same keys from the same seeds; byte-identical signatures (internal hedged and deterministic, pure with context hedged and deterministic, through `api` and the checked signers); each verifies the other's; both reject the same tampering; PKCS#8 and SPKI bytes identical, each decodes the other's; OID equals `const_oid::db::fips205`'s; encoder/decoder/conversion edge cases |

Also run, outside the repository: `../compat`'s whole test suite (including
the 86-result drop-in comparison with RustCrypto, `wipe.rs` and `heap.rs`)
against this crate's 128s, through a scratch shim crate that exposes
`sha2_128s` under `../rust`'s paths: all pass, default and `hw-sha2`. The
unscrubbed stack depth of keygen plus checked signing was 14,024 bytes
(`../rust`: 14,136); the adapter run left 0 of 208 searched secret forms.
And `cargo build --target aarch64-unknown-none` for the library: default,
`hw-sha2`, `hw-sha2` with `+sha2`, `hw-sha2,hw-sha512`.

## Translation (Charon + Aeneas)

- `scripts/extract.sh` (default build) → `lean/Slhdsa/{Types,Funs}.lean`
  (54 + 6,831 lines): 0 `axiom`, 0 `opaque`, no `External` template, no
  `sorry`. `lake build Slhdsa.Funs` succeeds (3,614 jobs).
- `scripts/extract-hw.sh` (`--features hw-sha2`, `--opaque
  'slhdsa::sha256::hw::arm'`) → `lean-hw/Slhdsa/{Types,Funs}.lean`: 0 `axiom`
  or `opaque` in the generated files; Aeneas left out 21 declarations (the
  vector type, its `clone`, `panic_bounds_check`, and the eighteen wrappers),
  every one defined in `../lean-hw/Slhdsa/{Types,Funs}External.lean`, which
  `multi/lean-hw` links to. `lake build` there succeeds (3,621 jobs).
- The `hw-sha512` build was not translated (see the last section).

## Measurements

Apple M5 Ultra, release builds, scratch harness (not in the repository)
calling the per-set `api` functions and RustCrypto's `slh-dsa` 0.2.0-rc.5 on
a 32-byte message with an empty context: keygen and sign are medians of 5
single calls, verify of 5 batches of 20, each run 3 times in alternating
order of the three builds; the tables give the median of the 3 runs. Load
average 1.4–1.8 during the runs (another agent's Lean builds); the spread of
signing time between runs was at most 2.7% (portable) and 1.3% (hardware).

**128s against `../rust`** (same harness, the two crates interleaved, 7 rounds
each run; median over runs of the per-run difference, range in brackets):

| build | keygen | sign | verify |
|---|---|---|---|
| portable | +2.2% (+1.1 … +2.5) | +1.0% (+0.9 … +1.2) | −0.3% (−0.6 … +1.3) |
| `hw-sha2` | +0.8% (+0.5 … +1.0) | +0.6% (+0.5 … +0.8) | +1.0% (+0.4 … +1.1) |

Absolute, `hw-sha2`: keygen 3.93 ms, sign 30.29 ms, verify 34.9 µs
(`../rust` in the same runs: 3.90 ms, 30.11 ms, 34.5–34.8 µs; the reference
numbers 3.91 ms / 30.20 ms / 35.35 µs). Portable: 40.2–40.7 ms, 309–310 ms,
309–311 µs (`../rust`: 39.7 ms, 306–308 ms, 307–312 µs). Where the portable
keygen excess comes from is not isolated: the N = 16 instance of
`chain_blocks_portable` is the same instruction sequence as `../rust`'s up
to register allocation (310 against 306 lines of disassembly, `compress`
inlined in both, no extra calls), and the extra work of the `LEN_MAX` arrays
(about 2 KB more zeroing per WOTS+ key, against ≈ 78 µs per key) is two
orders of magnitude too small to explain 2%. Code placement is the likely
cause; that is a guess.

**All six sets.** "RC" is RustCrypto in the same binary. In the portable
build RustCrypto was compiled with `--cfg sha2_backend="soft"` (portable
SHA-2, as `../bench` does); in the two hardware builds it uses `sha2` 0.11's
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

`--features hw-sha2` (SHA-512 portable):

| set | keygen | sign | verify | RC keygen | RC sign | RC verify |
|---|---|---|---|---|---|---|
| 128s | 3.93 ms | 30.29 ms | 36.4 µs | 8.30 ms | 62.55 ms | 64.5 µs |
| 128f | 61.0 µs | 1.51 ms | 99.3 µs | 128.7 µs | 2.99 ms | 180.5 µs |
| 192s | 6.88 ms | 115.5 ms | 119.2 µs | 12.53 ms | 124.6 ms | 109.0 µs |
| 192f | 105.5 µs | 4.41 ms | 241.1 µs | 192.4 µs | 5.41 ms | 288.0 µs |
| 256s | 4.74 ms | 126.6 ms | 170.2 µs | 8.32 ms | 114.5 ms | 156.5 µs |
| 256f | 291.7 µs | 9.40 ms | 271.7 µs | 513.5 µs | 11.15 ms | 299.6 µs |

`--features hw-sha2,hw-sha512` (experimental, unverified SHA-512 backend):

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
portable build in every set, the same ratio as `../rust` (its portable
SHA-256 compression is slower per block than the `sha2` crate's). With
`hw-sha2` it is faster than RustCrypto in every operation of the 128 and f
sets and in 192s keygen and signing, and slower in 192s verification and all
of 256s except keygen — because SHA-512 is still portable there.

**How much SHA-512 takes in the 192/256 sets** (`hw-sha2` build). Counted
with an instrumented scratch copy: SHA-512 compressions per keygen / sign /
verify are 5,632 / 317,940 / 379 (192s), 88 / 10,344 / 561 (192f), 4,864 /
399,344 / 526 (256s), 304 / 23,054 / 703 (256f) — nearly all of signing's
are the `H` of the FORS trees (one block per node) and the `T_len` of the
WOTS+ keys. A portable compression costs 179.6 ns (median of 7 runs of 10^6
calls). So SHA-512 is about 15–19% of key generation, 42–57% of signing and
42–57% of verification in these sets:

| set | keygen | sign | verify | measured saving with `hw-sha512` (keygen / sign / verify) |
|---|---|---|---|---|
| 192s | 15% | 49% | 57% | 11% / 41% / 45% |
| 192f | 15% | 42% | 42% | 10% / 33% / 33% |
| 256s | 18% | 57% | 56% | 13% / 48% / 44% |
| 256f | 19% | 44% | 47% | 13% / 36% / 37% |

(Share = count × 179.6 ns / measured time; the measured saving is what the
experimental backend actually removed, at about 30 ns per compression.) More
would need what the SHA-256 path has, several independent hashes
interleaved in the unit (the `H` of one FORS level, and the climbs of the k
trees, are independent); that was not tried.

## Hardware SHA-512 (`hw-sha512`): what it is

`multi/rust/src/sha512.rs`, module `hw`: nine wrappers around the FEAT_SHA512
intrinsics (`vsha512hq_u64`, `vsha512h2q_u64`, `vsha512su0q_u64`,
`vsha512su1q_u64`, loads, stores, add, extract) and a forty-step
`compress_block`, entered by `sha512::compress` after a run-time test
(`std::arch::is_aarch64_feature_detected!("sha3")`, or the build's target
features where the target guarantees them or has no operating system), with
the portable `compress_portable` as the fallback. One block at a time, no
multi-lane kernel. It is a separate feature so that the `hw-sha2` build, its
translation and its 21-declaration model are unchanged. Tested like the rest
(`compress` on 50,000 random blocks against `sha2::compress512`, and every
test file in the builds `hw-sha512` and `hw-sha2,hw-sha512`, including the
run-time detection path). Not translated, no model of the instructions, no
proof.

## Secrets and constant time

No branch, index or length depends on a secret beyond those of `../rust`. The
new branches are on `N` (a const generic), on parameters (`p.k`, `p.a`,
`p.d`, `p.hp`), on message, context and buffer lengths, on public digest
digits and tree indices, and in the hardware kernel on `N` and the slot
schedule (step ranges, which are public). The kernel's cache of the first
rounds is keyed on the first 16 block bytes, an address prefix, as before.
`der_decode` returns early on a prefix mismatch, like `../rust`'s
`pkcs8_decode` (the prefix is not secret). Root comparisons in the checked
signer use array `==` as in `../rust`. Secret values are on the stack in the
same places as in `../rust`; the SHA-512 key blocks of `PRF_msg` are on the
stack too. Nothing of this has been checked by the constant-time machinery of
`../lean/Ct` (it has not been run on this tree); the compat stack and heap
searches above were run for 128s only.

Observation about `../rust` (unchanged here, and carried into the SHA-512
path): `sha256_from` / `sha512_from` copy the tail of their message into a
heap `Vec` for padding, so the HMAC inner digest `H((K ⊕ ipad) ‖ opt_rand ‖ M)`,
which depends on `SK.prf`, reaches the heap in `PRF_msg`. It is not among the
forms `../compat/tests/heap.rs` searches for. Whether it matters is a
judgement call (it is a PRF output, not the key), but the documentation's
"nothing derived from the secret seed is written to the heap" is not
literally true of it.

## The proofs: what carries over

The translation changed shape, so every proof that unfolds a Rust function
needs at least re-checking. Expected per file (sources: `../lean/Slhdsa/Proofs`
= optimised 128s proofs, `lean/Slhdsa/Proofs` here = generic old-code proofs):

| file (this tree) | expectation |
|---|---|
| `Basic.lean` | carries over (`bytes`, `Room`, `paramsS`; `Params` is unchanged) |
| `Params.lean` | carries over; add `len ≤ LEN_MAX`, `k ≤ K_MAX` and `N = p.n` facts |
| `Sha256.lean` | replace by `../lean`'s `Sha256Core.lean`, `CompressTop.lean`, `Sha256.lean`: the portable Rust is a copy of `../rust/src/sha256.rs`, so these should carry over with little more than name changes |
| `Sha512.lean` | needs adapting: `compress` is now public and dispatches to `compress_portable` (body unchanged), `pad` takes `pre`, new `digest`, `sha512_from`; follow `../lean`'s `sha256_from` proofs |
| `Util.lean` | `to_int`, `base_2b`, `bytes_eq` carry over; `block` is now `[u8; N]` (as `../lean`'s `block_spec` with 16 → N) |
| `Hash.lean` | needs writing new: `../lean`'s `Hash.lean` (1,009 lines, 16-specific: `seed_ctx`, `short_block`, `trunc`, `stepBlock`/`runBlock`, `chain_blocks_spec`, `pair_block`, `thash_values`, `thash_short`, `prf_msg`, `h_msg_inner`, `h_msg`) generalised to N, plus the SHA-512 halves (`state512`, `thash_pair`, `thash` and `thash_values` for N > 16, HMAC-SHA-512 `prf_msg`, `h_msg_inner512`, MGF1-SHA-512 from this tree's old `Hash.lean`) |
| `Wots.lean` | needs adapting: `../lean`'s `Wots.lean` with N and with the `LEN_MAX` arrays used through `blocks[0..len]` |
| `Xmss.lean` | needs adapting, mostly mechanical: `../lean`'s with `p.hp` and N |
| `Fors.lean` | needs adapting: `../lean`'s `fors_batch`/`fors_pk_from_sig` proofs for the `N == 16` branches (now inside `if`s, arrays `K_MAX`), plus new, simpler proofs of the `N > 16` level loops (node-by-node `thash_pair`) |
| `Ht.lean` | needs adapting: this tree's generic `ht_sign`/`ht_verify` structure, with `../lean`'s array-typed statements |
| `Slh.lean` | needs adapting: keys are slices, key generation writes into `&mut` slices |
| `Sets.lean` | needs adapting and extending: the per-set wrappers now include the interface functions and encodings (22 functions × 6 sets) |
| `Theorems.lean` | the 5 × 6 statements keep their shape; add the interface, checked-signer and encoding statements |
| (missing) `Checked.lean`, `Api.lean`, `Encoding.lean`, `ApiTheorems.lean`, `EncodingTheorems.lean` | port from `../lean`, generically: `fors_pk_gen`, `ht_sign_checked` and the `api` wrappers follow the same pattern; `secret_keys_equal` and `der_decode` loops become generic over the length |
| `../lean-hw/Slhdsa/Proofs/Hw/*` for this tree | `Model`, `Rounds`, `Compress`, `Wrappers`, `Guard` should carry over (`compress_block` and the wrappers are unchanged); `ChainModel`, `ChainLane`, `ChainRun`, `ChainLoop`, `ChainMain`, `ChainAll`, `Chain` need adapting to the generic kernel (second value vector, masks per N, the last `SHA256H2` for N > 16, the saved `tail` for N = 24) |
| `../lean/Ct` for this tree | the instrumented copy must be regenerated from the new translation; the new branches are on the const generic `N` and parameters, which the checker should treat as public |
| `lean/Spec` | unaffected (it does not depend on the Rust); `spectest` still passes |

## Not done / caveats

- **No proofs for the new code.** The refinement proofs here are stale; the
  constant-time proofs, the hardware kernel proofs and the security link have
  not been started for this tree.
- **`hw-sha512` is experimental and unverified**: no translation, no model of
  the SHA-512 instructions, no proof; it is a separate feature so that the
  `hw-sha2` build and its translation are unaffected.
- **Two sources of `n`**: functions take `N` and `p.n` and require them to be
  equal. The per-set modules pass them consistently (checked by a test); a
  caller of the generic functions with a mismatched pair gets wrong results
  or a panic. A proof will carry `p.n = N` as a hypothesis.
- **`LEN_MAX` arrays**: the WOTS+ block arrays are sized for n = 32 (67 × 64
  bytes) in every set, i.e. 128s zeroes about 2 KB more stack per WOTS+ key
  than `../rust`. It is part of the 128s overhead measured above.
- **Stack and heap searches** (`../compat/tests/{wipe,heap}.rs`) were run for
  128s only, through a scratch shim; there is no RustCrypto-style adapter for
  the other five sets, so they were not searched. Stack use grows with `n`
  (the SHA-512 `T_len` buffer is 2,304 bytes) and was not measured for them.
- **Not tested**: a CPU without the SHA-2 instructions running the `hw-sha2`
  build (as for `../rust`), a CPU without FEAT_SHA512 running `hw-sha512`,
  any non-Apple AArch64 machine. The lane count and staggering of the
  kernel were not re-tuned for n = 24, 32.
- **The public root of `slhdsa`** no longer has `keygen`, `sign`, … for
  128s: they are `slhdsa::sha2_128s::…`. `../compat` and `../bench` would
  need their paths changed (or a shim like the one used above) to use this
  crate.
- `multi/rust/src/sha256.rs`'s hardware test reads `../../vectors/arm-wrappers.txt`
  (the main tree's record); with `ARM_VECTORS_WRITE=1` it would rewrite that
  file.

## Build

```
multi/scripts/check.sh          # Rust tests (3 builds), both extractions + checks, translations typecheck, spec sigVer ×6
multi/scripts/check.sh full     # also the slow spec keygen/signing vectors
multi/scripts/check.sh proofs   # also tries the stale proofs (expected to fail)
cd multi/rust && cargo test --release [--features hw-sha2[,hw-sha512]]
```

`multi/lean/.lake/packages` is an APFS clone of `lean/.lake/packages`;
`multi/lean-hw` uses those packages (`packagesDir`) and compiles `Arm.lean`
in place from `../../lean-hw`.

## Swapping multi/ in for rust/ (when the proofs exist)

1. Copy `multi/rust` → `rust`; drop the dev-dependency `slhdsa_ref` and the
   test `cross_128s_against_original_crate`.
2. Rust API: `slhdsa::keygen` etc. become `slhdsa::sha2_128s::keygen` (same
   signatures for 128s); `slhdsa::encoding::pkcs8_encode` becomes
   `slhdsa::sha2_128s::encoding::pkcs8_encode`; `slhdsa::params::SK_BYTES`
   becomes `slhdsa::sha2_128s::params::SK_BYTES`; the internal modules
   (`hash`, `wots`, `fors`, …) take `::<N>` and, where they need more than
   `n`, `&Params`. `../compat`, `../bench` and `../rust/ct-evidence` need
   those path changes.
3. The Lean side as in the previous version of this file (spec names take
   the parameter set; `Room` slack constants 304 / 561), once the proofs are
   redone.
