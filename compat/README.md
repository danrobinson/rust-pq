# slhdsa-compat: the interface to use, six SHA-2 sets

The interface of RustCrypto's [`slh-dsa`](https://github.com/RustCrypto/signatures/tree/master/slh-dsa)
crate (0.2.0-rc.5) for the six SHA-2 parameter sets SLH-DSA-SHA2-{128s, 128f, 192s, 192f,
256s, 256f}, on top of the verified crate in `../rust`. It is the single-set tree's adapter
(SLH-DSA-SHA2-128s only; git commit 26aa3d8) extended to all six SHA-2 sets.

Code written against `slh-dsa` that uses only SHA-2 sets switches by changing one line of its
`Cargo.toml`; the source stays as it is:

```toml
slh-dsa = { package = "slhdsa-compat", path = "…/formal-sig/compat" }
# with the ARMv8 SHA-256 instructions:
slh-dsa = { package = "slhdsa-compat", path = "…/formal-sig/compat", features = ["hw-sha2"] }
```

## What it provides

The same names with the same behaviour: `SigningKey<P>`, `VerifyingKey<P>`, `Signature<P>`,
`ParameterSet`, the six types `Sha2_128s`, `Sha2_128f`, `Sha2_192s`, `Sha2_192f`, `Sha2_256s`,
`Sha2_256f` (each with upstream's `NAME`, `ALGORITHM_OID`, `SkLen`, `VkLen`, `SigLen`, and
`Debug` and `Clone`), the length traits, the re-exported `signature` crate and its traits
(`Signer`, `Verifier`, `RandomizedSigner`, `Keypair`, the multi-part variants), the conversions
to and from bytes, and the PKCS#8 and SubjectPublicKeyInfo encodings.

The six types come from one macro (`src/params.rs`), which also checks at compile time that
each set's array lengths are the verified crate's (`slhdsa::sha2_*::params::{SK,PK,SIG}_BYTES`).

Additions, as in the single-set adapter:

- `SigningKey::generate()` draws the seeds from the operating system (feature `getrandom`, on
  by default).
- `SigningKey::try_sign_hedged(msg, ctx)` is FIPS 205's default signing: the per-signature
  randomness comes from the operating system (same feature).

As in RustCrypto's crate, `sign` is the deterministic variant and `sign_with_rng` the hedged
one with the caller's random source.

## Features

| Feature | Default | Meaning |
|---|---|---|
| `alloc` | yes | as upstream: `to_vec`, the PKCS#8 / SPKI encoders |
| `getrandom` | yes | `generate`, `try_sign_hedged` (needs a target `getrandom` supports) |
| `zeroize` | no | accepted for upstream compatibility; keys are always wiped |
| `hw-sha2` | no | passed to `../rust`: SHA-256 on the ARMv8 SHA-256 instructions and SHA-512 on the ARMv8.2 SHA-512 instructions, each where the CPU has them (proved relative to the instruction model of `../lean-hw`) |

`no_std`, always needs an allocator. Built for `aarch64-unknown-none` with
`--no-default-features` and each of: nothing, `alloc`, `alloc,zeroize`, `hw-sha2`,
`alloc,hw-sha2`, `alloc,zeroize,hw-sha2`, and the last also with
`-C target-feature=+sha2,+sha3`; also in the release profile with nothing and `hw-sha2`
(2026-11-22). `getrandom` does
not build there (the `getrandom` crate has no backend for it).

## Secrets are wiped

- A `SigningKey` holds its secret in an allocation of its own, overwritten when the key is
  dropped. Moving a key moves a pointer, so no copy is left where it was.
- The verified code keeps everything derived from the secret on the stack; this crate
  overwrites `SCRUB_BYTES` = 64 KiB of stack below its own frame after each key generation,
  signature and private-key parse.
- The scrub size is measured, not guessed: `tests/wipe.rs` runs each secret computation of the
  verified crate on a stack it owns, filled with a marker, and reports how deep it was written;
  it fails unless `SCRUB_BYTES` exceeds every figure by at least 8 KiB. Measured on this
  machine (Apple M5 Ultra, optimised test build, bytes):

  | set | keygen | sign | both in a row |
  |---|---|---|---|
  | SHA2-128s | 11,336 | 13,864 | 13,944 |
  | SHA2-128f | 10,568 | 13,352 | 13,432 |
  | SHA2-192s | 11,592 | 15,680 | 15,760 |
  | SHA2-192f | 10,728 | 14,816 | 14,896 |
  | SHA2-256s | 11,656 | 16,848 | 16,928 |
  | SHA2-256f | 11,016 | 16,048 | 16,128 |

  (default build; the `hw-sha2` build is listed under Tests). The deepest is the signer of
  SHA2-256s, about 17 KiB, so 64 KiB leaves ample room, also for a compiler that lays frames
  out less tightly.
- `tests/wipe.rs` then runs key generation, hedged and deterministic signing, a clone and moves of the
  key through this crate on such a stack, and searches it for 212 to 420 forms (per set) of
  the seeds and of values derived from them: `SK.seed`, `SK.prf`, HMAC's key blocks and the
  states after them, the inner HMAC digest of `PRF_msg`, the hidden FORS values next to the
  revealed ones, and the WOTS+ chain starts of the bottom layer, as bytes and as SHA-256 /
  SHA-512 words. `tests/heap.rs` has an allocator that searches every freed block for
  `SK.seed`, `SK.prf`, both key blocks and the inner `PRF_msg` digests of the messages signed.
  Both find nothing, and both find something in their controls.
- The inner `PRF_msg` digest is new in these searches (the single-set adapter's heap test
  missed it; `../rust` keeps it on the stack, the single-set crate did not). Checked against
  deliberately broken scratch copies of the backend (never `../rust` itself): with the outer HMAC hash put back through
  `sha256_from` / `sha512_from` (the old form), `tests/heap.rs` fails for all six sets, naming
  only the two inner digests; with a copy of the inner digest left below a 96 KiB frame,
  `tests/wipe.rs` fails for all six sets (first on the stack-depth check; with that check
  disabled, on the residue search, naming only the inner digest's forms).

It remains a best effort: processor registers are not cleared, the compiler may keep copies
that the source does not show, the amount of stack overwritten is sized for an optimised build
(an unoptimised one uses more), and bytes copied out with `to_bytes` are the caller's to wipe.
Note also that the interface itself is stack-hungry: a `Signature` is held inline (up to
49,856 bytes for 256f) and passed by value, as upstream does, so the wipe test's scenario
through this crate (key generation, two signatures, moves) used up to about 260 KiB of
(public) stack for 256f.

## What is and is not verified

Since 2026-11-22 every decision this crate made itself is made in the verified crate, by the
functions of `../rust/src/adapter.rs` (translated by Aeneas and proved: `../lean/Slhdsa/Proofs/Adapter.lean`,
headline list `../lean/Slhdsa/AdapterTheorems.lean`), which this crate calls at each set's
`PARAMS` and `N`:

| what | verified function | proved (for every valid parameter set) |
|---|---|---|
| joining a multi-part message | `adapter::append`, once per part | appending is list append |
| order of the argument checks: a context over 255 bytes is refused before a randomizer of the wrong length is noticed; the randomizer must be `n` bytes | `adapter::sign_into` (with `randomizer`) | `adapter_sign_into_long_ctx`, `adapter_randomizer_panic` |
| which randomness a deterministic signature uses (`PK.seed`) | `adapter::randomizer` | `adapter_randomizer_spec` (`randS`) |
| signing, hedged or deterministic, with a context, into the caller's buffer | `adapter::sign_into` | `adapter_sign_into_spec`: success exactly when the context has ≤ 255 bytes, and then Algorithm 22 |
| signing without context (KAT interface) | `adapter::sign_internal_into` | `adapter_sign_internal_into_spec`: Algorithm 19 |
| key generation from three separate seeds, their lengths | `adapter::keygen_seeds` | `adapter_keygen_seeds_spec` (Algorithm 18), `adapter_keygen_seeds_panic` |
| key generation from the `3n` random bytes | `api::keygen` | `api_keygen_spec` |
| which byte strings are private keys, and which bytes are their public key | `adapter::signing_key_from` | `adapter_signing_key_from_spec` (exactly `4n` bytes; `Spec.skPk`) |
| which byte strings are public keys / signatures | `encoding::public_key_from`, `adapter::signature_from` | `enc_public_key_from_spec`, `adapter_signature_from_spec` |
| verification, with and without context | `api::verify`, `slh::slh_verify_internal` | `api_verify_spec`, `slh_verify_internal_spec` |
| `==` on private keys | `encoding::secret_keys_equal` | `enc_secret_keys_equal_spec` |
| `==` on public keys and signatures; the algorithm-identifier test of PKCS#8 / SPKI decoding (`spki`'s `assert_algorithm_oid`, same error) | `adapter::bytes_equal` | `adapter_bytes_equal_spec` |
| the PKCS#8 and SubjectPublicKeyInfo encodings | `encoding::der_encode` with the set's prefix | `enc_der_encode_spec`, and per set `EncodingTheorems.lean` |

What is proved about the underlying functions is in `../STATUS.md` (functional correctness
against the FIPS 205 transcription), `../lean/CT_STATUS.md` (constant time) and `../security`
(security link), for the portable build of `../rust` and, relative to the instruction model of
`../lean-hw`, for the `hw-sha2` build, hardware SHA-256 and SHA-512 included (`../lean-hw`,
`../security-hw`; the adapter's functions are in both translations). The constant-time proofs
check the adapter's functions only through the checker and the erasure theorems (every
primitive they use is in the leakage model); there is no relational theorem about them.

### The exact remaining unproved surface

`src/` is 941 lines, 598 of them neither blank nor comment (`lib.rs` 121 / 27, `params.rs`
181 / 121, `signing_key.rs` 314 / 225, `verifying_key.rs` 166 / 124, `signature_encoding.rs`
125 / 94, `scrub.rs` 34 / 7). None of it is translated. Line by line it is:

- **Forwarding** (each body calls one verified function on the caller's slices, at the set's
  `PARAMS` and `N`, and copies nothing it decides): `params.rs`'s `Core` impl; the methods and
  trait impls of the three types. Trusted: that each passes the set's `PARAMS` with the
  matching `N` (the per-set `PN` facts `slhdsa.sha2_<set>.pn` hold for exactly those pairs) and
  arrays of the set's lengths (fixed by the types; `params.rs` checks at compile time that the
  lengths are the verified crate's).
- **Type and trait plumbing that cannot be translated**: the generic `ParameterSet` / length
  traits over `hybrid_array` sizes, `Signature`, `SigningKey`, `VerifyingKey`, the
  `signature` crate's traits, `Clone`, `Debug`, `From`/`TryFrom` conversions, `to_bytes`,
  `to_vec` (external traits and generic types; Aeneas translates neither the traits of other
  crates nor `typenum` sizes).
- **Three small pieces of logic, kept here and why**: the loop over the parts of a multi-part
  message in `lib.rs` (`for part in parts { append(..) }`: a `&[&[u8]]` has nested borrows,
  which Aeneas does not translate; the step it repeats is the verified `append`);
  `params.rs`'s `split` (`Option<&[u8]>` to the pair `(has, bytes)` the verified signers take:
  the erasure step of the constant-time library does not handle a `match` on `Option`); and
  in `SigningKey::try_new` and `raw_try_sign_with_rng`, which byte ranges of a buffer the
  random source fills (`[0, n)`, `[n, 2n)`, `[2n, 3n)`, and `[0, n)`), next to the RNG calls.
- **The random source** (`rand_core`'s `try_fill_bytes`, `getrandom::SysRng`): randomness is
  outside any functional statement.
- **The `pkcs8` / `spki` / `der` crates**: *decoding* a PKCS#8 or SPKI document (the
  `Decode…Key` blanket impls parse the DER before this crate is called; it then gets the
  algorithm identifier, which it compares with the verified `bytes_equal`, and the key bytes,
  which go through the verified parsers; the BIT STRING's unused-bits test is `der`'s), and
  the `der` crate's well-formedness check of the verified encodings on the way out
  (`SecretDocument::try_from`, `Document::try_from`), and `BitString::new` for signatures.
  Replacing them would change which inputs the interface accepts (`DecodePrivateKey` is a
  blanket impl over `TryFrom<PrivateKeyInfoRef>`).
- **Allocation and wiping**: the `Box` holding the private key, `Drop`/`ZeroizeOnDrop`, the
  `zeroize` calls, and `scrub.rs` (`scrub_stack` after each secret computation). Wiping is not a
  functional property and is tested, not proved (`tests/wipe.rs`, `tests/heap.rs`).

## Differences from RustCrypto's crate

- Only the six SHA-2 sets. The six SHAKE sets (`Shake128s` … `Shake256f`) do not exist here,
  nor do upstream's generic types `Sha2L1<N, M>` and `Sha2L35<N, M>`, of which its SHA-2 names
  are type aliases (here they are plain structs).
- `no_std` like RustCrypto's crate, but always needs an allocator. (The default `getrandom`
  feature needs a target the `getrandom` crate supports; turn it off on bare metal.)
- A `SigningKey` is always wiped; its `Debug` output leaves the secret out; comparing two
  signing keys looks at every byte.
- Multi-part messages are copied into one buffer before signing or verifying (since 2026-11-22
  also a one-part message).

## Tests

```bash
cargo test
cargo test --features hw-sha2
```

- `tests/dropin.rs`: one piece of source, written against RustCrypto's interface, is compiled
  against both crates for each of the six sets. All 516 recorded results (86 per set: keys,
  signatures, encodings, accept/reject answers, error cases) must be equal; the count is
  pinned.
- `tests/extras.rs` (37 tests; 39 with `hw-sha2`, which adds checks that the two hardware
  backends are in use): per set, random keys and message lengths around every block
  boundary of `PRF_msg` and `H_msg` (SHA-256 for n = 16, SHA-512 otherwise) against
  RustCrypto; operating-system randomness; a key whose public half does not match its seeds;
  key comparison; `Debug`.
- `tests/wipe.rs`, `tests/heap.rs` (6 tests each): the searches described above.

All pass in both builds: 51 tests by default (dropin 1, extras 37, heap 6, wipe 6, doc 1),
53 with `hw-sha2`. The stack depths `tests/wipe.rs` measured in
the `hw-sha2` build, bytes:

| set | keygen | sign | both |
|---|---|---|---|
| SHA2-128s | 12,656 | 15,152 | 15,232 |
| SHA2-128f | 11,888 | 14,640 | 14,720 |
| SHA2-192s | 12,784 | 16,368 | 16,448 |
| SHA2-192f | 11,920 | 15,504 | 15,584 |
| SHA2-256s | 12,784 | 17,488 | 17,568 |
| SHA2-256f | 12,144 | 16,688 | 16,768 |

In the release profile (`cargo test --release --test wipe`) the figures differ by a few hundred
bytes (at most 16,608 portable and 17,168 with `hw-sha2`, both for 256s).

## Timing

`examples/timing.rs`: key generation, deterministic signing of a 31-byte message, and
verification, through this crate and through RustCrypto's crate from the same seeds,
alternating between the two; release build; medians of 7 runs (31 for verification), in
milliseconds. Run twice on 2026-11-22 (Apple M5 Ultra, load average 1.8–2.7); the two runs agree
within 1.5 %. RustCrypto's crate goes through `sha2` 0.11.1, which on this CPU detects and uses
the ARMv8 SHA-256 *and* SHA-512 instructions at run time.

```bash
cargo run --release --example timing --features hw-sha2
```

Medians of the first run (this crate / RustCrypto; the last column is RustCrypto's time over
this crate's, so above 1 means this crate is faster):

| set | operation | `hw-sha2` | ratio |
|---|---|---|---|
| 128s | keygen | 3.95 / 8.29 | 2.10 |
| 128s | sign | 30.4 / 62.6 | 2.06 |
| 128s | verify | 0.034 / 0.057 | 1.68 |
| 128f | keygen | 0.075 / 0.129 | 1.71 |
| 128f | sign | 1.53 / 2.99 | 1.96 |
| 128f | verify | 0.095 / 0.171 | 1.79 |
| 192s | keygen | 6.13 / 12.5 | 2.04 |
| 192s | sign | 67.7 / 124.8 | 1.84 |
| 192s | verify | 0.066 / 0.111 | 1.67 |
| 192f | keygen | 0.109 / 0.193 | 1.77 |
| 192f | sign | 2.92 / 5.40 | 1.85 |
| 192f | verify | 0.163 / 0.292 | 1.80 |
| 256s | keygen | 4.11 / 8.40 | 2.04 |
| 256s | sign | 65.1 / 115.6 | 1.78 |
| 256s | verify | 0.092 / 0.156 | 1.68 |
| 256f | keygen | 0.269 / 0.535 | 1.99 |
| 256f | sign | 6.05 / 11.19 | 1.85 |
| 256f | verify | 0.168 / 0.291 | 1.73 |

With `hw-sha2` (SHA-256 and, for n = 24 and 32, SHA-512 on the instructions, both proved
relative to the instruction model) this crate is 1.7–2.1× faster than RustCrypto's for every
set and operation. Before 2026-11-22 the SHA-512 backend was a separate, unproved feature; the
verified one signs 192s in 67.7 ms and 256s in 65.1 ms, as that one did (69.2 and 66.5 ms in the
measurement of that time). The cost of the adapter itself (an extra signature copy, the 64 KiB
stack scrub) was not measured separately.

## Credit and licence

The public interface and the PKCS#8 / SubjectPublicKeyInfo glue follow `slh-dsa` 0.2.0-rc.5
by the RustCrypto developers (copyright 2024 Trail of Bits), licensed Apache-2.0 OR MIT, by way
of the single-set tree's adapter. The licence texts are `LICENSE-APACHE-RustCrypto` and
`LICENSE-MIT-RustCrypto` in this directory.
