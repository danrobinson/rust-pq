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
- `SigningKey::try_sign_checked(msg, ctx, opt_rand)` signs with the guard against faults: each
  value a one-time key signs is computed twice, by routes that share no work, and an error is
  returned instead of a signature if a pair disagrees; it also refuses a private key whose
  stored public half does not belong to its seeds. The signature is the same as the plain one.

As in RustCrypto's crate, `sign` is the deterministic variant and `sign_with_rng` the hedged
one with the caller's random source.

## Features

| Feature | Default | Meaning |
|---|---|---|
| `alloc` | yes | as upstream: `to_vec`, the PKCS#8 / SPKI encoders |
| `getrandom` | yes | `generate`, `try_sign_hedged` (needs a target `getrandom` supports) |
| `zeroize` | no | accepted for upstream compatibility; keys are always wiped |
| `hw-sha2` | no | passed to `../rust`: SHA-256 on the ARMv8 SHA-256 instructions where the CPU has them |
| `hw-sha512` | no | passed to `../rust`: SHA-512 compression on the ARMv8.2 SHA-512 instructions (n = 24, 32 only). **Experimental and not covered by any proof.** |

`no_std`, always needs an allocator. Built for `aarch64-unknown-none` with
`--no-default-features` and each of: nothing, `alloc`, `alloc,zeroize`, `hw-sha2`,
`alloc,hw-sha2`, `hw-sha512`, `alloc,zeroize,hw-sha2,hw-sha512`, and the last also with
`-C target-feature=+sha2,+sha3`; also in the release profile with nothing, `hw-sha2` and
`hw-sha512`. `getrandom` does
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

  | set | keygen | sign | sign_checked | all three in a row |
  |---|---|---|---|---|
  | SHA2-128s | 11,336 | 13,864 | 13,880 | 13,976 |
  | SHA2-128f | 10,568 | 13,352 | 13,352 | 13,448 |
  | SHA2-192s | 11,592 | 15,680 | 15,728 | 15,824 |
  | SHA2-192f | 10,728 | 14,816 | 14,864 | 14,960 |
  | SHA2-256s | 11,656 | 16,848 | 16,896 | 16,992 |
  | SHA2-256f | 11,016 | 16,048 | 16,096 | 16,192 |

  (default build; the `hw-sha2` and `hw-sha2,hw-sha512` builds are listed under Tests). The
  deepest is the checked signer of SHA2-256s, about 17 KiB, so 64 KiB leaves ample room, also
  for a compiler that lays frames out less tightly.
- `tests/wipe.rs` then runs key generation, signing, checked signing, a clone and moves of the
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

Every decision this crate makes is made by a function of the verified crate, at the set's
module `slhdsa::sha2_128s` … `slhdsa::sha2_256f`:

- key generation, signing and verification (`keygen`, `sign`, `sign_deterministic`,
  `sign_checked`, `sign_deterministic_checked`, `verify`, `slh_sign_internal`,
  `slh_verify_internal`, `public_key`): the layout of a private key, the context-string
  framing, the choice of randomness for a deterministic signature;
- which byte strings are accepted as keys and signatures, and the comparison of two private
  keys (`encoding::secret_key_from`, `public_key_from`, `signature_len_ok`,
  `secret_keys_equal`);
- the PKCS#8 and SubjectPublicKeyInfo encodings (`encoding::pkcs8_encode`, `spki_encode`).

What is proved about those functions is in `../STATUS.md` (functional correctness against the
FIPS 205 transcription), `../lean/CT_STATUS.md` (constant time) and `../security` (security
link), for the portable build of `../rust` and, relative to the instruction model of
`../lean-hw`, for the `hw-sha2` build (`../lean-hw`, `../security-hw`). `hw-sha512` is
unverified.

What is left here, and is **not** covered by the proofs:

- the trait implementations and conversions between the fixed-size array types, each of which
  forwards to one of the functions above (plus upstream's argument checks kept in upstream's
  order: a context over 255 bytes is an error before a wrong-length `opt_rand` panics);
- the loop that appends the parts of a multi-part message into one buffer;
- drawing random bytes from the caller's or the operating system's random source;
- *decoding* PKCS#8 and SubjectPublicKeyInfo, which the `pkcs8` crate's traits do before this
  crate sees the key bytes (the bytes it hands over then go through the verified parser), and
  that crate's well-formedness check of the verified encoding on the way out;
- `==` on public keys and signatures (hybrid-array's comparison, as in the single-set adapter);
- the wiping.

Nothing the adapter needed was missing from `../rust`.

## Differences from RustCrypto's crate

- Only the six SHA-2 sets. The six SHAKE sets (`Shake128s` … `Shake256f`) do not exist here,
  nor do upstream's generic types `Sha2L1<N, M>` and `Sha2L35<N, M>`, of which its SHA-2 names
  are type aliases (here they are plain structs).
- `no_std` like RustCrypto's crate, but always needs an allocator. (The default `getrandom`
  feature needs a target the `getrandom` crate supports; turn it off on bare metal.)
- A `SigningKey` is always wiped; its `Debug` output leaves the secret out; comparing two
  signing keys looks at every byte.
- Multi-part messages are copied into one buffer before signing or verifying.

## Tests

```bash
cargo test
cargo test --features hw-sha2
cargo test --features hw-sha2,hw-sha512
```

- `tests/dropin.rs`: one piece of source, written against RustCrypto's interface, is compiled
  against both crates for each of the six sets. All 516 recorded results (86 per set: keys,
  signatures, encodings, accept/reject answers, error cases) must be equal; the count is
  pinned.
- `tests/extras.rs` (37 tests; 38 with `hw-sha2`, 39 with both, which add a check that the
  hardware backends are in use): per set, random keys and message lengths around every block
  boundary of `PRF_msg` and `H_msg` (SHA-256 for n = 16, SHA-512 otherwise) against
  RustCrypto; operating-system randomness; the checked signer; key comparison; `Debug`.
- `tests/wipe.rs`, `tests/heap.rs` (6 tests each): the searches described above.

All pass in the three builds: 51 tests by default (dropin 1, extras 37, heap 6, wipe 6, doc 1),
52 with `hw-sha2`, 53 with `hw-sha2,hw-sha512`. The stack depths `tests/wipe.rs` measured in
the hardware builds (identical for `hw-sha2` and `hw-sha2,hw-sha512`), bytes:

| set | keygen | sign | sign_checked | all three |
|---|---|---|---|---|
| SHA2-128s | 12,656 | 15,152 | 15,168 | 15,264 |
| SHA2-128f | 11,888 | 14,640 | 14,640 | 14,736 |
| SHA2-192s | 12,784 | 16,368 | 16,416 | 16,512 |
| SHA2-192f | 11,920 | 15,504 | 15,552 | 15,648 |
| SHA2-256s | 12,784 | 17,488 | 17,536 | 17,632 |
| SHA2-256f | 12,144 | 16,688 | 16,736 | 16,832 |

In the release profile (`cargo test --release --test wipe`) the figures are a few hundred bytes
lower (at most 16,688 portable and 17,248 with `hw-sha2`, both for 256s).

## Timing

`examples/timing.rs`: key generation, deterministic signing of a 31-byte message, and
verification, through this crate and through RustCrypto's crate from the same seeds,
alternating between the two; release build; medians of 7 runs (31 for verification), in
milliseconds. Each configuration was run twice; the two runs agree within about 5 %, so the
ratios below are stable on this machine (Apple M5 Ultra), although it was shared with Lean
builds using about 8 cores at the time (load average about 4). RustCrypto's crate goes through
`sha2` 0.11.1, which on this CPU detects and uses the ARMv8 SHA-256 *and* SHA-512 instructions
at run time in every build.

```bash
cargo run --release --example timing --features hw-sha2
cargo run --release --example timing --features hw-sha2,hw-sha512
```

Medians of the first run of each (this crate / RustCrypto; the last column is RustCrypto's time
over this crate's, so above 1 means this crate is faster):

| set | operation | `hw-sha2` | ratio | `hw-sha2,hw-sha512` | ratio |
|---|---|---|---|---|---|
| 128s | keygen | 4.21 / 8.84 | 2.10 | 4.18 / 8.79 | 2.10 |
| 128s | sign | 32.4 / 66.6 | 2.06 | 32.3 / 66.4 | 2.06 |
| 128s | verify | 0.037 / 0.066 | 1.78 | 0.038 / 0.067 | 1.77 |
| 128f | keygen | 0.082 / 0.138 | 1.69 | 0.081 / 0.137 | 1.68 |
| 128f | sign | 1.63 / 3.20 | 1.96 | 1.62 / 3.09 | 1.91 |
| 128f | verify | 0.102 / 0.187 | 1.83 | 0.099 / 0.177 | 1.80 |
| 192s | keygen | 7.29 / 13.7 | 1.88 | 6.20 / 13.1 | 2.12 |
| 192s | sign | 121 / 133 | 1.09 | 69.2 / 127 | 1.83 |
| 192s | verify | 0.118 / 0.106 | 0.89 | 0.063 / 0.106 | 1.68 |
| 192f | keygen | 0.125 / 0.198 | 1.58 | 0.124 / 0.210 | 1.69 |
| 192f | sign | 4.52 / 5.50 | 1.21 | 3.13 / 5.90 | 1.88 |
| 192f | verify | 0.241 / 0.291 | 1.21 | 0.170 / 0.307 | 1.81 |
| 256s | keygen | 4.86 / 8.57 | 1.76 | 4.19 / 8.63 | 2.06 |
| 256s | sign | 133 / 117 | 0.88 | 66.5 / 117 | 1.76 |
| 256s | verify | 0.182 / 0.170 | 0.94 | 0.103 / 0.173 | 1.67 |
| 256f | keygen | 0.332 / 0.560 | 1.69 | 0.295 / 0.565 | 1.92 |
| 256f | sign | 10.0 / 12.0 | 1.19 | 6.53 / 12.2 | 1.87 |
| 256f | verify | 0.287 / 0.314 | 1.09 | 0.186 / 0.320 | 1.72 |

With `hw-sha2` alone (not covered by the proofs, see above) this crate is about twice as fast
for the n = 16 sets. For n = 24 and 32, where `H`, `T_l`, `H_msg` and `PRF_msg` are SHA-512,
portable here but on the instructions in RustCrypto's crate, it ranges from about 10–13 %
slower (256s signing; also 192s and 256s verification) to about 1.2× faster (the f sets). With
the unverified `hw-sha512` as well it is 1.7–2.1× faster for every set and operation. The
cost of the adapter itself (an extra signature copy, the 64 KiB stack scrub) was not measured
separately.

## Credit and licence

The public interface and the PKCS#8 / SubjectPublicKeyInfo glue follow `slh-dsa` 0.2.0-rc.5
by the RustCrypto developers (copyright 2024 Trail of Bits), licensed Apache-2.0 OR MIT, by way
of the single-set tree's adapter. The licence texts are `LICENSE-APACHE-RustCrypto` and
`LICENSE-MIT-RustCrypto` in this directory.
