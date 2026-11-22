# slhdsa-compat: the interface to use

The interface of RustCrypto's [`slh-dsa`](https://github.com/RustCrypto/signatures/tree/master/slh-dsa)
crate (0.2.0-rc.5) for SLH-DSA-SHA2-128s, on top of the verified crate in `../rust`. This is
the crate a program should depend on; `../rust` is the verified core beneath it.

Code written against `slh-dsa` that uses only `Sha2_128s` switches by changing one line of
its `Cargo.toml`; the source stays as it is:

```toml
slh-dsa = { package = "slhdsa-compat", path = "…/formal-sig/compat" }
# with the ARMv8 SHA-256 instructions:
slh-dsa = { package = "slhdsa-compat", path = "…/formal-sig/compat", features = ["hw-sha2"] }
```

## What it provides

The same names with the same behaviour: `SigningKey<P>`, `VerifyingKey<P>`, `Signature<P>`,
`ParameterSet`, `Sha2_128s`, the length traits, the re-exported `signature` crate and its
traits (`Signer`, `Verifier`, `RandomizedSigner`, `Keypair`, the multi-part variants), the
conversions to and from bytes, and the PKCS#8 and SubjectPublicKeyInfo encodings.

Additions:

- `SigningKey::generate()` draws the seeds from the operating system (feature `getrandom`,
  on by default).
- `SigningKey::try_sign_hedged(msg, ctx)` is FIPS 205's default signing: the per-signature
  randomness comes from the operating system (same feature).
- `SigningKey::try_sign_checked(msg, ctx, opt_rand)` signs with the guard against faults
  described next.

As in RustCrypto's crate, `sign` is the deterministic variant and `sign_with_rng` the hedged
one with the caller's random source.

## Optional guard against faults

The signing methods do the work of the standard and no more, exactly as RustCrypto's do.

A fault while one tree of the signature is being computed gives a wrong root that the next
layer then signs correctly. The signature still verifies, and it shows a one-time key
signing a second value, which is what a forger needs; this is the published fault attack on
this family of schemes, and neither RustCrypto's crate nor OpenSSL guards against it.
`try_sign_checked` does: it computes each such value twice, by routes that share no work,
and returns an error instead of a signature if a pair disagrees. The signature is the same
as the plain one. It takes a little under twice as long (measured 1.87×), and it also
refuses a private key whose stored public half does not belong to its seeds.

## Secrets are wiped

- A `SigningKey` holds its secret in an allocation of its own, overwritten when the key is
  dropped. Moving a key moves a pointer, so no copy is left where it was.
- The verified code keeps everything derived from the secret on the stack; this crate
  overwrites that part of the stack after each key generation and signature.
- `tests/wipe.rs` runs key generation and signing on a stack it owns and then searches it
  for 208 forms of the seeds and of values derived from them; `tests/heap.rs` does the same
  for every freed heap block. Both find nothing, and both find something in their controls.

It remains a best effort: processor registers are not cleared, the compiler may keep copies
that the source does not show, the amount of stack overwritten is sized for an optimised
build, and bytes copied out with `to_bytes` are the caller's to wipe.

## What is and is not verified

Every decision this crate makes is made by a function of the verified crate:

- key generation, signing and verification (`slhdsa::keygen`, `sign`, `sign_deterministic`,
  `sign_checked`, `verify`): the layout of a private key, the context-string framing, the
  choice of randomness for a deterministic signature;
- which byte strings are accepted as keys and signatures, and the comparison of two private
  keys (`slhdsa::encoding`);
- the PKCS#8 and SubjectPublicKeyInfo encodings (`slhdsa::encoding::pkcs8_encode`,
  `spki_encode`): for this parameter set each is a fixed prefix followed by the key, and
  decoding an encoding is proved to give the key back.

What is left here, and is **not** covered by the proofs:

- the trait implementations and conversions between the fixed-size array types, each of
  which forwards to one of the functions above;
- the loop that appends the parts of a multi-part message into one buffer (the proof tools
  cannot express a slice of slices);
- drawing random bytes from the caller's or the operating system's random source;
- *decoding* PKCS#8 and SubjectPublicKeyInfo, which the `pkcs8` crate's traits do before this
  crate sees the key bytes (the bytes it hands over then go through the verified parser);
  and that crate's check of the verified encoding on the way out;
- the wiping.

## Differences from RustCrypto's crate

- Only `Sha2_128s`. The other eleven parameter sets do not exist here.
- `no_std` like RustCrypto's crate, but always needs an allocator. (The default `getrandom`
  feature needs a target the `getrandom` crate supports; turn it off on bare metal.)
- A `SigningKey` is always wiped; its `Debug` output leaves the secret out; comparing two
  signing keys looks at every byte.

## Tests

```bash
cargo test
```

```bash
cargo test --features hw-sha2
```

- `tests/dropin.rs`: one piece of source, written against RustCrypto's interface, is
  compiled against both crates. All 86 recorded results (keys, signatures, encodings,
  accept/reject answers, error cases) must be equal.
- `tests/extras.rs`: random keys and message lengths around every block boundary against
  RustCrypto; operating-system randomness; the checked signer; `Debug`.
- `tests/wipe.rs`, `tests/heap.rs`: the searches described above.

## Credit

The public interface and the PKCS#8 / SubjectPublicKeyInfo glue follow `slh-dsa`
0.2.0-rc.5 by the RustCrypto developers (copyright 2024 Trail of Bits), licensed
Apache-2.0 OR MIT. The licence texts are `LICENSE-APACHE-RustCrypto` and
`LICENSE-MIT-RustCrypto` in this directory.
