# slhdsa-compat

The interface of RustCrypto's [`slh-dsa`](https://github.com/RustCrypto/signatures/tree/master/slh-dsa)
crate (0.2.0-rc.5) for SLH-DSA-SHA2-128s, backed by the verified crate in `../rust`.

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

Two additions, behind the default `getrandom` feature:

- `SigningKey::generate()` draws the seeds from the operating system.
- `SigningKey::try_sign_hedged(msg, ctx)` is FIPS 205's default signing: the per-signature
  randomness comes from the operating system.

As in RustCrypto's crate, `sign` is the deterministic variant and `sign_with_rng` the hedged
one with the caller's random source.

## What is and is not verified

Key generation, signing and verification are calls to the verified crate's five functions.
This crate is the glue around them and is **not** covered by the proofs: the types, drawing
randomness, copying a multi-part message into one buffer, the encodings.

## Differences from RustCrypto's crate

- Only `Sha2_128s`. The other eleven parameter sets do not exist here.
- Needs the standard library (RustCrypto's crate is `no_std`).
- A `SigningKey` is always overwritten with zeros when dropped; its `Debug` output leaves
  the secret out; comparing two signing keys looks at every byte.
- The verified crate does not yet wipe its own intermediate values (FIPS 205 §3.1).

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
  RustCrypto; operating-system randomness; the secret is gone from memory after drop and
  absent from `Debug` output.

## Credit

The public interface and the PKCS#8 / SubjectPublicKeyInfo glue follow `slh-dsa`
0.2.0-rc.5 by the RustCrypto developers (copyright 2024 Trail of Bits), licensed
Apache-2.0 OR MIT. The licence texts are `LICENSE-APACHE-RustCrypto` and
`LICENSE-MIT-RustCrypto` in this directory.
