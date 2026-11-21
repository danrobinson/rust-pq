# formal-sig

A Rust implementation of **SLH-DSA-SHA2-128s** (FIPS 205, the standardised
SPHINCS+) with a machine-checked proof, in Lean 4, that the Rust code computes
exactly what the standard specifies.

## What is proven

For the Rust functions in [rust/src](rust/src), as translated to Lean by
[Aeneas](https://github.com/AeneasVerif/aeneas), the theorems in
[lean/Slhdsa/Theorems.lean](lean/Slhdsa/Theorems.lean) state:

| Rust function | Theorem | Says |
|---|---|---|
| `slh_keygen_internal` | `keygen_correct` | returns the keys of FIPS 205 Algorithm 18 |
| `slh_sign_internal` | `sign_internal_correct` | returns the signature of Algorithm 19 |
| `slh_verify_internal` | `verify_internal_correct` | returns the verdict of Algorithm 20, for every input |
| `slh_sign` | `sign_correct` | Algorithm 22 (pure signing with context) |
| `slh_verify` | `verify_correct` | Algorithm 24 |
| `sha256` | `sha256_correct` | is SHA-256 (FIPS 180-4) |

Each theorem also says the function returns normally: no panic, no arithmetic
overflow, no out-of-bounds index, no non-termination. The only hypothesis is
`Room`, that the message is short enough to hash: under 2^61 bytes, which is
the limit of SHA-256 itself and beyond any real machine's memory.

The proofs use no `sorry` and no axioms beyond Lean's three standard ones
(`propext`, `Classical.choice`, `Quot.sound`); the file ends with
`#print axioms` for each theorem.

"What the standard specifies" means the Lean transcription in
[lean/Spec](lean/Spec): about 420 lines over lists of bytes, depending only on
core Lean. The SHA-256 and HMAC inside the Rust crate are verified too, so no
hash function is assumed correct.

## What is tested

- The Rust crate passes the NIST ACVP vectors for SLH-DSA-SHA2-128s: 10 key
  generation, 28 signing, 28 verification (`cargo test --release`).
- The Lean specification, compiled and run on the same vectors, matches all 28
  verification cases, 2 key generation cases and 4 signing cases, one from each
  signing group (`lake build spectest`; the spec is slow, so it runs a subset).

## Performance

Measured on Apple Silicon (M5 Ultra), default release build, median of two
rounds ([bench/RESULTS.md](bench/RESULTS.md), run 4; `bench/run.sh` reproduces
it):

| | keygen | sign | verify |
|---|---|---|---|
| this crate | 40.4 ms | 305 ms | 324 µs |
| this crate, `hw-sha2` (below) | 4.00 ms | 30.2 ms | 35.4 µs |
| RustCrypto `slh-dsa` | 8.30 ms | 62.6 ms | 63.8 µs |
| OpenSSL 4.1 | 7.32 ms | 56.0 ms | 58.9 µs |
| slhdsa-c (portable C) | 28.6 ms | 218 ms | 225 µs |
| `fips205` as shipped | 61.2 ms | 472 ms | 479 µs |

The default build is about 5 times slower than RustCrypto and OpenSSL, which
use the ARM SHA-2 instructions; safe Rust in the Aeneas subset cannot. With
the opt-in `hw-sha2` feature the crate is about 2.1 times as fast as
RustCrypto and 1.8 times as fast as OpenSSL at key generation and signing, and
1.8 and 1.7 times at verification. Verifying a 1 MiB message, which is mostly
hashing the message, takes 352 µs against 365 µs and 405 µs.

The crate interoperates with RustCrypto, `fips205`, OpenSSL and slhdsa-c in
both builds: same keys from the same seeds, signatures verify both ways, and
deterministic signatures are byte-identical.

### Opt-in hardware SHA-2 (`hw-sha2`)

`cargo build --features hw-sha2` runs SHA-256 on the ARMv8 SHA-256
instructions when the CPU has them. It is off by default, and AArch64 only so
far: on other architectures, or on a CPU without the instructions, the
portable code runs.

**The theorems in this repository are about the default build, not this one.**
The backend is the crate's only `unsafe` code: module `hw` of
[rust/src/sha256.rs](rust/src/sha256.rs), about 330 lines with comments.
Aeneas translates the default build, in which that module does not exist. The
module stands in for two functions of the verified code, and everything else is
the same code in both builds:

- `sha256::compress`, the compression function on one block;
- `hash::chain_blocks`, which takes a set of independent 64-byte blocks and,
  for each, repeats a step a given number of times: write the step number
  into the block, compress it, and put the first 16 bytes of the result back
  into the block. One step is `F`, `PRF` or `H` of SLH-DSA, so nearly every
  hash of the scheme is a step of this function.

So a build with the feature computes what the verified build computes provided
that

> `hw::compress` returns what the portable code of `compress` returns, and
> `hw::chain_blocks` leaves in the blocks what the portable loops of
> `chain_blocks` leave there.

That statement is tested, not proved. With the feature on, `compress` agrees
with the `sha2` crate's compression function on 200,000 random and 5,140
edge-case inputs, and `chain_blocks` agrees with a reference written from that
function on 7,360 random batches of 0 to 140 blocks, with step ranges of every
kind the crate uses and step numbers around every carry
([rust/tests/compress.rs](rust/tests/compress.rs); the portable code passes the
same tests). The crate passes the NIST vectors, and it is byte-identical to the
other libraries in the interoperability check.

Where the speed comes from: the verified code is arranged so that the hashes
that do not depend on each other reach `chain_blocks` together (the 35 chains
of a WOTS+ key, the leaves and levels of a FORS subtree, the 14 FORS trees of a
verification). The processor has one unit for the SHA-256 round instructions,
and a single hash keeps it waiting, because each step needs the result of the
one before. The backend works on four chains at once, staggered so the unit
always has work, and skips the rounds whose inputs or outputs a chain step
does not use. In the default build the same function is a plain loop.

## What is not proven

- **That SHA-256 has the properties the security proof needs.** Unforgeability
  is reduced to named hash properties, which remain assumptions; see
  [Security](#security).
- **The specification is the standard.** `lean/Spec` is a hand transcription
  of FIPS 205; it is checked against NIST's vectors, not proven against the PDF.
  Two deliberate departures in form, not value: loops are written as folds, and
  the hypertree treats layer 0 inside its loop.
- **The toolchain.** The proof is about Aeneas's translation of the Rust MIR.
  Charon, Aeneas and rustc are trusted, as is the Lean kernel.
- **Side channels.** Nothing about timing or memory access patterns is proven.
  There is an audit and binary-level evidence, with one timing finding; see
  [Further work](#further-work-in-this-repository).
- **Other parameter sets in the main tree.** `rust/` and `lean/` are SHA2-128s
  only; all six SHA-2 sets are covered in the separate `multi/` copy. The pre-hash variants
  (HashSLH-DSA) and randomness generation are not implemented; callers supply
  seeds and `addrnd`.

## Layout

- `rust/` — the crate. Plain safe Rust: no `unsafe`, traits, iterators or closures
  (the opt-in `hw-sha2` backend aside; see [Performance](#performance)).
- `lean/Spec/` — the specification (`Sha256.lean`, `SlhDsa.lean`).
- `lean/Slhdsa/Types.lean`, `Funs.lean` — generated by Aeneas; do not edit.
- `lean/Slhdsa/Proofs/` — one file per layer: `Sha256`, `Hash`, `Util`,
  `Wots`, `Xmss`, `Fors`, `Ht`, `Slh`.
- `lean/Slhdsa/Theorems.lean` — the headline statements.
- `security/` — the link to VCVio's security theorem (`Link`) and the
  end-to-end statements from the Rust code (`E2E`).
- `vectors/` — the NIST vectors used by both test suites.
- `bench/` — benchmark against other libraries, with interoperability checks.
- `opt/` — working copy in which the hashing optimisation was developed and
  re-verified; `opt/original/` holds the crate and proofs from before it.
- `scripts/extract.sh` — regenerate the Lean translation from the Rust.
- `scripts/check.sh` — run everything.

## Reproducing

Needs Rust (rustup), Lean (elan), and Aeneas with Charon built under
`.tools/aeneas` (OCaml 5.3 via opam; see the Aeneas README). Then:

```bash
./scripts/check.sh
```

## Security

Two machine-checked security theorems are attached to the Rust code, in one
Lean workspace ([security/](security)), with standard axioms only. Both go
through the same link: the Rust key generation, signing and verification
compute the same bytes as the executable SLH-DSA-SHA2-128s of the
[VCVio](https://github.com/Verified-zkEVM/VCVio) library
(`E2E.end_to_end`, via [security/Link](security/Link), which proves `lean/Spec`
equal to VCVio's definitions including SHA-256, HMAC and MGF1).

### Standard model: reduction to named hash properties

`E2E.standard_model_security_split` and `E2E.pure_standard_model_security_split`
([security/E2E/FinalSplit.lean](security/E2E/FinalSplit.lean)), proven in
[security/Reduction](security/Reduction): with the real SHA-2 functions and no
random oracle, every chosen-message forger, strong or existential, against the
internal algorithms or against sign/verify with context strings, has advantage
at most the sum of twelve advantages of explicitly constructed adversaries:

- PRF security of `PRF` (on the scheme's secret-key addresses) and of `PRF_msg`;
- interleaved target subset resilience of `H_msg`;
- decisional second-preimage resistance of `F` plus 3 x second-preimage
  resistance of `F`, at the FORS leaves;
- second-preimage resistance of `F`, `H`, `T_len` and `T_k`;
- 14 x undetectability, preimage resistance and second-preimage resistance of
  `F` along the WOTS chains.

All are the multi-target, distinct-tweak games of the SPHINCS+ literature. The
shape follows Hulsing-Kudinov (ePrint 2022/346) and its EasyCrypt
formalisation (ePrint 2024/910), which covers existential unforgeability of
abstract SPHINCS+; the strong-unforgeability and context-string statements,
and the tie to an implementation, are additional here. Two independent
reviews of the Lean source found the statements sound and the games genuine.

Limits of this theorem:

- **The twelve right-hand terms are assumptions** about the SHA-256-based
  functions. Nothing proves them small.
- **Reduction cost.** Three of the adversaries are polynomial in the number of
  signing queries. The other nine register between about 2^63 and 2^79.8
  targets, because these games fix targets before the public seed is revealed.
  The paper's and EasyCrypt's reductions have the same shape. There is no
  formal running-time statement.
- **Single key, pure mode** (no pre-hash variant). The statement here is for
  classical adversaries; the lift to quantum forgers is in `quantum/`.
- **Typed signatures.** The game is over VCVio's typed signatures; the
  byte-level statement follows from the proven codec lemmas but is not itself
  stated as a theorem.
- One second-preimage term on `F` has no counterpart in the paper, and the
  FORS-tree and XMSS-tree hashes share one `H` term.

### Random-oracle model

`E2E.end_to_end` also carries VCVio's random-oracle bound (`security_128s`):
with the tweakable hash, `H_msg` and `PRF_msg` as three independent random
oracles, the strong forging advantage is at most
`securityBound params (256^16) 2 1 qh qs` for `qh` hash and `qs` signing
queries. VCVio's documentation puts this at about 127 bits for
`qh = qs = 2^64`; that figure is theirs, not rechecked here. VCVio's generic
lemma connecting the oracle scheme to concrete primitives is false for its
SHA-2 instantiation (`not_hprf`), so that step is proven here by another route.

### Not covered by either

- **Randomness.** The Rust functions are the deterministic cores; sampling the
  seeds and `addrnd` uniformly is the caller's job.
- **Signature count.** Security degrades with the number of signatures as the
  standard says (2^64 for this parameter set); nothing enforces a limit.

Building it needs upstream VCVio cloned at `.tools/VCVio-upstream`; see
[security/README.md](security/README.md).

## Further work in this repository

These extend the results above. Each has its own status file with exact
statements; the summaries here say what is and is not established.

### All six SHA-2 parameter sets ([multi/](multi))

A parameter-generic Rust implementation (with SHA-512 and HMAC-SHA-512) and
the same guarantees for SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}:
refinement to a parameterised FIPS 205 spec (37 headline theorems), all NIST
ACVP non-pre-hash vectors passing, and the link to VCVio plus the
standard-model reduction instantiated per set
([multi/security](multi/security), 129 headline theorems). It is a separate
copy and has not been merged into `rust/` and `lean/`. Checks:
`multi/scripts/check.sh` and `multi/security/scripts/check.sh`.

### Quantum adversaries ([quantum/](quantum), see `quantum/STATUS.md`)

- **Proven:** the standard-model reduction holds for every quantum forger that
  makes classical signing queries, for all headline variants, with each
  reduction machine certified to be the classical reduction code around the
  forger's program.
- **Proven, for a uniformly random function with quantum queries:** bounds of
  order q^2/2^128, independent of the number of targets, for the exact adaptive
  second-preimage, preimage, undetectability, decisional second-preimage
  (when no quantum queries precede the seed reveal) and PRF games; subset resilience
  with the SPHINCS+ covering sum when hash queries follow the last signing query.
- **Proven, composed theorem for the scheme:**
  `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc_closed`
  ([quantum/Integration/SlhDsaComposedClosed.lean](quantum/Integration/SlhDsaComposedClosed.lean)).
  With the four hash components independent random functions on capped
  domains, reached through one quantum oracle, every quantum forger with at
  most `q` oracle calls and `qs` classical signing queries, within the
  message-length caps, has advantage at most an explicit bound. The only
  hypotheses are on the forger. Machine-checked numeric point: at most 2^-22
  at 2^40 oracle calls and 2^20 signatures.
- **Limits of that theorem:** the reduction's own hash evaluations (about two
  million per signature) are charged as quantum queries, so the bound exceeds
  1 from about 2^28 signatures, or from about 2^53 oracle calls at 2^20
  signatures (evaluated numerically, not machine-checked). Outside the caps
  the hash functions are constants, so equivalence with unbounded random
  oracles is informal. Subset resilience keeps its reprogramming loss, which
  dominates the bound. Nothing is established about SHA-2 itself. An
  independent statement-level review is in
  [quantum/AUDIT-closed.md](quantum/AUDIT-closed.md).

### Ideal compression function ([security/Ideal](security/Ideal), see `security/IDEAL_STATUS.md`)

With SHA-256's compression function a random table that every adversary may
query, and everything else the real construction, each of the twelve
assumptions has an explicit bound in the adversary's own queries, independent
of the number of targets except over 2^256. An independent review found these
sound.

The composed bound is proven with hypotheses on the forger only:
`suf_ideal_closed` and `euf_ideal_closed`
([security/Ideal/Realize/Final.lean](security/Ideal/Realize/Final.lean)). A
forger making at most `qf` compression queries and `qs` signing queries, on
messages of at most `ℓ` bytes, forges with probability at most an explicit
bound. Machine-checked points, for messages up to 2^26 bytes:

| signatures | forger's compression queries | forgery probability at most |
|---|---|---|
| 2^20 | 2^60 − 2^46 | 2^-70 + 2^-128 + 2^-61 |
| 2^40 | 2^64 | 2^-50 + 2^-88 + 2^-41 |
| 2^64 | 2^64 | 2^-44 + 2^-43 + 2^-31 |

`rust_ideal_security_closed`
([security/Ideal/RustFinalClosed.lean](security/Ideal/RustFinalClosed.lean))
states this next to the Rust refinement. Limits: the theorem is about the
internal interface (FIPS 205 Algorithms 18-20), not sign/verify with a context
string; the subset-resilience leg is vacuous once the forger's compression
queries plus twice the signatures reach about 2^70; the security statement
averages over random tables and says nothing about the real compression
function. Nothing is proven in the cipher-based (Davies-Meyer) model. An
independent statement-level review is in
[security/status/AUDIT-closed.md](security/status/AUDIT-closed.md).

### Side channels ([rust/ct-evidence](rust/ct-evidence), see `lean/CT_STATUS.md`)

Nothing about side channels is proven. A source audit found no
secret-dependent branch or index, and emulated execution traces of the
compiled code were identical across thousands of secret pairs. A timing test
on bare SHA-256 showed a small data-dependent difference that disappears with
the CPU's data-independent-timing mode, which the crate cannot enable itself.
A Lean proof is designed but not built.
