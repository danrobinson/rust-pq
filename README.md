# formal-sig

A Rust implementation of all twelve pure **SLH-DSA** parameter sets in FIPS 205
(the standardised SPHINCS+). Lean 4 proofs connect the Rust SHA-2 and SHAKE256
implementations to caller-visible RustCrypto signing, verification, key generation
and key parsing. All twelve sets pass NIST ACVP vectors and byte-for-byte
comparisons with RustCrypto. The six SHA-2 sets also have relational constant-time
proofs and unforgeability theorems under named hash assumptions.
[SHAKE256 proof](lean/Slhdsa/Proofs/Shake256.lean) · [Public API proofs](lean/Facade.lean)

Until 2026-11-22 the repository's main tree covered SLH-DSA-SHA2-128s only, and the six-set tree
lived in a subdirectory beside it. The six-set tree has replaced it; the single-set tree is git
commit `26aa3d8`. What the single-set tree had and this one does not is listed in
[HANDOFF.md](HANDOFF.md) ("What the single-set tree had that this tree does not").

## What is proven

The SHA-2 core ([rust](rust)) has one implementation with the hash length `n` as a const generic and
the rest of the parameter set passed at run time, and a module per set (`slhdsa::sha2_128s`, …,
`slhdsa::sha2_256f`) with fixed-size key types. For each set's functions, as translated to Lean by
[Aeneas](https://github.com/AeneasVerif/aeneas), [lean/Slhdsa/Theorems.lean](lean/Slhdsa/Theorems.lean)
states (namespace `slhdsa.sha2_<set>`; 37 theorems):

| Rust function (`sets::sha2_<set>::…`) | Theorem | Says |
|---|---|---|
| `slh_keygen_internal` | `keygen_correct` | returns the keys of FIPS 205 Algorithm 18 |
| `slh_sign_internal` | `sign_internal_correct` | returns the signature of Algorithm 19 |
| `slh_verify_internal` | `verify_internal_correct` | returns the verdict of Algorithm 20, for every input |
| `slh_sign` | `sign_correct` | Algorithm 22 (pure signing with context) |
| `slh_verify` | `verify_correct` | Algorithm 24 |
| `sha256::sha256`, `sha512::sha512` | `sha256_correct`, `sha512_correct` | are SHA-256 and SHA-512 (FIPS 180-4) |

Each theorem also says the function returns normally: no panic, no arithmetic overflow, no
out-of-bounds index, no non-termination. The only hypothesis is `Room`, that the message is short
enough to hash (`m.length + 152` resp. `+ 409` for the pure functions at n = 16, `+ 304` / `+ 561`
at n = 24, 32, below `usize::MAX` and `2^61`). The same statements are proved for the generic
functions at any valid parameter set (`slhdsa.generic.*`).

The proofs use no `sorry` and no axioms beyond Lean's three standard ones (`propext`,
`Classical.choice`, `Quot.sound`); every headline file ends with `#print axioms` for each theorem.

**The interface, and signing then verifying.** The interface functions have their own theorems,
in [lean/Slhdsa/ApiTheorems.lean](lean/Slhdsa/ApiTheorems.lean) (11 statements per set):

| Rust function | Theorems | Say |
|---|---|---|
| `keygen` | `api_keygen_correct`, `api_keygen_keyOk` | Algorithm 21 on the three blocks of its random bytes; the key it writes is well formed |
| `sign`, `sign_deterministic` | `api_sign_correct`, `api_sign_deterministic_correct` | Algorithm 22, hedged and with `PK.seed` as the randomness |
| `verify`, `public_key` | `api_verify_correct`, `api_public_key_correct` | Algorithm 24; the last two blocks of the private key |
| any signer, then `verify` | `complete`, `complete_internal`, `api_complete_sign`, … | for a key from key generation, the signature that signing returns is accepted by verification |

**Encodings.** `encoding` decides which byte strings are accepted as keys and signatures, compares
private keys, and produces the PKCS#8 and SubjectPublicKeyInfo encodings of keys (for each set a
fixed prefix followed by the key). [lean/Slhdsa/EncodingTheorems.lean](lean/Slhdsa/EncodingTheorems.lean)
(12 statements per set) proves each against a literal statement of the bytes, that decoding
accepts exactly the encoder's outputs and returns the key, and that the comparison is equality.

**Against the single-set statements.** [lean/Spec/Old128.lean](lean/Spec/Old128.lean) is a
verbatim copy of the single-set tree's SLH-DSA-SHA2-128s specification;
[lean/Spec/Compat128.lean](lean/Spec/Compat128.lean) proves the parameterised specification at
`Spec.sha2_128s` equal to it, function by function, and
[lean/Slhdsa/Compat128.lean](lean/Slhdsa/Compat128.lean) restates the 12 128s theorems that mention
the specification against it: literally the single-set tree's statements, up to the name of the
Rust function.

[lean/Spec/Correctness.lean](lean/Spec/Correctness.lean) proves the scheme correct at the level
of the specification (signatures made with a well-formed key verify; key generation makes
well-formed keys), for every valid parameter set.

**Constant time.** [lean/Ct](lean/Ct) proves that the branches and memory accesses of key
generation reveal nothing, and that those of signing reveal only what can be computed from the
public key, the message and the signature, for every SHA-2 set
([lean/CT_STATUS.md](lean/CT_STATUS.md)).

These proofs cover the default build ([lean](lean)) and the build with the opt-in `hw-sha2` feature ([lean-hw](lean-hw)), which runs SHA-256 and
SHA-512 on the processor's SHA-256 and SHA-512 instructions. The second proof rests on one thing
the first does not, a model of those instructions; see [below](#opt-in-hardware-sha-2-hw-sha2).

The proofs use the independent FIPS transcriptions in [lean/Spec](lean/Spec).
These define SHA-256, SHA-512, SHAKE256 and the SLH-DSA algorithms over lists of
bytes. The functional proofs cover the hash code inside the Rust crate, including
the Keccak permutation, SHAKE256 padding and multi-block output.

Details, design decisions and measurements: [STATUS.md](STATUS.md).

## What is tested

- The Rust crate passes the NIST ACVP vectors for all twelve sets: per set 10 key generation, 28
  signing, 28 verification (`cargo test --release`), and agrees byte for byte with RustCrypto's
  `slh-dsa` 0.2.0-rc.5 on keys, signatures (hedged and deterministic, with contexts) and
  encodings (`tests/rustcrypto.rs`).
- The Lean specification, compiled and run on the same vectors, matches every verification case
  of every set (`lake build spectest`; `scripts/check.sh full` also runs the slow key generation
  and signing cases).
- The adapter crate `compat/` is compared with RustCrypto's `slh-dsa` call for call: one piece of
  source compiled against both must give the same 1,056 results; and its wiping is checked by
  searching the stack and freed heap memory for the secrets of the six SHA-2 sets
  (`cd compat && cargo test`).

## Performance

Apple M5 Ultra, release builds, median of three runs (method and every number: [STATUS.md](STATUS.md),
"Measurements"); "RC" is RustCrypto's `slh-dsa` 0.2.0-rc.5 in the same binary, using hardware
SHA-2 in the `hw-sha2` columns:

The default build columns are from STATUS.md, "Measurements"; the `hw-sha2` columns (now with
the verified hardware SHA-512) were measured on 2026-11-22 with `compat/examples/timing.rs`
(medians of 7 runs, 31 for verification, through the adapter; [compat/README.md](compat/README.md),
"Timing"):

| set | keygen, default | sign, default | verify, default | keygen, `hw-sha2` | sign, `hw-sha2` | verify, `hw-sha2` | RC sign |
|---|---|---|---|---|---|---|---|
| 128s | 40.85 ms | 310.9 ms | 322.8 µs | 3.95 ms | 30.39 ms | 34 µs | 62.61 ms |
| 128f | 619.8 µs | 14.77 ms | 943.4 µs | 75 µs | 1.53 ms | 95 µs | 2.99 ms |
| 192s | 58.35 ms | 550.6 ms | 451.5 µs | 6.13 ms | 67.68 ms | 66 µs | 124.8 ms |
| 192f | 915.0 µs | 24.42 ms | 1.28 ms | 109 µs | 2.92 ms | 163 µs | 5.40 ms |
| 256s | 38.69 ms | 494.6 ms | 667.5 µs | 4.11 ms | 65.10 ms | 92 µs | 115.6 ms |
| 256f | 2.42 ms | 50.29 ms | 1.33 ms | 269 µs | 6.05 ms | 168 µs | 11.19 ms |

The default build uses only safe Rust in the Aeneas subset and is about 1.4 times slower than
RustCrypto's portable build. With `hw-sha2` it is 1.6–2.1 times faster than RustCrypto (which
uses the SHA-256 and SHA-512 instructions too) at every operation of every set.

The comparisons with OpenSSL 4.1, `fips205`, slhdsa-c and PQClean in [bench/RESULTS.md](bench/RESULTS.md)
were measured on the single-set crate (SLH-DSA-SHA2-128s; for 128s the six-set crate is within
2.5% of it). `bench/run.sh` now benchmarks the six-set crate's 128s functions under the same
names, and `cargo bench --bench sets` in `bench/` the six sets against RustCrypto.

### Multi-platform acceleration (`platform-sha2`)

Enable `platform-sha2` on either the core crate or the compatibility crate.
On x86-64 with SSE2 it dispatches to 16-way AVX-512 SHA-256 chains, SHA-NI pairs,
eight-way AVX2, or the portable chain loop. AVX-512 also batches independent FORS
parents and WOTS public-key hashes. On little-endian AArch64 it uses the hardware
chain kernel, pairs independent parents where SHA-512 instructions are available,
and uses RustCrypto compression for streaming messages. Long messages can be signed
and verified without copying the entire message to prepend its context.

**Proof coverage.** Lean proves functional refinement for both families in the default and `hw-sha2` configurations. The relational constant-time proofs cover their SHA-2 sets. For `platform-sha2`, Lean proves the extracted AVX-512 SHA-256 and SHA-512 compression cores against FIPS 180-4 for all 16 and eight lanes respectively. These proofs assume the modeled register and instruction semantics and correctly transposed input words. The AVX-512 SHA-512 FORS parent proof additionally covers the production caller from eight independent 128-byte blocks through truncation to 24 or 32 bytes, including preservation of later output rows. It models the standard array iterator, array map, and the two native-endian casts between a vector register and eight 64-bit words. [Eight-parent proof](lean-hw/Parent512/Proof.lean) The SHA-256 core also takes a precomputed four-round prefix. Lean also proves the AVX2 SHA-256 compressor from eight input byte arrays through feed-forward. The SHA-NI pair proof covers all rounds and the byte-level input and output of both lanes for any packed chaining state. [SHA-NI proof](lean-hw/Slhdsa/Proofs/ShaNi.lean) On Arm, the paired SHA-512 theorem covers both full blocks, truncation to 24 or 32 bytes, and writing both outputs. [Paired Arm proof](lean-hw/Paired/Proof.lean) The complete dispatch and its callers have hardware, differential and interoperability tests. [Block theorems](lean-hw/Slhdsa/Proofs/Platform.lean) · [SHA-2 measurements](bench/headroom.md) · [SHAKE measurements](bench/merged.md)

The extracted SHA-NI chain driver refines the portable chain specification for every digest width from 0 through 32 bytes. It accepts arbitrary 64-byte blocks and independent 32-bit start and end indices for each lane, including reversed or empty ranges. Lean checks state packing, every shared iteration, lanes with different remaining lengths, and the odd final block. The theorem compares the entire resulting block for every input and assumes valid range-slice lengths and the modeled SHA-NI, SSSE3 and SSE4.1 operations. [Chain driver theorem](lean-hw/Chainni/Top.lean) · [Two-lane step](lean-hw/Chainni/Pair.lean) · [Unequal-length chains](lean-hw/Chainni/Residual.lean)

The complete 16-lane AVX-512 SHA-256 chain driver refines the portable chain specification for 16-, 24- and 32-byte digests. Lean compares every byte of every output block for arbitrary initial state, batch length and unsigned 32-bit start and end indices. The proof covers empty and reversed ranges, mixed finishing times, short batches on both sides of the SHA-NI feature check, and the bytes after a truncated digest. It checks the unaligned counter and digest packing, masked reads and writes, cached rounds, inline compression, and termination. The theorem assumes the range arrays cover the input blocks and uses the documented instruction, memory and feature-detection models. [Complete driver theorem](lean-hw/Chainwide/Top.lean) · [In-place batches and dispatch](lean-hw/Chainwide/Driver.lean) · [Loop invariant](lean-hw/Chainwide/Loop.lean) · [Portable reference correspondence](lean-hw/Chainwide/Reference.lean) · [Complete output writer](lean-hw/Chainwrite/Top.lean) · [Three-host comparison](bench/merged.md#avx-512-chain-output-stores)



The eight-lane AVX2 driver and the complete x86 chain dispatcher refine the same portable recurrence for every digest width from 0 through 32 bytes. The proof covers all feature combinations, partial digest words, every group and its portable tail, arbitrary 32-bit ranges, and preservation of every output byte. For larger widths or short range slices, the dispatcher returns the exact result of the portable call, including its behavior on failure. The proof assumes the modeled instruction semantics, little-endian register layout, disjoint mutable slice borrows, and OS support for each enabled CPU feature. [AVX2 driver](lean-hw/Chainavx2/Top.lean) · [x86 dispatch and fallback](lean-hw/Chainx86/Top.lean)

Lean verifies the complete extracted AVX-512 WOTS endpoint-generation kernel for the 16-, 24- and 32-byte SHA-2 parameter sets. For each output keypair and chain, the destination contains the FIPS 205 Algorithm 6 PRF followed by all fifteen Algorithm 5 steps. The theorem covers empty and partial batches, crossing a keypair boundary, and preservation of each row’s 22-byte header and unused suffix. It assumes the supplied SHA-256 state represents the public seed, the rows have room for the endpoints, and the keypair and iterator counts fit their Rust integer types. For WOTS recovery, Lean verifies the stable permutation of all signature indices, the partition between digits below 15 and digits equal to 15, and the complete direct-copy loop for digit 15. Each bypassed row receives its own signature element at byte 22 while preserving the surrounding bytes, and every other row is preserved. The extracted refill loop assigns each consumed queue position to exactly one previously free lane, preserves other lanes and stops when the queue is exhausted or all lanes are active. For each newly assigned lane, Lean derives the signed SIMD byte offset from its queued index and the signature length, verifies the big-endian loads and preserves the unassigned lanes. It also verifies the counter increment, completion mask and output writes for one retirement step. These writes assume distinct, in-bounds destinations for the finishing lanes and preserve all bytes outside their endpoint slots. [Assigned signature loads](lean-hw/Wots/Assigned.lean) · [Counter and output theorem](lean-hw/Wots/Finish.lean) The outer recovery loop, its hash steps and final output still need an end-to-end proof. [Refill theorem](lean-hw/Wots/Refill.lean) · [Signature loads](lean-hw/Wots/Load.lean) [Recovery preparation theorem](lean-hw/Wots/Plan.lean) · [Ordering and partition](lean-hw/Wots/Ordering.lean) [Endpoint kernel theorem](lean-hw/Wots/Driver.lean) · [Store placement and preservation](lean-hw/Wots/Placement.lean) · [Batch computation](lean-hw/Wots/Endpoint.lean)

On x86-64 and AArch64 the extracted SHA-512 parent-block constructor writes the compressed address, both child nodes and the FIPS padding for a seeded 128-byte prefix. Given those padded blocks and the corresponding seed state, the x86 eight-lane and Arm two-lane routines return the FIPS 205 parent hash H and preserve the entries after the batch. [Parent-block theorem](lean-hw/Parentblock/Proof.lean) · [FIPS parent theorems](lean-hw/Parentblock/Fips.lean)

The FORS tree and authentication-path driver proofs cover both production SHA-512 batch widths for 24- and 32-byte nodes. On a supported CPU the drivers process every complete group. Each in-place tree output equals FIPS H on the corresponding original children. Each path output uses the signature sibling selected by the original index, in the correct order, and shifts that index by one bit. The proofs cover the untouched tail, the zero-work return when the feature is unavailable, and immediate return for every unsupported node width. They assume the FIPS public-seed state, valid buffer and address bounds, and the modeled CPU feature and instruction semantics. [Four driver theorems](lean-hw/Parentdriver/Proof.lean)

The shared AVX-512 SHA-256 digest writer used by FORS leaves, FORS parents and WOTS key digests serializes every active lane of an arbitrary vector state. Lean checks byte order, the 32-bit and 64-bit unpacks within each 128-bit lane, the register reinterpretation under the little-endian layout, bounds on each slice write, and truncation for 16-, 24- and 32-byte outputs. The theorem holds for every output slice length from zero through sixteen. [Digest writer theorem](lean-hw/Store256/Proof.lean) · [Register transpose theorem](lean-hw/Store256/Transpose.lean)

For SHA2-128s and SHA2-128f, the AVX-512 WOTS public-key digest theorem follows the production entry point for one through sixteen keys. It checks the mask and signed gather offsets, all ten 64-byte blocks, the first four SHA rounds in each block, the remaining rounds, and every returned digest byte. With the FIPS public-seed state and correctly padded inputs, each 16-byte result equals the FIPS 205 tweakable hash T. The theorem assumes AVX-512 availability and the modeled x86 instruction and memory semantics. [FIPS 205 theorem](lean-hw/Digest256/Fips.lean) · [Digest theorem](lean-hw/Digest256/Top.lean)

For all six SHA-2 parameter sets, the extracted AVX-512 FORS leaf entry point returns exactly FIPS 205 Algorithm 15 at height zero. Lean checks both padded address-and-message blocks, the shared SHA-256 rounds, both complete compressions, digest truncation, and output ordering for arbitrary batches, including empty slices and partial final groups. The theorem assumes a correctly derived public-seed state, the FORS tree address type, AVX-512 availability, nonoverflowing leaf indices and the modeled instruction semantics. [FIPS FORS leaf theorem](lean-hw/Leaf256/Fips.lean) · [Production entry point](lean-hw/Leaf256/Top.lean)

For the SHA-256 FORS parent entry point, Lean checks all 16-byte parent outputs against FIPS 205 `H` of the indexed address and the original left and right children. It covers partial batches, masked reads, unaligned word packing, shared rounds, compression, truncation and in-place writes. The output preserves the slice length and the entire suffix after the last parent. The active path assumes AVX-512 availability, the public-seed state, enough input children and nonoverflowing indices and byte offsets. Unsupported widths and counts below two return zero and preserve the buffer before querying CPU features. [Production entry and early returns](lean-hw/Parent256/Top.lean) · [In-place batch loop](lean-hw/Parent256/Driver.lean) · [FIPS batch theorem](lean-hw/Parent256/Batch.lean)


The AVX-512 SHA-512 WOTS public-key digest theorem covers batches of one through eight already-padded inputs. Each active lane consumes its own 1,280 or 2,304 bytes and returns the first 24 or 32 bytes of the corresponding SHA-512 compression chain. The proof checks effective addresses against the allocation bounds and assumes the x86 little-endian layout, the modeled SIMD instructions, and an affirmative CPU/OS feature check. Given the specified public-seed state and padded address and endpoint bytes, the returned bytes equal the FIPS 205 tweakable hash T. The extracted XMSS message initializer writes the WOTS key address, delimiter and big-endian length. Lean checks that inserting the endpoint bytes at offset 22 then produces the FIPS padding at all three parameter sizes. The SIMD computation and insertion of the endpoint bytes is still a separate proof obligation. [Padding theorem](lean-hw/Keypadding/Proof.lean) [FIPS 205 theorem](lean-hw/Gather512/Fips.lean) [Digest theorem](lean-hw/Gather512/Top.lean) · [Gather memory model](lean-hw/Gather512/FunsExternal.lean)
· [Wide x86 benchmarks](bench/wide-x86.md) · [Original cross-platform comparison](bench/platforms.md)

### Opt-in hardware SHA-2 (`hw-sha2`)

`cargo build --features hw-sha2` runs SHA-256 on the ARMv8 SHA-256 instructions and SHA-512 on
the ARMv8.2 SHA-512 instructions (FEAT_SHA512), each when the CPU has them (two separate run-time
tests). It is off by default, and AArch64 only so far: on other architectures, or on a CPU
without the instructions, the portable code runs.

**What is proved.** The backends, modules `hw` of [rust/src/sha256.rs](rust/src/sha256.rs) and
[rust/src/sha512.rs](rust/src/sha512.rs), have two layers each:

- `hw::arm`: eighteen (SHA-256) and ten (SHA-512) functions, each one to three intrinsics (loads
  and stores, add, or, and, two shifts, `EXT`s, the four SHA-256 and the four SHA-512
  instructions, and the tests for the CPU features). This is the only code Aeneas does not
  translate.
- Everything else: the SHA-256 single-block kernel, the kernel that works on four hash chains at
  once, generic in the hash length (16, 24 or 32 bytes), and the SHA-512 single-block kernel.
  Aeneas translates it like the rest of the crate. Apart from the wrappers, the only `unsafe` is
  at the three calls that enter a kernel once the CPU feature has been tested.

[lean-hw](lean-hw) holds Aeneas's translation of the crate built with the feature.
[lean-hw/Arm.lean](lean-hw/Arm.lean) gives the instructions their meaning: a transcription of the
pseudocode of `SHA256H`, `SHA256H2`, `SHA256SU0`, `SHA256SU1`, `SHA512H`, `SHA512H2`, `SHA512SU0`
and `SHA512SU1` in the Arm Architecture Reference Manual, and of the plain vector operations.
[lean-hw/Slhdsa/FunsExternal.lean](lean-hw/Slhdsa/FunsExternal.lean) defines each of the
twenty-eight functions in terms of it. From those definitions the theorems above are proved for
this build too, whichever answers the two feature tests give: the headline files of `lean-hw`
are those of the default build (links), and so are all proof files except those about
`sha256::compress`, `sha512::compress` and `hash::chain_blocks`, the functions the backends stand
in for. Their proofs ([lean-hw/Slhdsa/Proofs/Hw](lean-hw/Slhdsa/Proofs/Hw),
[lean-hw/Slhdsa/Proofs/Hw512](lean-hw/Slhdsa/Proofs/Hw512)) show that sixteen steps of the SHA-256
instructions and forty steps of the SHA-512 instructions are the compression functions of
FIPS 180-4, and that the four-lane kernel leaves every block as the portable loops would, for
each of the three hash lengths. The SHA-512 statement, `slhdsa.hw_compress_block512_spec`
([lean-hw/Slhdsa/Proofs/Hw512/Compress.lean](lean-hw/Slhdsa/Proofs/Hw512/Compress.lean)):

```lean
theorem hw_compress_block512_spec (hw : Arm.haveSha512 = true) (state : Array U64 8#usize)
    (block : Array U8 128#usize) :
    sha512.hw.compress_block state block ⦃ r =>
      wv r.val = compress (wv state.val) (bytes block.val) ⦄
```

and, without the instructions (`Hw512/Guard.lean`), `compress_block512_undef`:
`Arm.haveSha512 = false → sha512.hw.compress_block state block = fail .undef`.

**What that rests on**, beyond what the default build's proof rests on:

- *The instruction model is the processor's behaviour.* This is tested, not proved.
  [vectors/arm-wrappers.txt](vectors/arm-wrappers.txt) records what the wrappers return on an
  Apple M5 for 2,961 inputs (1,745 SHA-256, 1,216 SHA-512); `cargo test --features hw-sha2` checks the record against the
  processor it runs on, and [lean-hw/ArmTest.lean](lean-hw/ArmTest.lean) runs the model on the
  same record. They agree on every case.
- *Each wrapper does what its definition says*: that the intrinsic it calls is the instruction
  named, and that its bounds check covers the memory it touches. With the two vector types, the
  `clone` of one and `panic_bounds_check` that is thirty-two trusted definitions in three files
  (`Arm.lean`, `Slhdsa/TypesExternal.lean`, `Slhdsa/FunsExternal.lean`); the SHA-512 ones were
  added on 2026-11-22 and are not covered by the review below.
- *What the feature tests mean.* Every wrapper except the two tests fails in the model when the
  processor lacks its instructions (`Arm.haveSha2`, `Arm.haveSha512`, independent), and the proofs
  get the fact they need from the code's own test
  ([lean-hw/Slhdsa/Proofs/Hw/Guard.lean](lean-hw/Slhdsa/Proofs/Hw/Guard.lean),
  [lean-hw/Slhdsa/Proofs/Hw512/Guard.lean](lean-hw/Slhdsa/Proofs/Hw512/Guard.lean)). What stays
  trusted is that `std`'s feature detection answers truthfully.

An independent review of these trusted pieces and of the context-string security statements of
the single-set tree is in [reports/Trusted statements review.md](<reports/Trusted statements review.md>).
`scripts/check-arm.sh` replays the record on another AArch64 machine (needs only Rust; so far run
on the M5 only).

## The interface to use ([compat/](compat))

The verified crate works on byte arrays. [compat/](compat) puts the interface of RustCrypto's
`slh-dsa` 0.2 around the verified functions, for the twelve SHA-2 and SHAKE sets:
the same `SigningKey`, `VerifyingKey` and `Signature` types, the `signature` crate's traits, and
the PKCS#8 encodings. A program that uses `slh-dsa` with the SHA-2 sets switches by changing its
dependency line:

```toml
slh-dsa = { package = "slhdsa-compat", path = "…/formal-sig/compat" }
```

The public SHA-2 and SHAKE proofs follow the production signer and verifier through message
assembly, parameter dispatch, and construction of the result. They also cover
caller-supplied RNG key generation, randomized signing on successful and failed
draws, the three raw byte parsers, and PKCS#8/SPKI key import after ASN.1 decoding. The portable and accelerated builds use
the same public statements. [Public API proofs](lean/Facade.lean)

External DER parsing, operating-system entropy, allocation, and physical memory
wiping have separate trust assumptions. [Adapter proof scope](compat/README.md#public-api-proofs)

## What is not proven

- **That SHA-2 has the properties the security proof needs.** Unforgeability is reduced to named
  hash properties, which remain assumptions; see [Security](#security).
- **The specification is the standard.** `lean/Spec` is a hand transcription of FIPS 205; it is
  checked against NIST's vectors, not proven against the PDF.
- **The toolchain.** The proof is about Aeneas's translation of the Rust MIR. Charon, Aeneas and
  rustc are trusted, as is the Lean kernel.
- **The processor, for `hw-sha2`.** See [above](#opt-in-hardware-sha-2-hw-sha2).
- **Side channels, beyond the source.** The constant-time theorems are about the Rust source: the
  compiler, the processor's instruction timing, speculation, power and faults are outside them.
- **Pre-hash variants.** HashSLH-DSA is outside the implemented interface. The
  verified crate takes seeds and `addrnd` from the caller; drawing them from the operating system
  is done in `compat/`, outside the proofs.
- **Wiping** (FIPS 205 §3.1): done by `compat/` and tested there, not proved.
- **Faults.** Nothing is proved about a disturbed computation.
- **The rest of what a user runs, outside the translations** (surveyed 2026-11-22): in
  `rust/src`, only the intrinsic wrappers `sha256::hw::arm` (18 functions, 76 code lines) and
  `sha512::hw::arm` (10 functions, 51 code lines), defined by the instruction model, and the
  test-only module `sha256::hw::vectors` (`#[cfg(test)]`) are not translated; everything else,
  including `hw_active` (proved to return the feature test's answer: `sha256_hw_active_eq`,
  `sha512_hw_active_eq`), is. The feature detection (`std::arch::is_aarch64_feature_detected!`)
  is trusted to answer truthfully; the `#[cfg]` branches select between the two translated
  builds (on targets other than little-endian AArch64 the `hw-sha2` build compiles to the
  default build's code, which the default proofs cover, plus the two `hw_active` functions
  returning `false`); the `extern crate std` and `forbid`/`deny(unsafe_code)` attributes in
  `lib.rs` carry no logic; neither crate has a build script. The `unsafe` calls that enter a
  kernel after its feature test (three) are covered as calls of translated functions; that the
  test makes them sound is the trusted meaning of the wrappers. Allocation failure is not
  modelled (Aeneas's `Vec` succeeds up to `usize::MAX` bytes). Panics are proved absent under
  the stated hypotheses; the adapter's own `assert!`s (randomizer and seed lengths) are proved
  to fail exactly when those lengths are wrong.

## Layout

- `rust/` — the crate (`no_std` + `alloc`, safe Rust in the Aeneas subset apart from the `hw-sha2`
  wrappers): generic modules (`hash`, `wots`, `xmss`, `fors`, `ht`, `slh`, `api`, `encoding`, `adapter`,
  `sha256`, `sha512`) and the per-set modules (`sets.rs`).
- `lean/` — `Spec/` (the specification), `Slhdsa/Types.lean`, `Funs.lean` (generated by Aeneas;
  do not edit), `Slhdsa/Proofs/` (one file per layer), the headline files
  `Slhdsa/{Theorems,ApiTheorems,EncodingTheorems,Compat128,AdapterTheorems}.lean`, `Ct/` (constant time),
  `SpecTest.lean`, `CT_STATUS.md`.
- `lean-hw/` — the same for the crate built with `hw-sha2`: its translation, the instruction model
  (`Arm.lean`, `Slhdsa/{Types,Funs}External.lean`), the kernel proofs (`Slhdsa/Proofs/Hw/`), its
  `Ct/`, `ArmTest.lean`, and links to the files of `lean/` that do not depend on the build.
- `security/` — the security theorems (`MLink`, `MReduction`, `ME2E`, `MIdeal` for the six sets;
  the generic `Reduction`, `Ideal`, `Link`, `E2E` they build on); `security/STATUS.md`.
- `security-hw/` — the same libraries compiled against `lean-hw`. No source of its own.
- `quantum/` — the quantum-random-oracle analysis of SLH-DSA-SHA2-128s ([below](#quantum-adversaries-quantum-see-quantumstatusmd)).
- `compat/` — the RustCrypto-style adapter (forwarding to `rust/src/adapter.rs` and the rest of the
  verified crate; its own code is not verified, see above).
- `bench/` — benchmarks against other libraries, with interoperability checks.
- `ct-evidence/` — binary-level constant-time evidence (emulator traces, dudect timing,
  disassembly), recorded on the single-set crate and repointed at this one.
- `vectors/` — the NIST vectors for the twelve sets, and the record of the intrinsic wrappers on a
  processor.
- `scripts/` — `extract.sh`, `extract-hw.sh` (regenerate the translations), `ct-gen.sh` (the
  instrumented copy for the constant-time proofs), `gen/` (generators of the per-set Lean files),
  `extract_vectors.py`, `check.sh` (run everything), `check-arm.sh` (another processor).
- `reports/`, `research_notes/` — reports and notes.

## Reproducing

Needs Rust (rustup), Lean (elan), Aeneas with Charon built under `.tools/aeneas` (OCaml 5.3 via
opam; see the Aeneas README), and, for `security/`, VCVio at `.tools/VCVio-upstream`
([security/README.md](security/README.md)). Then:

```bash
./scripts/check.sh                     # everything except the quantum check
(cd quantum && scripts/check-integration.sh)
```

## Security

Machine-checked security theorems, with standard axioms only, in one Lean workspace
([security/](security)); [security-hw](security-hw) compiles the same files against the
translation of the crate built with `hw-sha2`, so every statement here also holds for that build,
given its instruction model. They go through one link: the Rust functions compute the same bytes
as the executable SLH-DSA-SHA2 scheme of the [VCVio](https://github.com/Verified-zkEVM/VCVio)
library at that set (`MLink`: `lean/Spec` equals VCVio's definitions, including SHA-256, SHA-512,
HMAC and MGF1, for each of the six sets). All names below are per set,
`ME2E.sha2_<set>.…`; [security/STATUS.md](security/STATUS.md) has the statements verbatim.

### Standard model: reduction to named hash properties

`rust_security` and `rust_pure_security`: the Rust key generation, signing and verification (the
internal functions, resp. the ones with context strings) never panic and are pointwise the
deterministic cores of the byte-level scheme; and, with the real SHA-2 functions and no random
oracle, every chosen-message forger, strong or existential, against that scheme has advantage at
most the sum of twelve advantages of explicitly constructed adversaries: PRF security of `PRF`
and of `PRF_msg`; interleaved target subset resilience of `H_msg`; decisional second-preimage
resistance of `F` plus 3 × second-preimage resistance at the FORS leaves; second-preimage
resistance of `F`, `H`, `T_len` and `T_k`; and (w − 2) × undetectability, preimage resistance and
second-preimage resistance of `F` along the WOTS chains (proved in `security/Reduction`,
instantiated by `MReduction`). `api_pure_security` restates it for the interface functions
(`keygen`, `sign`, `sign_deterministic`, `verify`). Which SHA-2 function each game is about differs between the n = 16
and the n = 24, 32 sets (SHA-512 for `H`, `T_l`, `H_msg`, `PRF_msg` there).

The shape follows Hülsing–Kudinov (ePrint 2022/346) and its EasyCrypt formalisation (ePrint
2024/910). Limits: the twelve right-hand terms are assumptions about the SHA-2-based functions,
not proved small; three adversaries are polynomial in the number of signing queries, the other
nine register about 2^63 to 2^82 targets (these games fix targets before the public seed is
revealed); no running-time statement; single key, pure mode only.

### Random-oracle model

`pure_rom_security`, `rust_pure_rom_security_bytes`, `api_pure_rom_security(_bytes)`: with the
tweakable hash, `H_msg` and `PRF_msg` as three independent random oracles, the strong forging
advantage against the context-string interface the Rust functions implement is at most VCVio's
`securityBound params (256^n) 2 1 qh qs` for `qh` hash and `qs` signing queries, at every set.
Nothing transfers this bound to the SHA-2 instantiation (that is the random-oracle methodology).

### Ideal compression function (SLH-DSA-SHA2-128s)

With SHA-256's compression function a random table that every adversary may query, and
everything else the real construction, `security/Ideal` bounds each of the twelve assumptions in
the adversary's own queries and composes them: `Ideal.suf_ideal_closed_tight8`,
`euf_ideal_closed_tight8` and their context-string forms, with hypotheses on the forger only.
`MIdeal.sha2_128s.rust_ideal_security_closed_tight8`, `…_pure_tight8` and
`api_ideal_security_closed_pure_tight8` state this next to the Rust functions of the 128s set.
Machine-checked points, messages up to 2^26 bytes:

| signatures | forger's compression queries | forgery probability at most |
|---|---|---|
| 2^20 | 2^60 | 2^-77 + 2^-132 + 2^-63 |
| 2^40 | 2^64 | 2^-63 + 2^-94 + 2^-59 |
| 2^64 | 2^64 | 2^-45 + 2^-46 + 2^-39 |

A tighter bound (about 2^-67, 2^-63, 2^-62 at these points) is under way in
`security/Ideal/Direct` and is **not proved**: its statements are conditional on one remaining
hypothesis. See [HANDOFF.md](HANDOFF.md) and [security/status/DIRECT.md](security/status/DIRECT.md).

Limits: the subset-resilience leg is vacuous once `qf + 4·qs + 2` (compression queries plus four
times the signatures) reaches about 2^70; the statement averages over random tables and says
nothing about the real compression function; no Davies–Meyer model; 128s only (the other sets
would need the counting re-instantiated and, at n = 24, 32, an ideal SHA-512 compression
function). What would tighten it: `security/status/TIGHT.md`.

### Quantum adversaries ([quantum/](quantum), see `quantum/STATUS.md`)

`slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc_closed`
([quantum/Integration/SlhDsaComposedClosed.lean](quantum/Integration/SlhDsaComposedClosed.lean)):
for SLH-DSA-SHA2-128s at the external pure byte interface, with the four hash components (Thash,
H_msg, PRF, PRF_msg) independent uniformly random functions on length-capped domains (extended
by constants outside the caps), reached through one quantum oracle, every quantum forger with at
most `q` oracle calls and `qs` classical signing queries within the caps has SUF-CMA (EUF-CMA)
advantage, averaged over the functions, at most an explicit bound; hypotheses on the forger only,
and `35 ≤ c.tl`. Machine-checked numeric point: at most 2^-22 at 2^40 oracle calls and 2^20
signatures. The scheme in it is `Reduction.pureBytesAlg Link.vp (randPrims ω) …`, the same generic
definition whose real-SHA-2 instance the Rust functions compute (`MIdeal.sha2_128s.pure_bytes_end_to_end`),
but no theorem relates the capped random functions to SHA-2 or to the Rust code: there is no
Rust-level quantum statement (there was none in the single-set tree either). Limits: the
reduction's own hash evaluations are charged as quantum queries, so the bound exceeds 1 from
about 2^28 signatures; equivalence with unbounded random oracles is informal; an independent
statement-level review is in [quantum/AUDIT-closed.md](quantum/AUDIT-closed.md).

### Not covered

- **Randomness.** The Rust functions are the deterministic cores; sampling the seeds and
  `addrnd` uniformly is the caller's job.
- **Signature count.** Security degrades with the number of signatures as the standard says;
  nothing enforces a limit.

## Binary-level evidence ([ct-evidence](ct-evidence))

On the single-set crate (results of 2026-11-21, [ct-evidence/RESULTS.md](ct-evidence/RESULTS.md)):
under an emulator, control flow, memory addresses, allocation sizes and copy lengths were identical
across secrets in every comparison, in both builds; in timing (dudect), nothing above the hash
level was distinguishable, and short hash calls were distinguishable only with the processor's
data-independent-timing mode off. The harness now builds against this crate's 128s functions; on
it only the emulator's self-check (`cttrace hwcheck`) has been run.
