# formal-sig

A Rust implementation of all twelve pure **SLH-DSA** parameter sets in FIPS 205
(the standardised SPHINCS+). Lean 4 proofs connect the Rust SHA-2 and SHAKE256
implementations to signing, verification, key generation
and key parsing through this library’s RustCrypto-compatible API. All twelve sets pass NIST ACVP vectors and byte-for-byte
comparisons with RustCrypto. All twelve sets also have source-level leakage proofs and classical unforgeability bounds under named hash assumptions. Lean also proves that the measured Apple arm64 public keygen, signing and verification drivers return the same keys, signature bytes and verdict as the public Rust session for all twelve sets, under local cryptographic and runtime contracts. Linked Linux AArch64 and x86-64 proofs cover selected primitives. [End-to-end proof and remaining contracts](reports/Linked%20signer%20verification.md) · [Proof scope and artifact checks](reports/SHAKE%20and%20linked%20binary%20verification.md)
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
public key, message, public context and signature, for all twelve sets
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

The platform-optimized build had lower median latency than OpenSSL 4.1.0 in **1,344 of 1,344 workloads**
and RustCrypto `slh-dsa` 0.2.0-rc.5 in **1,339 of 1,344**. The five RustCrypto wins were all
extractions of a 32-byte public key on the Xeon 8275CL or Graviton4. These measurements cover
all twelve SHA-2 and SHAKE parameter sets with `platform-sha2` enabled.

**Deterministic signing of a 32-byte message.** Each range gives the smallest and largest
speedup across the twelve parameter sets. A 4× speedup means signing took one-quarter of
the peer’s time.

| Processor | Speedup over RustCrypto | Speedup over OpenSSL |
|---|---:|---:|
| Apple M5 Ultra | 1.8–4.0× | 1.8–2.8× |
| Intel Xeon 8275CL | 11.6–18.9× | 5.4–11.0× |
| Intel Xeon 8124M | 13.0–21.3× | 6.1–12.4× |
| Intel Xeon 6975P-C | 4.0–12.1× | 3.2–5.5× |
| AMD EPYC 9R45 | 4.3–16.5× | 3.5–7.3× |
| AWS Graviton2 | 2.1–3.4× | 1.3–2.4× |
| AWS Graviton4 | 3.3–6.0× | 1.5–2.6× |

The suite measured key generation, public-key extraction, deterministic and hedged signing,
verification, and raw and DER key conversions. Signing and verification used 32-byte and
1 MiB messages. After warm-up, each workload ran six times, once per provider order.
Speedups are medians of within-round peer/library latency ratios. Linux used a pinned vCPU.
The Apple host ran under normal scheduling with concurrent work.

[Benchmark report](bench/results/peers-optimized/README.md) ·
[Method and reproduction](bench/peers/README.md) ·
[Interactive comparison by processor and operation](https://chatgpt.com/space/page_c6515006f9348191989c73423bcb0fbb) ·
[Signature and key-generation timings](bench/results/peers-optimized/workloads.csv) ·
[Key conversion timings](bench/results/peers-optimized/encoding-workloads.csv)

[Seven-platform comparison with Botan, parallel-sphincsplus, and Conduition, including multicore and Apple GPU signing](bench/results/optimized-competitors/README.md)

### Parallel CPU signing (`parallel`)

Enable the opt-in Cargo feature `parallel` on the core or compatibility crate to use spare CPU threads for a single signature. It includes `platform-sha2`. The caller computes FORS while scoped workers compute the independent XMSS authentication nodes. On AVX-512 CPUs, this build also batches eight SHAKE leaves and uses the vectorized Keccak round function for short inputs. Applications signing many independent messages can keep the single-threaded configuration to control concurrency.

The five-platform rerun covers all 122 workloads where a peer previously had lower median latency. The new build won each comparison, including one-thread comparisons on the Xeon 6975P-C and Apple CPU signing against OpenCL. Lean proves that every joined worker schedule in the model yields the FIPS 205 signature bytes, the eight-leaf batch yields the specified XMSS node, and both x86 single-state dispatch branches yield Keccak-f. Source-bound symbolic checks cover the Rust signer and the compiled subtree at all three digest widths. [Proofs, assumptions and replay](lean-hw/Parallel/README.md) · [Measurements](bench/results/parallel/README.md)

### Multi-platform acceleration (`platform-sha2`)

Enable `platform-sha2` on either the core crate or the compatibility crate.
On x86-64 with SSE2 it dispatches to 16-way AVX-512 SHA-256 chains, SHA-NI pairs,
eight-way AVX2, or the portable chain loop. AVX-512 also batches independent FORS
parents and WOTS public-key hashes. On little-endian AArch64 it uses the hardware
chain kernel, pairs independent parents where SHA-512 instructions are available,
and uses RustCrypto compression for streaming messages. Long messages can be signed
and verified without copying the entire message to prepend its context.

**Proof coverage.** Lean proves functional refinement for both families in the default and `hw-sha2` configurations. The relational leakage proofs cover the SHA-2 and SHAKE sets in both configurations. For `platform-sha2`, Lean proves the extracted AVX-512 SHA-256 and SHA-512 compression cores against FIPS 180-4 for all 16 and eight lanes respectively. These proofs assume the modeled register and instruction semantics and correctly transposed input words. The AVX-512 SHA-512 FORS parent proof additionally covers the production caller from eight independent 128-byte blocks through truncation to 24 or 32 bytes, including preservation of later output rows. It models the standard array iterator, array map, and the two native-endian casts between a vector register and eight 64-bit words. [Eight-parent proof](lean-hw/Parent512/Proof.lean) The SHA-256 core also takes a precomputed four-round prefix. Lean also proves the AVX2 SHA-256 compressor from eight input byte arrays through feed-forward. The SHA-NI pair proof covers all rounds and the byte-level input and output of both lanes for any packed chaining state. [SHA-NI proof](lean-hw/Slhdsa/Proofs/ShaNi.lean) On Arm, the paired SHA-512 theorem covers both full blocks, truncation to 24 or 32 bytes, and writing both outputs. [Paired Arm proof](lean-hw/Paired/Proof.lean) The complete dispatch and its callers have hardware, differential and interoperability tests. [Block theorems](lean-hw/Slhdsa/Proofs/Platform.lean) · [SHA-2 measurements](bench/headroom.md) · [SHAKE measurements](bench/merged.md)

For all six SHA-2 parameter sets on x86-64 Linux, Lean checks the named `slh_keygen_internal`, `slh_sign_internal`, and `slh_verify_internal` functions against FIPS 205 Algorithms 18–20. The public `slh_sign`, `slh_verify`, `sign`, `sign_deterministic`, and `verify` proofs include context rejection, the copy-based path for messages shorter than 1,024 bytes, and segmented HMAC and message hashing for longer inputs. The source gate extracts each fixed-size Rust entry, including the AVX-512 FORS dispatcher, then checks that its theorem applies to that translation. The proofs cover every CPU feature branch within the modeled instruction and external compression interfaces. [Named public API proofs](lean-hw/X86platform/Public.lean) · [Named internal API proofs](lean-hw/X86platform/Sets.lean) · [Fresh-source check](scripts/check-x86-core-proof.py)

The `platform-sha2` portable fallback has fresh Rust-to-Lean entry checks for all 60 named SHA-2 core operations on 32-bit i686 Linux, 64-bit big-endian PowerPC Linux and 64-bit RISC-V bare metal. The executable SHA-256 and SHA-512 compressors at this boundary have portable refinement proofs. [Portable SHA-2 public operations](lean-hw/Portableplatform/Public.lean) · [Target checks](scripts/check-portable-sha2-api-proof.py)

The extracted SHA-NI chain driver refines the portable chain specification for every digest width from 0 through 32 bytes. It accepts arbitrary 64-byte blocks and independent 32-bit start and end indices for each lane, including reversed or empty ranges. Lean checks state packing, every shared iteration, lanes with different remaining lengths, and the odd final block. The theorem compares the entire resulting block for every input and assumes valid range-slice lengths and the modeled SHA-NI, SSSE3 and SSE4.1 operations. [Chain driver theorem](lean-hw/Chainni/Top.lean) · [Two-lane step](lean-hw/Chainni/Pair.lean) · [Unequal-length chains](lean-hw/Chainni/Residual.lean)

The complete 16-lane AVX-512 SHA-256 chain driver refines the portable chain specification for 16-, 24- and 32-byte digests. Lean compares every byte of every output block for arbitrary initial state, batch length and unsigned 32-bit start and end indices. The proof covers empty and reversed ranges, mixed finishing times, short batches on both sides of the SHA-NI feature check, and the bytes after a truncated digest. It checks the unaligned counter and digest packing, masked reads and writes, cached rounds, inline compression, and termination. The theorem assumes the range arrays cover the input blocks and uses the documented instruction, memory and feature-detection models. [Complete driver theorem](lean-hw/Chainwide/Top.lean) · [In-place batches and dispatch](lean-hw/Chainwide/Driver.lean) · [Loop invariant](lean-hw/Chainwide/Loop.lean) · [Portable reference correspondence](lean-hw/Chainwide/Reference.lean) · [Complete output writer](lean-hw/Chainwrite/Top.lean) · [Three-host comparison](bench/merged.md#avx-512-chain-output-stores)



The eight-lane AVX2 driver and the complete x86 chain dispatcher refine the same portable recurrence for every digest width from 0 through 32 bytes. The proof covers all feature combinations, partial digest words, every group and its portable tail, arbitrary 32-bit ranges, and preservation of every output byte. For larger widths or short range slices, the dispatcher returns the exact result of the portable call, including its behavior on failure. The proof assumes the modeled instruction semantics, little-endian register layout, disjoint mutable slice borrows, and OS support for each enabled CPU feature. [AVX2 driver](lean-hw/Chainavx2/Top.lean) · [x86 dispatch and fallback](lean-hw/Chainx86/Top.lean)

Lean verifies the complete extracted AVX-512 WOTS endpoint-generation kernel for the 16-, 24- and 32-byte SHA-2 parameter sets. For each output keypair and chain, the destination contains the FIPS 205 Algorithm 6 PRF followed by all fifteen Algorithm 5 steps. The theorem covers empty and partial batches, crossing a keypair boundary, and preservation of each row’s 22-byte header and unused suffix. It assumes the supplied SHA-256 state represents the public seed, the rows have room for the endpoints, and the keypair and iterator counts fit their Rust integer types. [Endpoint theorem](lean-hw/Wots/Driver.lean)

Lean also verifies every output byte of the extracted AVX-512 WOTS recovery kernel for all three widths. For signature element `i` with digit `d`, the endpoint at byte 22 of row `i` equals FIPS 205 Algorithm 5 applied for `15 − d` steps starting at `d`, using chain address `i`. Every row retains its 22-byte header and unused suffix, and extra output rows are unchanged. The theorem assumes the SHA-256 public-seed state, at most 67 digits in the range 0–15, enough signature bytes and output rows, and the modeled x86 instruction and memory semantics. It covers empty inputs, digit-15 direct copies and all lane refill and retirement orders produced by the scheduler. [Recovery theorem](lean-hw/Wots/Recovery.lean) · [Loop invariant](lean-hw/Wots/RecoveryKernel.lean) · [Row accounting](lean-hw/Wots/RecoveryRows.lean)

The checked AVX-512 recovery wrapper returns the FIPS tweakable hash of those endpoints in signature order. The proof follows the actual endpoint slice, WOTS public-key address, padding, and SHA-256 or SHA-512 compression for all three widths. The public x86 entry point also computes the message digits and checksum and returns the FIPS 205 Algorithm 8 result for every CPU dispatch outcome, assuming a consistent public seed and enough signature bytes. [Algorithm 8 theorem](lean-hw/Wotsapi/Fallback.lean) · [Wrapper theorem](lean-hw/Wotswide/Recovery.lean) · [Endpoint hash equivalence](lean-hw/Wotswide/Hash.lean)

The checked x86 entry points call these verified WOTS kernels when the CPU and buffer dimensions satisfy their Rust assertions. Both reject calls when the AVX-512 feature test is false. The recovery entry requires exactly `2n + 3` digits for digest width `n`. [Checked entry-point theorems](lean-hw/Wotsx86/Proof.lean)

On x86-64 and AArch64 the extracted SHA-512 parent-block constructor writes the compressed address, both child nodes and the FIPS padding for a seeded 128-byte prefix. Given those padded blocks and the corresponding seed state, the x86 eight-lane and Arm two-lane routines return the FIPS 205 parent hash H and preserve the entries after the batch. [Parent-block theorem](lean-hw/Parentblock/Proof.lean) · [FIPS parent theorems](lean-hw/Parentblock/Fips.lean)

The FORS tree and authentication-path driver proofs cover both production SHA-512 batch widths for 24- and 32-byte nodes. On a supported CPU the drivers process every complete group. Each in-place tree output equals FIPS H on the corresponding original children. Each path output uses the signature sibling selected by the original index, in the correct order, and shifts that index by one bit. The proofs cover the untouched tail, the zero-work return when the feature is unavailable, and immediate return for every unsupported node width. They assume the FIPS public-seed state, valid buffer and address bounds, and the modeled CPU feature and instruction semantics. [Four driver theorems](lean-hw/Parentdriver/Proof.lean)

The extracted x86 BMI2 SHA-256 and SHA-512 kernels implement sequential FIPS 180-4 compression for any initial chaining state and any number of complete blocks, including zero. Lean verifies all byte loads, the sixteen-word rolling schedule, the 64 or 80 unrolled calls per block, and the addition of the working state back into the chaining state. Each call in these kernels links to a verified Rust definition. [Full kernel theorems](lean-hw/Streamscalar/Top.lean) · [Unrolled block proofs](lean-hw/Streamscalar/Block.lean) · [Round and schedule proof](lean-hw/Streamstep/Transition.lean)

The extracted AVX-512 XMSS subtree routine returns the FIPS 205 Algorithm 9 node for every valid index at heights 2, 3 and 4, the three heights selected by the dispatcher. Lean checks leaf generation and every in-place parent reduction, including tree height and index in each address. The proof covers all six SHA-2 parameter sets under the SIMD and SHA backend assumptions below. [Subtree theorem](lean-hw/Xmssroot/Top.lean) · [Tree reduction](lean-hw/Xmssroot/Tree.lean)

The x86 XMSS parent hash returns FIPS 205 H for all six SHA-2 parameter sets. The proof covers the two children, address encoding, padding, the selected single-block SHA implementation and truncation. [XMSS parent hash theorem](lean-hw/Treehash/Proof.lean)

The x86 remainder dispatch chooses either the verified BMI2 kernel or the external RustCrypto bulk routine. Lean checks both outcomes for each value of the BMI2 and SHA feature flags. The single-block SHA-256 and SHA-512 entries also select exactly 64 or 128 bytes at any valid offset. The locked RustCrypto SHA-NI and AVX2 implementations have source-extracted proofs of sequential FIPS compression for all block counts. The fallback uses the library’s verified scalar compressors. [SHA-NI source check](scripts/check-x86-sha-dispatch.py) · [AVX2 source check](scripts/check-rustcrypto-avx2.py) [Remainder and single-block proofs](lean-hw/X86remainder/Proof.lean)

Lean directly equates this library's scalar SHA-256 and SHA-512 compression results with the pinned RustCrypto SHA-NI and AVX2 implementations for every initial state and block sequence. A third theorem equates the Apple and Linux AArch64 sequential SHAKE256 results for every input and output length. See [the three equality theorems](lean-hw/PeerEquality/Primitives.lean).

Lean also checks 720 direct output equalities between the portable, Linux x86-64, Apple AArch64 and Linux AArch64 SDK implementations. Each of the twelve parameter sets contributes ten operations and each operation is checked for all six pairs of builds. The observations include both serialized keys, every signature byte, context rejection and the verification decision. Signing comparisons use identical seeds and randomizers. The SHA-2 statements use their message-length bounds and the context-bearing SHAKE statements require that the framed message fit in memory. [Pairwise SDK proof replay](scripts/check-cross-target-outputs.py) · [Output equality](lean-hw/PeerEquality/Outputs.lean)

The x86 SHAKE256 streaming proof covers every input and output length, with AVX-512 detection both enabled and disabled. The accelerated path loads all 17 little-endian rate words, preserves the eight capacity words, executes all 24 Keccak rounds across its two register layouts, and writes the state back before processing the remainder. The source replay checks the public streaming function and audits the axioms of both round layouts and the full digest theorem. [Streaming theorem](lean-hw/Kxouter/Top.lean) · [Source replay](scripts/check-platform-proof.sh)

The pinned independent RustCrypto SHA-2 suites implement the FIPS 205 component hash functions for all six SHA-2 parameter sets. The proof covers address compression, arbitrary multipart messages, HMAC, MGF1 and digest truncation for the verified Apple and Linux Arm compression paths, x86 SHA-NI SHA-256 and AVX2 SHA-512 paths, and software compression. Its source translation and machine-length assumptions are documented with the theorem. For the six SHAKE suites, fresh RustCrypto MIR establishes the component hash recipes for arbitrary multipart messages. The buffered provider theorem proves its streaming contract, and the target checks cover the release buffering paths, padding, byte views and Keccak dispatch. [SHA-2 proof and assumptions](lean-hw/RcSlhSha2/README.md) · [SHAKE source replay](scripts/check-peer-shake.py) · [Buffered SHAKE proof](lean-hw/Peerarmkeccak/Xof.lean) · [Streaming source checks](scripts/check-peer-streaming.py)

For all twelve SLH-DSA parameter sets, a [symbolic LLVM IR check](scripts/check-peer-key-extraction.py) follows each output byte of public-key extraction from a fixed-size private key, including RustCrypto's parsing and reserialization. It covers Apple AArch64, Linux AArch64 and Linux x86-64 release targets. This check trusts rustc, LLVM and its small byte-copy interpreter. A [Kani/CBMC comparison](scripts/check-peer-digest.py) also checks both crates’ actual digest splitting and FORS base conversion for every possible digest in each of the twelve parameter sets, including the 64-bit tree-index case. The twelve harnesses passed with Kani 0.68.0 and CBMC 6.11.0. A separate release LLVM check traces the signature parser and both encoding methods on all three targets. For each of the twelve parameter sets, Lean proves that the library and the pinned peer produce identical key bytes, context-bearing signature bytes and verification decisions. This includes arbitrary message partitions. A separate Lean check instantiates both the typed API and raw-byte comparisons with the extracted public entry points for Apple AArch64, Linux AArch64 and Linux x86-64. It checks 72 theorems across the three targets and twelve parameter sets. [Target-specific peer comparison](scripts/check-platform-peer.py). The caller proofs instantiate the independently checked hash, WOTS, FORS, XMSS and hypertree operations. Inputs must have the specified key, signature and randomizer sizes, matching RNG draws, and enough room to represent the framed message. The peer source translation, compiler, machine instructions and memory model remain in the trust boundary. [Public equivalence theorems](lean-hw/PeerEquality/Library.lean) · [Reproducible caller check](scripts/check-peer-callers.sh). [Signature encoding check](scripts/check-peer-signature-encoding.py) · [Caller theorems and assumptions](lean-hw/PeerEquality/Callers.md)

On AArch64 Linux and Apple Silicon, all six SHA-2 parameter sets satisfy their FIPS 205 statements for key generation, seeded internal key generation, public-key extraction, internal signing and verification, context signing and verification, deterministic signing, and the two `slh_sign` and `slh_verify` entry points. The checker recompiles each target and kernel-checks all 60 named theorems against its fresh translation, along with the segmented message-digest theorem. The proofs cover the two-lane FORS helpers and scalar tails. The streaming proof substitutes verified RustCrypto providers for both bulk SHA calls. On Linux the same substitution covers single-block SHA-512. [Public API extraction and proof check](scripts/check-arm-api-proof.py) · [FORS callers](lean-hw/Armplatform/ForsLoops.lean) · [Linux proof specialization](lean-hw/Armplatform/LinuxInternal.lean)

On x86-64 Linux, the platform build's six SHA-2 parameter sets have fresh Rust-to-Lean checks for seeded key generation, internal signing and internal verification, including FORS and hypertree processing. The compression contracts and instruction models below apply to these composed proofs. [Internal entry-point check](scripts/check-x86-core-proof.py)

For portable SHAKE, the proof checks eight generic public and internal operations and all 60 fixed-size SDK wrappers against complete Rust translations on i686 Linux, big-endian PowerPC64 Linux and bare-metal RISC-V. The permutation, aligned absorption and arbitrary-length output are included. On accelerated x86-64 Linux, a separate release-assembly check follows the eight-way AVX-512 Keccak permutation from its state loads through all 24 rounds and back to its stores. It assumes the stated instruction semantics, valid state memory and the System V stack convention. Its coverage is the permutation itself. The complete Apple Silicon and AArch64 Linux sequential SHAKE sponges now have separate refinement proofs for arbitrary input and output lengths. The target-specific SHAKE checks cover 60 SDK entries and 63 facade groups on each of Apple AArch64, Linux AArch64 and Linux x86-64. On Graviton the permutation proof covers all three states in the combined NEON and scalar path, under the modeled instruction semantics. [Public SHAKE proof replay](scripts/check-shake-platform-api.py) · [Graviton round proof](lean-hw/Kmixed/Top.lean). [Apple sponge theorem](lean-hw/Kappleouter/Top.lean) · [AArch64 Linux sponge theorem](lean-hw/Kspongel/Top.lean) [Portable API check](scripts/check-portable-shake.py) · [Release assembly check](scripts/check-keccak-assembly.sh) · [Permutation theorem](lean-hw/Keccakasm/Proof.lean)

On Apple Silicon, AArch64 Linux and x86-64 Linux, the RustCrypto facade has 63 checked SHA-2 statements per target covering deterministic and randomized signing, context handling, verification, key generation, raw and DER import, and multipart messages. They include the three known-answer-test entry points, arbitrary message partitions, and rejection of overlong contexts even when the caller supplies malformed randomness. With a valid context, malformed randomness triggers the assertion before signature generation. The signing adapter chooses between the contiguous and segmented implementations at 1,024 bytes. The PKCS#8 and SPKI output proofs cover all twelve parameter sets and track the exact bytes, result and error conversion at the external DER document constructors. [Facade source and axiom checks](scripts/check-platform-facade.py) · [Adapter verification](lean-hw/Platformadapter/Proof.lean) · [Public DER exports](lean-hw/Platformadapter/Exports.lean)

The x86 streaming proofs follow message grouping, SHA rounds, feed-forward, padding, and serialization. The current eight-block SHA-256 scheduler has a fresh source-extracted proof of every round word for every lane. The top-level theorems use eight-block drivers for both SHA-256 and SHA-512. The SHA-512 proof follows all 80 schedule words in each lane. [SHA-512 schedule correspondence](lean-hw/S512schedule/Proof.lean) · [Eight-block SHA-512 driver](lean-hw/S512driver/Top.lean). SHA-256 requires a block-aligned prior byte count and padding headroom. SHA-512 also requires length headroom. [Eight-block schedule theorem](lean-hw/S8table/Top.lean) · [Driver theorems](lean-hw/X86stream/Top.lean)

On AArch64 Linux and Apple Silicon, Lean verifies that the extracted SHA-256 and SHA-512 streaming drivers split the message into blocks, pad the tail using the prior byte count, and serialize the final state as specified by FIPS 180-4. The SHA-256 theorem requires a block-aligned prior count and room for 72 additional bytes under both the platform and SHA-256 length bounds. The SHA-512 theorem reserves 144 bytes within the platform length bound. A separate Linux theorem covers the SHA-512 single-block entry at any offset with 128 bytes available. These proofs model Rust slice operations. Substituting the verified RustCrypto provider into the extracted driver preserves the complete result, including the chaining state passed between the message and padding blocks. The release-code gate also checks the Linux feature probe and fallback. [Provider substitution theorems](lean-hw/Armstream/Providers.lean) · [Release-code replay](scripts/check-rustcrypto-arm-code.sh). [Driver and single-block theorems](lean-hw/Armstream/Proof.lean) · [External contracts](lean-hw/Armstream/FunsExternal.lean)

The shared AVX-512 SHA-256 digest writer used by FORS leaves, FORS parents and WOTS key digests serializes every active lane of an arbitrary vector state. Lean checks byte order, the 32-bit and 64-bit unpacks within each 128-bit lane, the register reinterpretation under the little-endian layout, bounds on each slice write, and truncation for 16-, 24- and 32-byte outputs. The theorem holds for every output slice length from zero through sixteen. [Digest writer theorem](lean-hw/Store256/Proof.lean) · [Register transpose theorem](lean-hw/Store256/Transpose.lean)

For SHA2-128s and SHA2-128f, the AVX-512 WOTS public-key digest theorem follows the production entry point for one through sixteen keys. It checks the mask and signed gather offsets, all ten 64-byte blocks, the first four SHA rounds in each block, the remaining rounds, and every returned digest byte. With the FIPS public-seed state and correctly padded inputs, each 16-byte result equals the FIPS 205 tweakable hash T. The theorem assumes AVX-512 availability and the modeled x86 instruction and memory semantics. [FIPS 205 theorem](lean-hw/Digest256/Fips.lean) · [Digest theorem](lean-hw/Digest256/Top.lean)

For all six SHA-2 parameter sets, the extracted AVX-512 FORS leaf entry point returns exactly FIPS 205 Algorithm 15 at height zero. Lean checks both padded address-and-message blocks, the shared SHA-256 rounds, both complete compressions, digest truncation, and output ordering for arbitrary batches, including empty slices and partial final groups. The theorem assumes a correctly derived public-seed state, AVX-512 availability, nonoverflowing leaf indices and the modeled instruction semantics. [FIPS FORS leaf theorem](lean-hw/Leaf256/Fips.lean) · [Production entry point](lean-hw/Leaf256/Top.lean)

For the SHA-256 FORS parent entry point, Lean checks all 16-byte parent outputs against FIPS 205 `H` of the indexed address and the original left and right children. It covers partial batches, masked reads, unaligned word packing, shared rounds, compression, truncation and in-place writes. The output preserves the slice length and the entire suffix after the last parent. The active path assumes AVX-512 availability, the public-seed state, enough input children and nonoverflowing indices and byte offsets. Unsupported widths and counts below two return zero and preserve the buffer before querying CPU features. [Production entry and early returns](lean-hw/Parent256/Top.lean) · [In-place batch loop](lean-hw/Parent256/Driver.lean) · [FIPS batch theorem](lean-hw/Parent256/Batch.lean)


The AVX-512 SHA-512 WOTS public-key digest theorem covers batches of one through eight already-padded inputs. Each active lane consumes its own 1,280 or 2,304 bytes and returns the first 24 or 32 bytes of the corresponding SHA-512 compression chain. The proof checks effective addresses against the allocation bounds and assumes the x86 little-endian layout, the modeled SIMD instructions, and an affirmative CPU/OS feature check. Given the specified public-seed state and padded address and endpoint bytes, the returned bytes equal the FIPS 205 tweakable hash T. The extracted XMSS message initializer writes the WOTS key address, delimiter and big-endian length. Lean checks that inserting the endpoint bytes at offset 22 then produces the FIPS padding at all three parameter sizes. The extracted x86 XMSS leaf generator composes this initializer with the WOTS endpoint computation, insertion and SHA-256 or SHA-512 digest. For every supported width, it returns the FIPS WOTS public key for each consecutive leaf, including a partially occupied final group. For a batch contained in any FIPS parameter set’s XMSS tree, Lean also proves that every prepared lane fits the 32-bit address field and each returned value is the corresponding height-zero Algorithm 9 node. The theorem assumes AVX-512 availability and a valid public-seed state. [Batched leaf theorem](lean-hw/Xmsskeys/Top.lean) · [Endpoint insertion](lean-hw/Wots/Payload.lean). [Padding theorem](lean-hw/Keypadding/Proof.lean) [FIPS 205 theorem](lean-hw/Gather512/Fips.lean) [Digest theorem](lean-hw/Gather512/Top.lean) · [Gather memory model](lean-hw/Gather512/FunsExternal.lean)
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
- **Default and `hw-sha2` proof coverage** (surveyed 2026-11-22). For those two builds, in
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
([security/README.md](security/README.md)). The platform proof compares extractions for the Rust targets
`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, and `aarch64-apple-darwin`. Then:

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

[The six-set range theorems](security/ME2E/RomBounds.lean) bound strong and existential forgery at the pure
byte interface by `qh / 2^(8n−2)` for `2^32 ≤ qh ≤ 2^64` and `qs ≤ 2^64` in this
three-oracle model. For example, at `qh = 2^40` the bounds are `2^-86`, `2^-150`, and
`2^-214` at 16, 24, and 32 bytes respectively, for both tree shapes.

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
nothing about the real compression function. These numerical examples apply to 128s.
See [the tightening work](security/status/TIGHT.md).

[The secret-address PRF bound](security/MIdeal/SkPrf.lean) extends to all six sets.
For `q` classical compression queries and `qo` PRF requests the advantage is at most
`q / 2^(8n) + (q + qo)² / 2^256`. The proof identifies the two SHA-256 compression
calls, including the address, secret and padding bytes, at each width.
[Both FORS-leaf games](security/MIdeal/Fors.lean) have bounds for every set,
and [the SHA-512 message PRF](security/MIdeal/MsgPrf512.lean) has a two-sided
bound at both wide node sizes, for any fixed public SHA-256 table.
For SHA2-128f the [classical pure-byte SUF-CMA and EUF-CMA theorems](security/MIdeal/Sha2_128f.lean)
combine all these terms under explicit SHA-256 query, signing, and message bounds and the condition
`4 * Fors128f.budget q qs L ≤ 2^128`. The adversary also has access to the independent SHA-512 table.
For 128f, Lean also checks the [HMAC-SHA-256 advantage](security/MIdeal/MsgPrf128f.lean),
[fixed-arity and WOTS+ target-collision bounds](security/MIdeal/Hash128f.lean),
and [WOTS+ preimage and undetectability bounds](security/MIdeal/Wots128f.lean)
with the 128f reduction’s target counts. The [three WOTS bounds for the byte forger](security/MIdeal/Wots128fBound.lean) include both phases and derive their query budgets from the adversary’s compression and signing queries. The [message-hash layouts](security/MIdeal/Hmsg.lean)
account for both MGF1 counters in 128f and the SHA-512 path in the four wider sets.
For those four sets, the [message-hash security bound](security/MIdeal/Itsr512.lean)
counts compression queries, target queries, and the maximum message length.
The [128f message-hash security bound](security/MIdeal/Itsr128fBound.lean) covers the
34-byte digest from both MGF1 counters. With at most `q` compression queries,
`qs` target queries, and messages of at most `L` bytes, it bounds ITSR success
by `reuseSum 66 6 33 Q + Q²/2^256`, where
`Q = q + (qs + 1)(⌊(L+56)/64⌋ + 4)`.
The [wide-set target-collision bound](security/MIdeal/ArityTcr512.lean) covers
all fixed arities other than one, including H, T_len and T_k. It charges both
phases and verification, and allows the adversary to know the SHA-256 table.
For the same four sets, the [arity-one and WOTS+ target-collision proofs](security/MIdeal/SingletonTcr.lean)
charge SHA-256 queries and allow the adversary to know the SHA-512 table.

### Quantum adversaries ([quantum/](quantum), see `quantum/STATUS.md`)

[The quantum standard-model reduction](quantum/Integration/SlhDsaRustQuantum.lean)
pairs the Rust API correspondence for every SHA-2 set with EUF-CMA and SUF-CMA
reductions for the same pure byte scheme. The signer accepts classical queries. The right-hand
sides are quantum hash-game advantages for the actual SHA-2 functions.

[The complete quantum random-oracle proof](quantum/Integration/SlhDsaSetClosed.lean)
covers all six sets when the four hash components are independent random functions
on capped inputs. At `2^40` quantum oracle queries and `2^20` classical signing
queries the checked forgery bounds for 128s, 128f, 192s, 192f, 256s and 256f are
respectively `2^-22`, `2^-21`, `2^-81`, `2^-85`, `2^-147` and `2^-149`.
See [the numerical certificate](quantum/Integration/SlhDsaSetNumeric.lean).

[The shared-compression experiment](quantum/Integration/SlhDsaCompressionQuantum.lean)
gives the forger one quantum port for the two compression tables. The honest hash components
use those same tables, and [substituting the real tables](security/MIdeal/MixedTables.lean)
recovers the FIPS functions for every set. The theorem bounds forgery by hash-game advantages
averaged over the tables. [The secret-address PRF step](quantum/Integration/SlhDsaCompressionPrfBudget.lean)
contributes at most `8 B² / 2^(8n)` for all six sets. Its compression-query budget
`B` includes the forger, key generation, signing, and verification. The [FORS target-collision](quantum/Integration/SlhDsaCompressionFors.lean)
and [decisional second-preimage](quantum/Integration/SlhDsaCompressionDspr.lean) theorems
cover all six sets with a classical selection phase and a quantum second phase
making at most `q` compression queries. The [FORS reduction](quantum/Integration/SlhDsaCompressionForsReduction.lean)
supplies that budget from the byte-level forger's compression-query count, signing-query count,
and encoded-message limit. The [WOTS+ reduction](quantum/Integration/SlhDsaCompressionWotsReduction.lean)
also supplies explicit budgets for preimage resistance, chain target collisions, and
undetectability on SHA2-192s, 192f, 256s, and 256f. For these four sets, Lean now proves
[closed SUF-CMA and EUF-CMA bounds](quantum/Integration/SlhDsaCompressionWideMixed.lean)
in the shared ideal-compression model. The proof charges honest construction classically and
allows coherent access to the same tables afterward. The [class collision estimate](quantum/Integration/SlhDsaCompressionMixedBudget.lean)
is at most 1/256 per nonsingleton arity at a 1 KiB message limit, `2^40` public queries and
`2^20` signing queries. The message-hash estimate still reaches one at `2^40` public queries,
so the overall theorem gives no quantitative forgery guarantee at that benchmark.

With at most one signing query, the proof uses all decoded FORS coordinates. For encoded messages of at most 64 KiB and up to `2^40` public queries, the complete forgery bounds are `2^-19` (192s), `2^-22` (192f), `2^-78` (256s), and `2^-79` (256f). [Signature theorems](quantum/Integration/SlhDsaCompressionSingleTarget.lean) · [Numerical certificate](quantum/Integration/SlhDsaCompressionSingleBenchmark.lean)

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
but transferring this numerical bound to concrete SHA-2 remains open. The
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
