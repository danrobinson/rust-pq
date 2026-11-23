# SHAKE and linked binary verification

## The six SHAKE sets

The proofs apply to 128s, 128f, 192s, 192f, 256s and 256f. Three properties answer different questions about the signer.

| Property | What the proof establishes | Boundary |
|---|---|---|
| Functional correctness | The extracted implementation produces the FIPS 205 keys, signatures and verification verdicts, including the optimized hypertree signing logic. | Rust translation, the formal specification and the stated platform primitive and input assumptions. [Public API proofs](../lean/Facade.lean) |
| Classical unforgeability | A successful forger against the internal or pure byte-string scheme yields adversaries against named component properties. Lean specializes ordinary and strong chosen-message forgery bounds to the six executable SHAKE components and proves the scheme-to-game correspondences. | The remaining advantage terms are cryptographic assumptions. Their values for SHAKE256 and quantum-query security require separate arguments. [Concrete components](../security/MLink/ShakePrimitives.lean) · [Transfer](../security/ME2E/Shake.lean) · [Bounds](../security/MReduction/Shake.lean) |
| Source leakage | Key generation has an identical trace across seeds. A simulator given the public key, message, context and published signature reproduces the successful hedged or deterministic signing trace. The proofs cover arbitrary-length streaming SHAKE, the fixed-size key APIs and DER operations. | Default and `hw-sha2` extracted configurations. The events include branches, indices and copy lengths. DER decoding allows disclosure of public header mismatches. The separately compiled compatibility facade and accelerated `platform-sha2` signer need their own leakage proofs. [Trace statements and model](../lean/CT_STATUS.md) |

## Evidence from linked executables

The crate distributes Rust code. Downstream linking selects and can transform the final machine code. For this audit we used two consumers built in release mode with `platform-sha2` from library revision `74b1b3e`. Each checker reads the final file, identifies the code and constants, checks them and reports the complete file's digest. A new deployment needs a replay against its own artifact.

| Executable and routines | Result | How it was established |
|---|---|---|
| Apple arm64 ACVP executable, two-state SHA3 Keccak-f and single-state adapter | On arbitrary inputs each 25-word state gets the FIPS 202 permutation. The adapter duplicates the input, makes one direct call and writes back the complete result. | The checker binds the 464-byte leaf, the 192-byte round table and the 380-byte adapter. Lean executes the round instruction words for arbitrary scratch registers and proves equality for all 24 rounds. A restricted Python symbolic executor checks the outer loads, loop, ABI, stack and adapter. [Exact round witness](../lean/Spec/AppleKeccakWitness.lean) · [Instruction semantics](../lean/Spec/ArmSha3Binary.lean) · [Artifact checker](../scripts/apple-binary/check.py) |
| Same Apple executable, SHA-256 and SHA-512 hardware compression | Both linked routines implement FIPS 180-4 compression, for arbitrary initial chaining states and valid sequences of complete blocks. | The checker follows the linked constant addresses, translates the 556-byte and 2,344-byte functions to register programs, and checks them against the Apple programs used in the multi-block proofs. [SHA-256 proof](../lean-hw/Rcarmcode/Proof.lean) · [SHA-512 proof](../lean-hw/Rcarmcode/Proof512.lean) · [Link check](../scripts/apple-binary/sha2.py) |
| Same Apple executable, SHAKE hypertree signer | Every normally executing path makes exactly one direct XMSS signing call per layer, recovers a root after every nonfinal layer and skips recovery after the final layer. This covers all six public depths/width combinations. | An exhaustive control-flow checker follows the actual branches and call targets in the three linked functions, explores both outcomes of unknown branches and checks termination of the resulting finite graphs. The check assumes valid parameters and normally returning ABI-conforming callees. It concerns call order and count. [Checker](../scripts/apple-binary/hypertree.py) |
| Linux x86-64 benchmark executable, eight-state AVX-512 Keccak-f | Each of eight independent arbitrary states gets the FIPS 202 result. With fixed buffer, stack, code and return addresses, every input produces the same architectural memory-access and control-transfer trace. | Lean checks the entire 1,158-byte leaf, including its loop back edge, the linked table and the return. The checked-in witness contains the bytes. [Theorems and exact witness](../lean-hw/Keccakasm/ReleaseWitness.lean) · [Assumptions and replay](../lean-hw/Keccakasm/Linked.md) |

The machine-code results assume that the loader preserves the measured bytes, that the CPU implements the modeled ISA and enabled features, and that pointers, stack, alignment and non-aliasing satisfy the function's ABI. The Apple gate also trusts the Mach-O reader, LLVM disassembly for the SHA-2 and hypertree checks, and the restricted Python checkers. The mathematical certificates are checked by Lean. Whole-program dispatch, other machine-code routines, allocator/runtime behavior, speculation, physical timing and fault resistance remain open.

## Replaying the checks

On Apple Silicon, with the repository's Lean and Rust dependencies and the Apple command-line tools installed, run from the repository root:

```sh
python3 scripts/apple-binary/check.py --self-test --certificate /tmp/LinkedArm.lean
```

The checked-in round witness can also be replayed on any supported Lean host with `cd lean && lake build Spec.AppleKeccakWitness`. The Apple checker builds the locked release ACVP consumer by default. To check a different unstripped thin Apple arm64 executable with the supported routines and instruction schedules, pass its path as the positional argument. Six one-bit mutation controls change a SHA3 rotation, the Keccak loop back edge, the wrapper's direct call, a round constant, a SHA-256 round instruction and the hypertree's final recovery guard.

For an x86-64 Linux release consumer, including a stripped ELF with suitable unwind metadata:

```sh
uv run --script scripts/test-keccak-elf.py /path/to/consumer
```

The x86 checker rejects four independent byte mutations. The recorded Apple file SHA-256 is `ab672dc82d293ec220beb29f475bedda4614d59c76636cd16edef18705e1ac0a`. The Linux stripped file SHA-256 is `d0684e30aa7e85cc8c7229cd5da885ae7f9eb6d9c857d01363b90f993c330c69`. Both were built with Rust 1.100.0. As a separate runtime check, the measured Apple executable passed all 53 ACVP test groups, and the matching release RustCrypto interoperability target passed all 36 test groups.
