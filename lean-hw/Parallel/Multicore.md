# Proof coverage of the persistent worker implementation

| Component | Checked property | Implementation boundary |
|---|---|---|
| Apple eight-lane Keccak | For arbitrary input words and round constant, Lean checks all 25 output words of the scalar, SHA3 and NEON round bodies against FIPS 202. A symbolic replay checks the round constants, coordinate ordering, loads and stores for each active lane count from zero through eight. | The replay lifts the Rust bodies under lane-wise intrinsic semantics. The compiler, emitted instructions and CPU feature detection are trusted here. [Replay](../../scripts/check-apple-hybrid.py) |
| Split XMSS and FORS subtrees | For any number of levels and any valid root index, merging the specified consecutive subtrees gives FIPS Algorithm 9 or 15. A Rust replay checks the reducer's child indices, height, hash input order and in-place writes for all supported heights. | The child nodes satisfy their primitive contracts. Absolute indices must fit in the Rust index type. [Theorems](SplitTree.lean) · [Source check](../../scripts/check-split-tree.py) |
| Parallel key generation | Every drained and joined ticket schedule computes the specified XMSS public root. The source check covers the two split policies, the ticket counter, slot writes, parent domain and final reduction. | Assumes normally returning workers, atomic ticket allocation, publication and join semantics. [Key generation theorem](SplitTree.lean) |
| Batched verification | In the worker model, per-item results equal the individual verdicts in input order. The short-circuit accumulator returns true exactly when every item verifies. | This theorem models claims, completed checks, rejection and joining. The OS worker pool and individual verification kernels require separate implementation proofs. [Batch theorems](Batch.lean) |
| Parallel WOTS signing | Independent WOTS jobs using the preceding layer's XMSS root produce the FIPS hypertree signature in layer order for every valid parameter set. | The theorem assumes the specified FORS root, authentication nodes and WOTS operations. A complete source binding of the new job planner, barrier and assembly is open. [Hypertree theorem](Fused.lean) |
| HashSLH-DSA framing | For the four pre-hash choices, the formatter rejects invalid lengths and otherwise emits the exact domain byte, one-byte context length, context, DER OID and supplied digest. | Aeneas re-extracts the actual formatter on Apple AArch64, Linux AArch64 and Linux x86-64. Correct computation of the supplied digest and the cached signer are separate obligations. [Theorem](../Prehash/Proof.lean) · [Replay](../../scripts/check-prehash-framing.py) |

The scoped-worker signing theorem describes a different scheduler. Its replay does not certify the persistent worker implementation. The ARM SHA-2 kernels, fused SHAKE tree routines, cache, Metal shaders and Objective-C bridge still require end-to-end implementation proofs for these paths.

Run from the repository root with the proof toolchains installed.

```sh
python3 scripts/check-apple-hybrid.py
python3 scripts/check-split-tree.py
python3 scripts/check-prehash-framing.py
(cd lean-hw && lake build Parallel.Batch Parallel.Fused)
```
