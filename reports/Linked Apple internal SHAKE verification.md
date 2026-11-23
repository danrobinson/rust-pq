# Linked Apple internal SHAKE verification

For the Apple arm64 ACVP executable with SHA-256 `ab672dc82d293ec220beb29f475bedda4614d59c76636cd16edef18705e1ac0a`, Lean constructs a `VerifyTrace` for all six public `slh_verify_internal` entries. On a correctly sized signature, each row's `*_eq` theorem identifies the Boolean returned by the restricted machine semantics with `Spec.slhVerifyInternal`, given local contracts for the calls made during the replay. Both acceptance and rejection are covered. [Interpreter and trace constructor](../lean/Spec/ArmVerifyBody.lean) · [Six artifact witnesses](../lean/Spec/AppleVerifyBodyWitness.lean)

| SHAKE profile | Signature bytes | XMSS recovery calls | Final comparison |
|---|---:|---:|---:|
| 128s | 7,856 | 7 | 16 bytes |
| 128f | 17,088 | 22 | 16 bytes |
| 192s | 16,224 | 7 | 24 bytes |
| 192f | 35,664 | 22 | 24 bytes |
| 256s | 29,792 | 8 | 32 bytes |
| 256f | 49,856 | 17 | 32 bytes |

The malformed-length proof starts at the wrapper, reads the linked parameter record, computes the required signature size and follows the unequal branch through register restoration and return. Every representable different length returns false before a hash call. The correct-length branch copies the randomizer, public seed and public root to the inputs of the actual `H_msg` call and forwards the message pointer and length. [Length, ABI and buffer semantics](../lean/Spec/ArmVerifyLength.lean) · [Per-profile length certificates](../lean/Spec/AppleVerifyLengthWitness.lean)

After `H_msg`, the replay checks digest offsets and bounds, both native byte-accumulation loops and their masking operations, the `base_2b` inputs, the FORS signature slice and address, and the FORS result passed to the first layer. It checks every layer's index, address, input root, seed, signature slice and output buffer, then follows the machine's update of the tree and leaf coordinates. For 192- and 256-bit profiles it fetches instructions from the separately linked `ht_verify` functions. The final comparison checks all root bytes and the replay follows the resulting W0 through deallocation, the epilogue and RET. [Digest offset interpretation](../lean/Spec/ArmSignCoordinates.lean) · [Little-endian root comparison semantics](../lean/Spec/ArmRootComparison.lean)

The theorem assumes local contracts for `H_msg`, `base_2b`, FORS recovery and each XMSS recovery call on the arguments checked by the interpreter. The XMSS contract is a structured WOTS and authentication-path witness. The return comparison and whole verification result are conclusions. The runtime model uses disjoint modeled memory regions, initialized correctly sized keys and signatures, positive capacities for nonempty vectors, normal deallocation and AArch64 calling conventions. The theorem covers this linked executable's internal verification entries. Propagating all lower-level native routine proofs through a single ISA semantics, public context framing, allocation failures, arbitrary memory placements and other executables are separate obligations. [Native SMT verification driver](../scripts/linked-signer/verify.py)

Run `lake build Spec.AppleVerifyLengthWitness Spec.AppleVerifyBodyWitness` from `lean/` to replay the checked-in certificates. The six length-gate and hash-argument mutation proofs and six post-hash mutation proofs alter machine words, including the digest assembly, FORS argument, layer signature selection, and final comparisons. Re-extract the two Lean witness files from an executable with the two Python generators. [Length witness generator](../scripts/apple-binary/verify_length_witness.py) · [Verification body generator](../scripts/apple-binary/verify_body_witness.py)
