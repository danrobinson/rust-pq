# Linked Apple public SHA-2 verification

The Lean replay covers both public pure-verification exports, `verify` and `slh_verify`, on all six SHA-2 sets in the measured Apple arm64 release ACVP executable. Its SHA-256 is `ab672dc82d293ec220beb29f475bedda4614d59c76636cd16edef18705e1ac0a`. Each replay starts at the linked symbol and follows its control flow through the return to the caller.

| Input | Checked path |
| --- | --- |
| Context exceeds 255 bytes | Returns false before calling framing, hashing or signature verification. |
| Valid context, message at most 1023 bytes | Checks the framing call, its arguments, the returned vector passed to the internal verifier, the internal verifier's target and arguments, deallocation, and the forwarded Boolean. The internal verifier rejects malformed signatures. |
| Valid context, message at least 1024 bytes, wrong signature length | Enters the linked segmented verifier, computes and compares the required size from the linked parameters, then returns false before reading signature or public-key data. |
| Valid context, message at least 1024 bytes, correct signature length | Checks the segmented digest call with the signature randomizer, both public key components and the distinct context/message pointers and lengths. It then runs the seed, FORS, hypertree and root-comparison control flow through cleanup and return. |

For each exported symbol, the `*_eq` theorem relates the modeled result to `Spec.slhVerify` for every correctly sized signature and public key satisfying the local digest, FORS and XMSS output contracts. The short path instantiates the checked pure-framing model for all eight allocation branch choices. The segmented path represents the digest input logically as the mode byte, one-byte context length, context, and message. Its digest is a local callee contract in this Lean replay. The actual calling convention and parameter order are checked at the call. The `*_malformed` and `*_contextRejected` theorems require no cryptographic result hypotheses.

The narrow segmented routine's final comparison gets the two halves of the public root from separate stack locations. A six-instruction bit-vector lemma proves that it compares all sixteen bytes. The wider sets reuse the earlier bytewise root equivalence. The verifier checks return-PC, stack and callee-saved-register restoration, with the same restricted AArch64 instruction model, valid ABI buffers, and successful allocation/deallocation assumptions as the internal proof. The proof covers this executable's functional return and excludes operating-system allocation failure and microarchitectural timing.

To reproduce the extraction and replay, supply the measured executable:

```sh
python3 scripts/apple-binary/sha2_public_verify_witness.py "$EXE" | cmp - lean/Spec/AppleSha2PublicVerifyWitness.lean
(cd lean && lake build Spec.AppleSha2PublicVerifyWitness)
```

Six negative controls mutate the two public length thresholds, the short verifier's signature pointer, the segmented digest's context length, one SHA seed instruction, and one register in the final root comparison. The kernel replays each altered image and checks that its expected success certificate fails. [Public verifier model](../lean/Spec/ArmSha2PublicVerify.lean) · [Linked witnesses](../lean/Spec/AppleSha2PublicVerifyWitness.lean) · [Internal verifier](Linked%20Apple%20internal%20SHA-2%20verification.md)
