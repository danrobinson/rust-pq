# Linked Apple internal SHA-2 verification

The Lean witness covers all six exported `sha2_*::slh_verify_internal` functions in the measured Apple arm64 release ACVP executable, SHA-256 `ab672dc82d293ec220beb29f475bedda4614d59c76636cd16edef18705e1ac0a`. The replay starts at the public ABI wrapper. It computes the signature size from the linked parameter bytes, follows the conditional branch and validates the return to the original caller.

* Every representable incorrect signature length returns false before reading message, signature or public-key bytes.
* At the correct length, the replay checks the three actual input buffers to H_msg, the message arguments, the offsets and masks used to derive the tree and leaf, and the digest prefix and signature supplied to SHA-2 FORS recovery.
* Each native XMSS call receives the correct layer slice, the preceding root, the seed context and the layer, tree and leaf coordinates. The 128-bit routine contains the hypertree loop directly. Both wider routines call a separately linked hypertree body that the replay follows to its return.
* A bit-vector/byte-memory theorem shows that the final comparison reads and compares all 16, 24 or 32 bytes of the recovered and public roots. The verifier preserves the resulting Boolean across digest deallocation, restores the modeled callee-saved state and returns through the original ABI.

The six `*_eq` theorems say that the modeled return is `Spec.slhVerifyInternal` for the same inputs. Each takes the public-size conditions and the local H_msg, FORS and individual XMSS result contracts through `ArmVerifyBody.Callees`. The digest decoder runs inside SHA-2 FORS. It receives the exact digest prefix there. The reference call constructor can supply these records for arbitrary correctly sized inputs.

The 128-bit inline seed prefix uses the checked SHA-256 key-generation circuit with relocation, stack offset and exit-branch differences validated against the linked words and constants. The wider variants check the call to their linked seed-context routine, its input seed and use of the returned context. The proofs use the restricted ARM decoder, valid Rust ABI regions and successful callee and deallocation contracts. They cover functional return values for the internal-verification entry points. Public context framing, machine timing and other binaries have separate evidence.

To reproduce the certificate from a supplied image, run the two extractions and compare their output to the committed Lean files. Build the second module to replay both proofs in Lean's kernel.

```sh
python3 scripts/apple-binary/sha2_verify_witness.py "$EXE" | cmp - lean/Spec/AppleSha2VerifyLengthWitness.lean
python3 scripts/apple-binary/sha2_verify_witness.py "$EXE" --body | cmp - lean/Spec/AppleSha2VerifyWitness.lean
(cd lean && lake build Spec.AppleSha2VerifyWitness)
```

The negative controls alter the length branch, rejection Boolean, SHA seed circuit, FORS and layer input slices, a wide seed call, and both narrow and wide root comparisons. [Restricted verifier](../lean/Spec/ArmSha2Verify.lean) · [Length and H_msg witness](../lean/Spec/AppleSha2VerifyLengthWitness.lean) · [Return witness](../lean/Spec/AppleSha2VerifyWitness.lean) · [Reference calls](../lean/Spec/ArmReferenceCalls.lean)
