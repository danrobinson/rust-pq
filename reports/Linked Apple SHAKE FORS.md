# Linked Apple SHAKE FORS

For all six standard SHAKE parameter sets, the linked Apple arm64 FORS signer writes the FIPS 205 Algorithm 16 signature blocks in order. Recovery takes arbitrary signature bytes of the required length and reconstructs the Algorithm 17 public key. The input selections are arbitrary valid base-`2^a` digits. The checks include the recursive node equations from Algorithm 15 and the hash inputs for secret generation. The measured file is the release ACVP consumer, SHA-256 `ab672dc82d293ec220beb29f475bedda4614d59c76636cd16edef18705e1ac0a`. [Algorithm specifications](../lean/Spec/SlhDsa.lean) · [Binary checker](../scripts/linked-signer/fors.py)

| SHAKE sets | Node width | Sign entry / extent | Recover entry / extent | Recursive node entry / extent |
|---|---:|---|---|---|
| 128s and 128f | 16 bytes | `0x10007e1e8` / 916 B | `0x10007f23c` / 1,240 B | `0x10007ed4c` / 412 B |
| 192s and 192f | 24 bytes | `0x10007e57c` / 976 B | `0x10007f714` / 1,376 B | `0x10007eee8` / 388 B |
| 256s and 256f | 32 bytes | `0x10007e94c` / 1,024 B | `0x10007fc74` / 1,472 B | `0x10007f06c` / 464 B |

**Selection, addresses and layout.** The checker reads the parameter row from the measured image. It tracks the arbitrary layer, tree and keypair fields, compares the full 32-byte big-endian FIPS address at each hash, and uses independent symbolic variables for every selected digit. For tree `i`, the secret has global index `i * 2^a + digit[i]`. At level `j`, the sibling index is `i * 2^(a-j) + ((digit[i] >> j) XOR 1)`. The leaf secret occupies the first block in a row of `a+1` blocks, followed by the sibling at each height. The proof compares every output byte, the allocation size, pointer and returned vector metadata. It includes both odd and even tree counts, including duplication in the unused lane of the final odd batch. Recovery chooses the left or right sibling from the appropriate digit bit. The root hash consumes one root for each active tree in original order.

**Recursive nodes.** The zero-height case checks the `FORS_PRF` and leaf `FORS_TREE` domains. The positive-height case checks both child indices, the height decrease, the two-lane packing, and the parent hash in its tree domain. The recursive call is summarized with a fresh independent symbolic output for each lane after those conditions are checked. The bound `index < 2^20 / 2^height` covers all six parameter rows; each child satisfies it at the decreased height. These equations support induction without running exponentially many equivalent subtrees.

**Hashing.** The checker executes the linked batch headers, the 24-byte pair helper and the inlined permutations’ input/output adapters. It compares every byte of the 400-byte interleaved pre-permutation state with two independently formed 200-byte padded states. For the root hash it also executes the actual scalar sponge initialization, absorption and finalization. Each stream input at this call site is an 8-byte-aligned length of 16, 24 or 32 bytes. The check follows transitions across the 136-byte rate boundary, validates the domain and final padding bits, and compares the output bytes after the last Keccak call. This caller takes only the aligned short-input paths of `Sponge::absorb`. [Padding and absorption lemmas](../lean-hw/Shakebatch/LinkedFors.lean) · [Linked permutation witness](../lean/Spec/AppleKeccakWitness.lean)

**Verification boundary.** The outer result is a symbolic execution and SMT comparison against the FORS equations. Its trusted software includes the Mach-O reader, VEX AArch64 lifter, angr, three short VEX bitvector operation models, claripy/Z3 and the Python checker. Lean checks the matching permutation witness and its correspondence with short SHAKE and aligned word absorption. The checker validates the measured leaf schedule, constants and single-state wrapper before using their permutation contracts. Runtime assumptions are successful allocation, the standard `memcpy` and `memset_pattern16` contracts, the compiler allocation shim, normal ABI returns and enough stack. Inputs and writable outputs occupy the indicated disjoint modeled regions at representative addresses. The solver ranges over their contents. Panic/OOM paths, asynchronous faults, physical timing and arbitrary relocated caller memory layouts require separate treatment. [VEX operation models](../scripts/linked-signer/arm_vector_ir.py)

From a proof checkout with the Lean dependencies installed, replay the complete matrix and the four altered binaries with:

```sh
uv run --script scripts/linked-signer/fors.py /path/to/acvp
uv run --script scripts/linked-signer/fors.py /path/to/acvp --mutations
```

The controls change the secret-generation address type, the sibling calculation, the final roots address type, and the ordering of two children. Each must fail at its corresponding data-flow comparison.
