# Functional correctness of the parallel SLH-DSA paths

The source replay on this page targets the scoped-worker signer. See [persistent-worker proof coverage](Multicore.md) for the implementation on this branch.

The signing theorem equates the signature byte string with the repository's FIPS 205 specification for every message, key and signing randomizer. It covers SHA-2 and SHAKE and every completion order admitted by the worker model. The subtree theorem equates the eight-leaf construction with the height-three XMSS node for arbitrary seeds, address and valid subtree index. The x86 permutation theorem covers both values of the AVX-512 feature test.

| Path | What is checked |
|---|---|
| Parallel signing | A Lean transition system tracks the fetch counter, outstanding tickets and published nodes. Starting at zero, claiming one ticket at a time and joining after the caller drains the queue produces each required node exactly once. Lean proves that indexing those nodes in signature order gives the FIPS authentication paths, that the inter-layer WOTS roots agree, and that omitting the last unused root preserves every signature byte. The public framing theorem includes context rejection. [Signing theorems](Signing.lean) |
| Eight SHAKE leaves | Lean projects the batched WOTS chains onto individual keys, checks endpoint order, and proves that ascending in-place writes at each tree level preserve both children needed by later parents. The result is FIPS 205 Algorithm 9 at height three. [Subtree theorems](Subtree.lean) |
| Single-state x86 SHAKE | A fresh Aeneas extraction with the feature enabled matches the proved caller and scalar fallback. On capable hardware the zero rate block leaves the input state unchanged before Keccak-f. Both branches produce the specified permutation. [Dispatch proof](Dispatch.lean) · [Zero-block proof](../Kgridbulk/ZeroBlock.lean) |

## Connection to Rust

The signer replay lifts the actual Rust sign function to symbolic byte and bit types. Every output byte carries its primitive call and byte offset. Primitive calls compare their full input terms, including the complete XMSS signature slice passed to root recovery. The two input indices have distinct symbolic bits. The reference constructs each tree and leaf address directly from the original indices. The six parameter geometries cover both hash families because the scheduler shares its source and treats those primitives opaquely. The replay exercises a failed CPU-count query, one available CPU, failed spawns, partial spawning and successful spawning. A separate source check binds the counter, worker body, caller drain and scoped join to the effects in the Lean transition system. [Signer replay](../../scripts/parallel-proof/signer.py)

For the subtree, the replay compiles the Rust routine, its layout helpers and the production address serializer into an x86-64 Linux proof executable. Symbolic execution checks every byte of each permutation input against eight independently assembled FIPS byte strings. This includes the address domains, 15 chain steps, endpoint order, complete 136-byte rate blocks, final padding and the seven parent inputs. The two seeds, incoming address fields, valid 29-bit subtree index and all primitive results are symbolic. Each permutation and parent hash returns fresh symbolic data, so the argument checks do not depend on a collision assumption. The replay checks the returned root and rejects symbolic branches, symbolic memory addresses and unexpected calls. It checked 572 calls at 16 bytes, 833 at 24 bytes and 1,096 at 32 bytes. A separate release-build check compares the AVX-512 permutation instruction stream with its existing proved assembly model. [Subtree replay](../../scripts/parallel-proof/subtree.py) · [Assembly check](../../scripts/check-keccak-assembly.sh)

The signing theorem assumes a normally returning scope, standard atomic fetch-add and join semantics, and the specified FORS, WOTS and XMSS primitive contracts. At most 89 counter increments are needed across the twelve parameter sets, including workers' terminating fetches. The symbolic replay trusts its term and bit interpretations, the Rust compiler and the symbolic executor. The subtree proof executable uses modeled permutation and parent-hash calls. These are compositional functional-correctness results. OS scheduling progress, timing leakage, worker-stack erasure and an end-to-end proof of a linked parallel signer are outside their scope.

## Replay

With the repository's Aeneas and Lean dependencies installed, an x86-64 Linux Rust target and `uv`, run the following from the repository root. The driver installs its pinned Python proof dependencies in a managed environment, builds all three Lean modules, audits the headline theorems for unexpected axioms, checks the source bindings and runs the symbolic and assembly checks.

```sh
uv run --script scripts/check-parallel-proof.py
```

During validation, separate disposable builds reversed the leaf lanes, changed the final SHAKE domain byte and substituted the secret seed for the signature randomizer. The checks rejected all three changes.
