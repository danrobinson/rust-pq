# Functional correctness of parallel SLH-DSA

Lean proves that a signing execution satisfying the worker model produces the FIPS 205 signature bytes, including public context framing. The proof uses the FIPS FORS signature and authentication nodes, computes each layer's WOTS message from the preceding XMSS root, and places WOTS signatures in layer order after all jobs join. The phase-one completion theorem permits any ticket to finish last. [Signing theorem](Fused.lean) · [Coverage by component](Multicore.md)

## Connection to Rust

The signer replay runs the production job planner, sorting, barrier, slot publication and signature assembly over symbolic bytes and index bits. It compares every signature byte with a separate construction that obtains each tree address directly from the original indices. It exercises all six FIPS parameter geometries with scalar and modeled SIMD primitives, the single-CPU fallback, and one or four executing workers. A source check guards the order of ticket claims and completion events used by the Lean model. Hash and signature primitives have specified contracts. The replay substitutes a scoped execution harness for the production persistent pool. Its checks exercise particular thread executions. Lean quantifies over completion orders in the model. The signer theorem assumes the pool contract and worker progress. [Signer replay](../../scripts/parallel-proof/signer.py)

The production pool guard borrows the closure through its destructor. The rustc MIR replay checks that an owning dispatcher calls that destructor on normal return and unwind. Lean proves that every conflicting pair of accesses to the shared job cell is ordered, including accesses by later dispatchers, for histories satisfying the per-generation protocol and C++20 coherence. The proof includes a concrete infinite sequence of parked, panicking workers and successful handoffs. Three finite herd7 RC11 tests enumerate reads-from choices, and a two-dispatch Rust test runs under Miri’s Stacked and Tree Borrows. The remaining proof obligation is to map every Rust execution, including pointer provenance and thread/condition-variable behavior, into the Lean histories. [Borrow theorem](PoolBorrow.lean) · [Rust and MIR replay](../../scripts/check-pool-borrow.py) · [RC11 replay](../../scripts/check-pool-litmus.py)

The cached signing replay lifts the SHA-2 and SHAKE job planners and byte assembly from `cache.rs`. It checks a top-tree hit with both a hit and a miss at the preceding layer. For SHAKE it also checks scalar and grouped FORS jobs, the grouped recursion step and each lane’s sponge input and output. Eight mutation tests exercise the ticket stride, cached root, siblings, lane order, recursion, sponge layout and authentication-path offset. The Lean ledger proves that any two normally joined schedules with the same jobs publish identical slot values, assuming unique tickets, successful single-assignment writes and a drained job queue. The replay models the hash primitives and takes valid cached trees as inputs. [Cached signer replay](../../scripts/parallel-proof/cached.py) · [Schedule theorem](Cached.lean) · [Mutation tests](../../scripts/parallel-proof/cached_mutations.py)

The SHAKE subtree replay compiles the production traversal, byte-layout helpers, WOTS leaf code and address serializer to optimized x86-64 code with modeled Keccak and final parent-hash calls. At heights one, two and three, the checker compares every active permutation lane and the final root with FIPS byte strings for arbitrary seeds, address fields, valid subtree index and fresh primitive results. It checks all three digest widths and rejects symbolic control flow or addresses. A separate source replay checks the traversal, child order, absolute indices and buffer updates at every subtree position within the largest standard XMSS tree (height nine), under leaf and parent contracts, for SIMD widths three and eight. [Symbolic execution](../../scripts/parallel-proof/subtree.py) · [Traversal check](../../scripts/parallel-proof/tree-layout.rs) · [Eight-leaf theorem](Subtree.lean)

The single-state x86 SHAKE dispatcher has a separate proof for both results of the AVX-512 feature check. The release assembly check compares the AVX-512 permutation with its proved instruction model. [Dispatch theorem](Dispatch.lean) · [Assembly check](../../scripts/check-keccak-assembly.sh)

## Replay

Install the project's Lean and Aeneas toolchains, the x86-64 Linux Rust target and uv. From the repository root run

```sh
uv run --script scripts/check-parallel-proof.py
```

The driver builds the Lean modules, audits theorem axioms, checks the source bindings, runs the symbolic executions and checks the x86 permutation assembly.
