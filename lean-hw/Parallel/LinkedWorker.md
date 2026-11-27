# Linked Apple signing worker handshake

The parallel release ACVP consumer contains six signing worker bodies, one per hash family and hash output length. The checker analyzes the direct, normal-return control flow of each body, including its spin and condition-variable loops. For the checked image it identifies the following operations by their register dataflow and their use in branch conditions.

| Closure capture offset | Role and machine operation |
| --- | --- |
| `0x80`, `0x88` | An `LDADDAL` increments the completion counter by one. The worker compares the returned count plus one to the captured total. |
| `0x00` | An `STLRB` publishes the value one before the call to notify all waiters. `LDAPRB` reads the same state byte in the spin and parked paths. |
| `0xe8`, `0xf0` | An `LDADD` increments the second work cursor by one. The worker compares the returned index to the captured WOTS slots vector length. |

For every worker, a generated Lean certificate proves that every represented path from entry to the READY store traverses a successful completion-count equality test. Every path to either second-phase claim traverses an acquire load whose value compared equal to READY. The checker rejects mutations to the branch directions, acquisition or publication instruction, and ticket address. The check reads an immutable copy of the supplied binary and reports its SHA-256 digest.

Run `python3 scripts/check-linked-worker-handshake.py BINARY --self-test` on macOS with Xcode command-line tools and the project's Lean toolchain. Add `--herd PATH_TO_HERD7` and optionally `--libdir MODEL_DIRECTORY` to check a three-thread projection against herdtools7's Arm memory model. The projection checks that a reader observing READY sees a first worker's pre-completion row and the finalizer's pre-publication root. It admits a successful execution, and separate weakened-instruction controls admit stale rows or roots.

Lean checks the path-cut argument over the graph emitted by the checker. This relies on the Mach-O symbol extents, LLVM disassembly, the Python register/spill and branch translation, and the platform calling convention. The analysis models compiler-private spill storage and stable read-only closure captures over normally returning calls. It treats a call as a fall-through edge and a transfer outside the function as an exit. The certificate covers the worker's control dependencies. The litmus checks the particular memory-event projection. Instruction-by-instruction payload computation, unwinding, scheduler progress and the execution of an entire linked consumer are outside these results.
