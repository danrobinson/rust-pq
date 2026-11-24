# Linked AVX-512 Keccak permutation

The certificate covers the eight-state Keccak-f[1600] leaf in an x86-64 Linux ELF, from its first state load through its return. For every eight input states with 25 words each, the output of every lane is the FIPS 202 permutation of that input. Arbitrary incoming scratch-register and spill values are allowed.

`Binary.lean` defines the subset of x86 encodings and single-lane operations used by the leaf. `Linked.lean` checks the register state between rounds, the exact loop counter and its exit, and the little-endian table reads. It composes these results with `KeccakAsm.round_fips`. Concrete byte equality covers all EVEX opcode and operand fields, read/write offsets, alignment instructions, the RIP-relative table address, the conditional jump displacement, `vzeroupper`, and `ret`. The checker accepts this instruction schedule and relocation within signed displacement range. A different compiler schedule requires a fresh proof.

`LinkedTrace.lean` proves a second result in the same restricted instruction model. Every possible state produces the same architectural data-access and control-transfer trace for fixed addresses and return location. It includes 25 vector loads, the per-round spill accesses and indexed constant reads, all 24 conditional branch outcomes, 25 vector stores and the final return. Each row access is 64 bytes. The trace leaves instruction latency, transient execution, caches below the architectural access model, power and faults outside its scope.

## Check an artifact

From the repository root, supply the **final linked executable**. The checker also supports stripped executables that retain ELF unwind extents.

```sh
uv run --script scripts/check-keccak-elf.py /path/to/program --save-certificate /tmp/Artifact.lean
uv run --script scripts/test-keccak-elf.py /path/to/program
```

The first command reads the executable's ELF load segments, function extent and round-table displacement. Lean compares all extracted bytes with its encoding and audits the specialized functional and trace theorems. The second command checks the original and flips one bit at a time in the ternary immediate, backwards branch target, constant address and table contents. Each altered certificate must fail inside Lean. The executable is read as data throughout.

`ReleaseWitness.lean` records the concrete bytes from the repository's `platforms` benchmark, a consumer calling all twelve parameter sets. It was built at production library revision `74b1b3e` using Rust 1.100.0, `cargo build --locked --release --features platform-sha2 --target x86_64-unknown-linux-gnu --bench platforms` in `rust/`, and Zig 0.15.2 as the cross-linker. Build paths and link options can change the file hash. The sample has these identities:

| Range | ELF virtual address | Bytes | SHA-256 |
|---|---:|---:|---|
| Entire stripped ELF | | 1,277,912 | `d0684e30aa7e85cc8c7229cd5da885ae7f9eb6d9c857d01363b90f993c330c69` |
| Permutation | `0x71170` | 1,158 | `23fa8d80b4feaf27cd514173e326c768c1fef57c65dc0224d601ab204fbc4fdb` |
| Constants | `0xa868` | 192 | `f8e6964adffc257265537256d21e93496a17b9271dc5d64f40869eeeaaff6fbb` |

Replay the sample without a compiler or cross-linker using `cd lean-hw && lake build Keccakasm.ReleaseWitness`. Re-run the ELF checker to bind a particular deployed file to a new certificate. The SHA-256 digest identifies the full file. The two theorems describe the bytes selected from that file.

## Assumptions

The byte encoder and operation model describe the supported instruction subset. Their match to the architectural x86-64 semantics and the hardware remains trusted. The ELF reader, Python file I/O and hash identify and map the measured bytes. Lean checks their equality and the subsequent mathematical proof. The loader must map these bytes with one load bias and preserve them at execution. The code expects enabled AVX-512 support, a valid System V x86-64 call with a writable red zone and valid return address, and a writable 1,600-byte transposed state disjoint from the spill, return slot, constants and code. The certificate concerns calls entering this leaf at the measured address. It does not verify a full ISA interpreter, dynamic dispatch, callers, process startup or the rest of a signing executable.
