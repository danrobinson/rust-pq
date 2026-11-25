# Metal signature values

[CommandValues.lean](CommandValues.lean) composes the command epochs, typed signature layout and FIPS 205 pipeline model. For supported parameters, well-formed signing keys and a successful public signing batch, the result contains the FIPS signature of each request in order, with its context and supplied randomness. The theorem covers pooled buffers larger than the current output, an empty batch and context rejection. The host checker instantiates it for both XMSS modes on all twelve parameter sets. [Host traces and public wrappers](../../scripts/metal-command.py) · [FIPS pipeline model](Pipeline.lean)

The theorem takes a local value contract for each command. Its premise says that if every region read by that command contains its intended values, the command produces the intended values in its own output regions. Host initialization has no inputs in the command graph. Each GPU input has exactly one writer in an earlier epoch. Induction on epochs then supplies the local premises without assuming that the returned buffer already contains a valid signature.

| Producer | Value checked |
|---|---|
| Host | Context guard and framing, argument order to the randomizer and digest routines, key packing, selected key, descriptor fields and offsets, randomizer prefix and returned slices. The host checks bind the Rust statements and rely on the CPU primitive contracts. |
| WOTS chain tips, two-phase and streaming XMSS leaves | WOTS PRF and hash address at each step, chaining value, ordered chain tips, address encoding, all compression or permutation inputs, padding, output truncation and word order. |
| FORS passes and XMSS reduction | The leaf secret and its PRF/F domain, ordered children, absolute node index and height at every parent hash, sibling node values, subroot publication, final root and output serialization. |
| FORS public key | Ordered tree roots, full hash transcript and truncated result. |
| WOTS signature | Selected FORS root or preceding layer root, message and checksum digits, chain length, key and address, final serialized bytes. |

The [shader value checker](../../scripts/check-metal-values.py) uses production MSL function bodies and CBMC bitvectors. Key data, messages, target indices, descriptor fields and cryptographic outputs are symbolic. Hash comparisons check the bytes entering compression or permutation and allow arbitrary results, so the claims compose with the primitive implementations. At threadgroup barriers the checker supplies an arbitrary table of node words indexed by height, absolute node index and word number. Each producer must write the specified entry. The prior [barrier checker](../../scripts/check-metal-workgroups.py) establishes that all lanes have published the required entries before the next phase reads. The [address checker](../../scripts/check-metal-reads.py) and grid checks justify specializing active lanes to their row-major coordinates and rebasing accesses to the selected records.

The Lean theorem retains its local execution contracts. The shader, host and address checkers supply separate source evidence for them. Application to a device assumes the MSL and host projections describe the compiled program, the Objective-C runtime and the device. The contracts cover integer and pointer semantics, coherent buffers, barriers, valid buffer bindings, CPU and GPU primitives and successful completion. Full native signature comparisons use finite test vectors.

Run from the repository root with CBMC installed or `CBMC` set to its executable.

```sh
python3 scripts/check-metal-kernels.py
python3 scripts/check-metal-values.py
uv run --script scripts/check-metal-reads.py
uv run --script scripts/check-metal-workgroups.py
```
