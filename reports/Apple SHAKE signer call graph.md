# Linked Apple SHAKE signer call graph

The 24 signing exports in the measured Apple arm64 ACVP executable lead to 195 distinct local function extents through explicit direct calls and branches. The file contains four signing APIs for each of the six SHAKE parameter sets. The linker assigns the same address to SHAKE-256f’s `sign` and `slh_sign`, giving 23 distinct entry addresses. The executable is 1,499,120 bytes and its SHA-256 is `ab672dc82d293ec220beb29f475bedda4614d59c76636cd16edef18705e1ac0a`. It is the Rust 1.100.0 release ACVP consumer with `platform-sha2` identified in the [binary verification report](SHAKE%20and%20linked%20binary%20verification.md).

| From one export | SHAKE-128s/f | SHAKE-192s/f | SHAKE-256s/f |
|---|---:|---:|---:|
| Internal signing | 136 local extents | 137 | 136 |
| Context-bearing signing, deterministic signing, or fixed-size signing | 138 each | 139 each | 138 each |

### What the direct calls establish

The internal wrappers enter one of three width-specialized signing functions. For example, the 128f wrapper at `0x100072b94` branches to `slhdsa::shake::slh::slh_sign_internal::<16>` at `0x10007be90`. Its body contains calls to sponge absorption and finalization, message hashing, base conversion, FORS signing and recovery, hypertree signing, allocation and release, copying, slice failure and unwinding. The graph includes code that the compiler inlined into these bodies, but cannot split the inlined operations into separate symbols or establish their semantics.

Across all 24 exports, 747 direct calls and 27 cross-function unconditional branches target local code. A further 154 calls and ten branches target dynamic import stubs. An independent pass over LLVM’s disassembly reproduced all 938 direct site/destination pairs. Direct branches to another extent are reported as tail branches. The listing does not assert that every call site runs for a valid signature.

### Which signer routines still need machine-code summaries?

Of the 195 extents, 83 have a top-level `slhdsa` symbol or implement a method on an `slhdsa` type. The remaining 112 include compiler-generated and runtime code, among them an array-map specialization used by the two-state Keccak block driver. The following is the baseline at proof revision `fd9d940`. The source proofs continue to apply at their own abstraction level.

| Linked code | Binary verification status at that revision |
|---|---|
| Six internal signing entry stubs | Checked argument forwarding, parameter rows and direct branch targets. The other 18 exported signing names also enter this inventory. |
| Three width-specialized hypertree signers | Checked the XMSS sign/recover call order for each standard parameter set. The bytes returned by callees and all failure paths require additional contracts. |
| Two-state SHA3 Keccak permutation and single-state adapter | Existing LinkedArm and wrapper results cover the permutation and data movement under their stated ISA and ABI assumptions. |
| Internal signer and context preparation | The three `slh_sign_internal` bodies, shared `with_context`, output serialization and their inlined code need full functional summaries. |
| SHAKE hash and sponge helpers | `Sponge::absorb`, `Sponge::finish`, `sha3::blocks`, its array-map specialization, and width-specific `h_msg`, `start` and `thash_pair`. |
| Tree and chain helpers | FORS `nodes`, `sign` and `recover`; XMSS `xmss_node`, `xmss_sign` and `xmss_pk_from_sig`; batch `chains`, `chain_order`, `header`, `keygen`, `sign`, `recover` and the 24-byte `pair` specialization; `wots_digits` and `base_2b`. |
| Compiler and runtime | `RawVec` growth and reserve, allocation, deallocation, allocation error, slice-index and bounds-check panic, landing pads and unwinding. A successful-path argument needs to discharge the conditions that lead to failure or state explicit assumptions. |

### Imports and unresolved exits

The 83 library extents directly name four imports through Mach-O stubs: `_memcpy`, `_bzero`, `_memset_pattern16` and `__Unwind_Resume`. The full closure names 29 imports, including allocation, panic, synchronization, environment and I/O functions. Each root’s complete import list and each site’s stub address appear in the JSON. The names identify the linker's requests; dyld and the selected implementations determine what runs.

Across the 195 extents, 28 register-indirect calls and five register-indirect branches leave unknown targets. These sites occur in runtime or compiler code, including panic hooks, formatting, destruction and synchronization. The scan also records 34 BRK and 357 UDF instruction words and 128 extent boundaries where the final instruction could fall through under the local decoding. Extents include padding and cold blocks. A final call to a nonreturning panic or unwind function, for example, has a syntactic fallthrough even though that callee normally never returns. None of the 83 library extents contains a register-indirect call or branch. Exception dispatch, loader interposition, upstream callers, and actual path feasibility remain outside this direct-edge inventory.

### Reproduce the site listing

With Apple command-line tools and `uv` installed, pass the unstripped thin arm64 executable to the [inventory tool](../scripts/apple-binary/signer_inventory.py).

```sh
scripts/apple-binary/signer_inventory.py /path/to/acvp > signer-inventory.json
```

The JSON identifies every function by preferred virtual address, mangled names, demangled aliases, size and code digest. Each explicit cross-function transfer gives its source and destination, each import gives its stub address and each open exit gives its instruction or possible destination. The scan follows explicit local calls and cross-function branches, scans the entire extent of each discovered function, and records potential cross-extent fallthrough as open. Indirect and exception destinations can reach code outside this listing. The binary’s hash is computed from the same immutable snapshot read by the metadata tools.
