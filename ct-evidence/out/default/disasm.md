## Static summary of slhdsa functions in target/release/cttrace

| function | insns | conditional branches | indirect br/blr | udiv/sdiv | crypto-ext insns | SIMD/FP-register insns | csel-family |
|---|---|---|---|---|---|---|---|
| `<instantiation in slhdsa> do_reserve_and_handle::alloc::Global` | 34 | 2 | 0 | 0 | 0 | 0 | 3 |
| `<instantiation in slhdsa> raw_vec::Raw::finish_grow` | 44 | 5 | 0 | 0 | 0 | 0 | 1 |
| `<instantiation in slhdsa> raw_vec::Raw::grow_one` | 25 | 1 | 0 | 0 | 0 | 0 | 1 |
| `slhdsa::api::keygen` | 24 | 0 | 0 | 0 | 0 | 8 | 0 |
| `slhdsa::api::sign` | 47 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::api::sign_deterministic` | 46 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::fors::fors_batch` | 335 | 10 | 0 | 0 | 0 | 107 | 0 |
| `slhdsa::fors::fors_node` | 64 | 1 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::fors::fors_pk_from_sig` | 608 | 24 | 0 | 0 | 0 | 128 | 0 |
| `slhdsa::fors::fors_sign` | 151 | 9 | 0 | 0 | 0 | 13 | 0 |
| `slhdsa::fors::fors_sk_gen` | 21 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::hash::chain_blocks` | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::hash::chain_blocks_portable` | 300 | 8 | 0 | 0 | 0 | 70 | 1 |
| `slhdsa::hash::h_msg` | 292 | 13 | 0 | 0 | 0 | 22 | 0 |
| `slhdsa::hash::prf_msg` | 271 | 6 | 0 | 0 | 0 | 13 | 0 |
| `slhdsa::hash::seed_ctx` | 111 | 1 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::hash::thash` | 121 | 4 | 0 | 0 | 0 | 16 | 0 |
| `slhdsa::hash::thash_short` | 173 | 3 | 0 | 0 | 0 | 20 | 0 |
| `slhdsa::hash::thash_values` | 297 | 2 | 0 | 0 | 0 | 85 | 0 |
| `slhdsa::ht::ht_sign` | 100 | 6 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::ht::ht_verify` | 201 | 7 | 0 | 0 | 0 | 14 | 2 |
| `slhdsa::sha256::hmac_sha256` | 142 | 13 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::sha256::schedule` | 144 | 8 | 0 | 0 | 0 | 33 | 9 |
| `slhdsa::sha256::sha256` | 6 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::sha256::sha256_from` | 402 | 23 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::slh::slh_keygen_internal` | 135 | 1 | 0 | 0 | 0 | 16 | 0 |
| `slhdsa::slh::slh_sign` | 47 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::slh::slh_sign_internal` | 267 | 13 | 0 | 0 | 0 | 12 | 0 |
| `slhdsa::slh::slh_verify_internal` | 163 | 2 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::slh::with_context` | 86 | 6 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::util::base_2b` | 87 | 8 | 0 | 0 | 0 | 2 | 1 |
| `slhdsa::wots::sk_blocks` | 124 | 1 | 0 | 0 | 0 | 23 | 0 |
| `slhdsa::wots::wots_digits` | 141 | 8 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::wots::wots_pk_from_sig` | 142 | 4 | 0 | 0 | 0 | 29 | 0 |
| `slhdsa::wots::wots_pk_gen` | 42 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::wots::wots_sign` | 89 | 5 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::xmss::xmss_node` | 58 | 1 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::xmss::xmss_pk_from_sig` | 81 | 3 | 0 | 0 | 0 | 9 | 1 |
| `slhdsa::xmss::xmss_sign` | 286 | 10 | 0 | 0 | 0 | 24 | 0 |
| **total (45 functions)** | 6330 | 252 | 0 | 0 | 0 | 703 | 22 |

Crypto-extension instructions in slhdsa code (mnemonic: count): none

Other SIMD/FP-register instructions in slhdsa code (mnemonic: count): str: 189, ldr: 161, stp: 57, ldur: 50, stur: 44, mov.b: 24, movi.2d: 14, ushl.2d: 14, ldp: 12, shl.4s: 12, orr.16b: 12, mov.s: 10, ushl.4s: 10, dup.4s: 8, mov: 8, ushll.4s: 8, tbl.16b: 8, uzp1.8h: 7, xtn.8b: 7, uzp1.8b: 7, uzp1.4s: 6, and.16b: 6, dup.2d: 4, umov.b: 4, xtn.4h: 4, zip1.4s: 4, xtn.2s: 2, mov.d: 2, zip1.8b: 2, movi.16b: 2, eor.16b: 2, rev64.4s: 1, trn2.4s: 1, ld4.8b: 1

Call sites in slhdsa code whose target is outside the crate (target: sites): `rust_dealloc`: 61, `__Unwind_Resume`: 27, `_memcpy`: 16, `grow_oneB7_`: 14, `panic_bounds_check`: 11, `slice_index_fail`: 11, `_bzero`: 5, `handle_error`: 3, `rust_alloc`: 1, `rust_no_alloc_shim_is_unstable_v2`: 1, `rust_realloc`: 1

Calls of `memcmp`/`bcmp` from slhdsa code: 0.

### Conditional branches in `slhdsa::sha256::schedule` (144 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.hs` | `cmp R, R` | forward | 4 |
| `b.lo` | `adds R, R, #0x1` | backward (loop) | 1 |
| `b.lo` | `cmp R, #0x8` | forward | 1 |
| `b.ne` | `adds R, R, #0x8` | backward (loop) | 1 |
| `b.ne` | `subs R, R, #0x1` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::sha256::schedule` (base + index register):

- `ldr w14, [x12, x11]` x1
- `str w14, [x13, x11]` x1

### Conditional branches in `slhdsa::sha256::sha256_from` (402 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.ne` | `cmp R, R` | forward | 9 |
| `cbz` | `cbz R` | forward | 3 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 2 |
| `b.eq` | `cmp R, #0x38` | forward | 1 |
| `b.eq` | `cmp R, R` | backward (loop) | 1 |
| `b.eq` | `cmp R, R` | forward | 1 |
| `b.hs` | `cmp R, #0x40` | forward | 1 |
| `b.lo` | `cmp R, R` | backward (loop) | 1 |
| `b.ls` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `cmp R, #0x38` | forward | 1 |
| `b.ne` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `subs R, R, R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::sha256::sha256_from` (base + index register):

- `strb w8, [x9, x22]` x6
- `ldr w2, [x23, x12]` x2
- `ldr w1, [x22, x12]` x1
- `strb w8, [x24, x22]` x1
- `strb w8, [x9, x24]` x1
- `strb w9, [x8, x24]` x1
- `ldr w1, [x24, x12]` x1

### Conditional branches in `slhdsa::hash::chain_blocks` (1 instructions, 0 crypto-extension)

(a tail jump to `slhdsa::hash::chain_blocks_portable`)

### Conditional branches in `slhdsa::hash::chain_blocks_portable` (300 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, R` | forward | 3 |
| `b.hs` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 1 |
| `b.ne` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `subs R, R, #0x1` | backward (loop) | 1 |
| `cbz` | `cbz R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::hash::chain_blocks_portable` (base + index register):

- `ldr w20, [x3, x13, lsl #2]` x1
- `ldr w8, [x5, x13, lsl #2]` x1
- `ldr w22, [x17, x13]` x1
- `ldr w24, [x15, x13]` x1

### Conditional branches in `slhdsa::hash::thash_short` (173 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, #0x2a` | forward | 1 |
| `b.hs` | `cmp R, #0x2b` | forward | 1 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::thash_short` (base + index register):

- `strb w8, [x23, x22]` x1
- `ldr w6, [x15, x12]` x1
- `ldr w7, [x23, x12]` x1

### Conditional branches in `slhdsa::hash::thash_values` (297 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.lo` | `cmp R, #0x240` | backward (loop) | 1 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::thash_values` (base + index register):

- `ldr w2, [x28, x12]` x1
- `ldr w1, [x27, x12]` x1

### Conditional branches in `slhdsa::hash::seed_ctx` (111 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.ne` | `cmp R, #0x100` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::seed_ctx` (base + index register):

- `ldr w3, [x14, x12]` x1
- `ldr w2, [x21, x12]` x1

### Conditional branches in `slhdsa::hash::prf_msg` (271 instructions, 0 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `cbz` | `cbz R` | forward | 3 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 2 |
| `b.hi` | `cmp R, R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::hash::prf_msg` (base + index register):

- `str q0, [x20, x8]` x1
- `ldr w2, [x22, x8]` x1
- `ldr w1, [x23, x8]` x1
- `ldr w2, [x22, x12]` x1
- `ldr w1, [x21, x12]` x1

## Object-code comparison of slhdsa

- A: `target/release/build/slhdsa/71d522cffa462b8f/out/libslhdsa-71d522cffa462b8f.rlib`
- B: `target/parent/release/build/slhdsa/b5f420dc9e5ca955/out/libslhdsa-b5f420dc9e5ca955.rlib`

Constant-data sections of the object files (`__const`, `__literal*`, `__cstring`; unlinked, so independent of addresses):

- `__TEXT,__literal16`: 384 bytes, identical
- `__TEXT,__cstring`: 6 strings, the source-file paths of the panic locations; identical except that A has them absolute and B relative to the crate directory (44 bytes longer each)
- `__DATA,__const`: 336 bytes, identical except 14 8-byte fields that are larger in A by exactly 44: the lengths of those path strings in the panic-location records
- `__TEXT,__const`: 708 bytes, identical

constant data: same numeric constants and tables in A and B.

51 functions identical instruction-for-instruction (incl. relocation targets), 0 different, 0 present in only one; 6991 disassembly lines (instructions + relocation records) compared in A; 0 code ranges left unnamed.

