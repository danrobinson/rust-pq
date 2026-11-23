## Static summary of slhdsa functions in target-hw/release/cttrace

| function | insns | conditional branches | indirect br/blr | udiv/sdiv | crypto-ext insns | SIMD/FP-register insns | csel-family |
|---|---|---|---|---|---|---|---|
| `<instantiation in slhdsa> do_reserve_and_handle::alloc::Global` | 34 | 2 | 0 | 0 | 0 | 0 | 3 |
| `<instantiation in slhdsa> raw_vec::Raw::finish_grow` | 44 | 5 | 0 | 0 | 0 | 0 | 1 |
| `<instantiation in slhdsa> raw_vec::Raw::grow_one` | 25 | 1 | 0 | 0 | 0 | 0 | 1 |
| `slhdsa::api::keygen` | 24 | 0 | 0 | 0 | 0 | 8 | 0 |
| `slhdsa::api::sign` | 47 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::api::sign_deterministic` | 48 | 3 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::fors::fors_batch` | 350 | 10 | 0 | 0 | 0 | 108 | 0 |
| `slhdsa::fors::fors_node` | 64 | 1 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::fors::fors_pk_from_sig` | 600 | 24 | 0 | 0 | 0 | 127 | 0 |
| `slhdsa::fors::fors_sign` | 144 | 9 | 0 | 0 | 0 | 13 | 0 |
| `slhdsa::fors::fors_sk_gen` | 21 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::hash::chain_blocks` | 2704 | 33 | 0 | 0 | 1062 | 2460 | 8 |
| `slhdsa::hash::chain_blocks_portable` | 84 | 8 | 0 | 0 | 4 | 29 | 1 |
| `slhdsa::hash::h_msg` | 247 | 14 | 0 | 0 | 4 | 48 | 0 |
| `slhdsa::hash::prf_msg` | 180 | 8 | 0 | 0 | 8 | 66 | 0 |
| `slhdsa::hash::seed_ctx` | 49 | 2 | 0 | 0 | 4 | 28 | 0 |
| `slhdsa::hash::thash` | 121 | 4 | 0 | 0 | 0 | 16 | 0 |
| `slhdsa::hash::thash_short` | 144 | 4 | 0 | 0 | 4 | 43 | 0 |
| `slhdsa::hash::thash_values` | 240 | 3 | 0 | 0 | 4 | 114 | 0 |
| `slhdsa::ht::ht_sign` | 100 | 6 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::ht::ht_verify` | 201 | 7 | 0 | 0 | 0 | 14 | 2 |
| `slhdsa::sha256::hmac_sha256` | 142 | 13 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::sha256::sha256` | 6 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::sha256::sha256_from` | 308 | 27 | 0 | 0 | 8 | 63 | 0 |
| `slhdsa::slh::slh_keygen_internal` | 85 | 2 | 0 | 0 | 4 | 38 | 0 |
| `slhdsa::slh::slh_sign` | 47 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::slh::slh_sign_internal` | 219 | 14 | 0 | 0 | 4 | 36 | 0 |
| `slhdsa::slh::slh_verify_internal` | 114 | 3 | 0 | 0 | 4 | 32 | 0 |
| `slhdsa::slh::with_context` | 86 | 6 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::util::base_2b` | 87 | 8 | 0 | 0 | 0 | 2 | 1 |
| `slhdsa::wots::sk_blocks` | 124 | 1 | 0 | 0 | 0 | 23 | 0 |
| `slhdsa::wots::wots_digits` | 141 | 8 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::wots::wots_pk_from_sig` | 135 | 4 | 0 | 0 | 0 | 29 | 0 |
| `slhdsa::wots::wots_pk_gen` | 42 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::wots::wots_sign` | 84 | 5 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::xmss::xmss_node` | 58 | 1 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::xmss::xmss_pk_from_sig` | 81 | 3 | 0 | 0 | 0 | 9 | 1 |
| `slhdsa::xmss::xmss_sign` | 286 | 10 | 0 | 0 | 0 | 24 | 0 |
| **total (44 functions)** | 8088 | 291 | 0 | 0 | 1114 | 3405 | 21 |

Crypto-extension instructions in slhdsa code (mnemonic: count): sha256h.4s: 314, sha256h2.4s: 294, sha256su0.4s: 253, sha256su1.4s: 253

Other SIMD/FP-register instructions in slhdsa code (mnemonic: count): ldr: 458, mov.16b: 397, add.4s: 348, str: 271, stp: 117, ldp: 113, orr.16b: 100, ext.16b: 80, ldur: 52, stur: 51, rev32.16b: 45, mov.s: 30, movi.2d: 22, fmov: 21, ushr.4s: 20, shl.4s: 20, ushr.2s: 20, shl.2s: 20, dup.2s: 14, ushl.2d: 14, ushl.4s: 10, dup.4s: 8, uzp1.8h: 7, xtn.8b: 7, uzp1.8b: 7, uzp1.4s: 6, zip1.4s: 4, dup.2d: 4, umov.b: 4, xtn.4h: 4, movi.16b: 4, mov.d: 3, and.16b: 2, xtn.2s: 2, zip1.8b: 2, eor.16b: 2, rev64.4s: 1, trn2.4s: 1

Call sites in slhdsa code whose target is outside the crate (target: sites): `rust_dealloc`: 61, `__Unwind_Resume`: 27, `_memcpy`: 16, `grow_oneB7_`: 14, `slice_index_fail`: 13, `panic_bounds_check`: 8, `_bzero`: 5, `handle_error`: 3, `rust_alloc`: 1, `rust_no_alloc_shim_is_unstable_v2`: 1, `rust_realloc`: 1

Calls of `memcmp`/`bcmp` from slhdsa code: 0.

### `slhdsa::sha256::schedule`: no out-of-line copy in this binary

### Conditional branches in `slhdsa::sha256::sha256_from` (308 instructions, 8 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.ne` | `cmp R, R` | forward | 9 |
| `cbz` | `cbz R` | forward | 3 |
| `b.eq` | `cmp R, #0x10` | backward (loop) | 2 |
| `b.hi` | `cmp R, R` | forward | 2 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 2 |
| `b.eq` | `cmp R, #0x38` | forward | 1 |
| `b.eq` | `cmp R, R` | backward (loop) | 1 |
| `b.eq` | `cmp R, R` | forward | 1 |
| `b.hs` | `cmp R, #0x40` | forward | 1 |
| `b.hs` | `cmp R, R` | forward | 1 |
| `b.lo` | `cmp R, R` | forward | 1 |
| `b.ne` | `cmp R, #0x38` | forward | 1 |
| `b.ne` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `subs R, R, R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::sha256::sha256_from` (base + index register):

- `strb w8, [x9, x21]` x6
- `ldr q3, [x25, x9, lsl #4]` x2
- `ldr q2, [x8, x11, lsl #4]` x2
- `ldr q3, [x8, x12, lsl #4]` x2
- `ldr q3, [x8, x13, lsl #4]` x2
- `ldr q5, [x8, x12, lsl #4]` x2
- `str q4, [x8, x11, lsl #4]` x2
- `strb w8, [x26, x23]` x1
- `strb w8, [x9, x24]` x1
- `strb w20, [x8, x21]` x1

### Conditional branches in `slhdsa::hash::chain_blocks` (2704 instructions, 1062 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.hs` | `cmp R, R` | forward | 8 |
| `b.lo` | `cmp R, #0x2` | forward | 4 |
| `b.ne` | `subs R, R, #0x1` | backward (loop) | 3 |
| `b.eq` | `cmp R, #0x2` | backward (loop) | 2 |
| `b.eq` | `cmp R, #0x3` | backward (loop) | 2 |
| `b.hs` | `cmp R, R` | backward (loop) | 2 |
| `b.eq` | `cmp R, #0x1` | backward (loop) | 1 |
| `b.hs` | `cmp R, R ; ccmp R, #0x4, #0x2, lo` | forward | 1 |
| `b.lo` | `cmp R, R` | backward (loop) | 1 |
| `b.lo` | `cmp R, R` | forward | 1 |
| `b.lo` | `cmp R, R ; ccmp R, #0x4, #0x2, lo` | backward (loop) | 1 |
| `b.lo` | `cmp R, R ; ccmp R, R, #0x0, hs` | forward | 1 |
| `b.ne` | `cmp R, #0x1` | forward | 1 |
| `b.ne` | `cmp R, #0x2` | forward | 1 |
| `b.ne` | `cmp R, #0x3` | forward | 1 |
| `b.ne` | `cmp R, R` | backward (loop) | 1 |
| `cbz` | `cbz R` | forward | 1 |
| `tbnz` | `tbnz R, #0x0` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::chain_blocks` (base + index register):

- `ldr w15, [x3, x8, lsl #2]` x1
- `ldr w16, [x5, x8, lsl #2]` x1

### Conditional branches in `slhdsa::hash::chain_blocks_portable` (84 instructions, 4 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, R` | forward | 3 |
| `b.eq` | `cmp R, #0x10` | backward (loop) | 1 |
| `b.eq` | `cmp R, R` | backward (loop) | 1 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 1 |
| `b.hs` | `cmp R, R` | backward (loop) | 1 |
| `cbz` | `cbz R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::hash::chain_blocks_portable` (base + index register):

- `ldr w11, [x3, x8, lsl #2]` x1
- `ldr w12, [x5, x8, lsl #2]` x1
- `ldr q7, [x10, x14, lsl #4]` x1
- `ldr q6, [x9, x16, lsl #4]` x1
- `ldr q7, [x9, x17, lsl #4]` x1
- `ldr q7, [x9, x0, lsl #4]` x1
- `ldr q17, [x9, x17, lsl #4]` x1
- `str q16, [x9, x16, lsl #4]` x1

### Conditional branches in `slhdsa::hash::thash_short` (144 instructions, 4 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, #0x10` | forward | 1 |
| `b.eq` | `cmp R, #0x2a` | forward | 1 |
| `b.hs` | `cmp R, #0x2b` | forward | 1 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::thash_short` (base + index register):

- `strb w9, [x23, x22]` x1
- `ldr q4, [x9, x8, lsl #4]` x1
- `ldr q3, [x23, x11, lsl #4]` x1
- `ldr q4, [x23, x12, lsl #4]` x1
- `ldr q4, [x23, x13, lsl #4]` x1
- `ldr q6, [x23, x12, lsl #4]` x1
- `str q5, [x23, x11, lsl #4]` x1

### Conditional branches in `slhdsa::hash::thash_values` (240 instructions, 4 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, #0x10` | backward (loop) | 1 |
| `b.hs` | `cmp R, #0x240` | forward | 1 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::thash_values` (base + index register):

- `ldr q5, [x12, x13, lsl #4]` x1
- `ldr q4, [x11, x15, lsl #4]` x1
- `ldr q5, [x11, x16, lsl #4]` x1
- `ldr q5, [x11, x17, lsl #4]` x1
- `ldr q7, [x11, x16, lsl #4]` x1
- `str q6, [x11, x15, lsl #4]` x1

### Conditional branches in `slhdsa::hash::seed_ctx` (49 instructions, 4 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.eq` | `cmp R, #0x10` | forward | 1 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 1 |

Register-indexed loads and stores in `slhdsa::hash::seed_ctx` (base + index register):

- `ldr q3, [x13, x11, lsl #4]` x1
- `ldr q2, [x12, x15, lsl #4]` x1
- `ldr q3, [x12, x16, lsl #4]` x1
- `ldr q3, [x12, x17, lsl #4]` x1
- `ldr q5, [x12, x16, lsl #4]` x1
- `str q4, [x12, x15, lsl #4]` x1

### Conditional branches in `slhdsa::hash::prf_msg` (180 instructions, 8 crypto-extension)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `cbz` | `cbz R` | forward | 3 |
| `b.eq` | `cmp R, #0x10` | forward | 2 |
| `b.hs` | `cmp R, #0xc` | backward (loop) | 2 |
| `b.hi` | `cmp R, R` | forward | 1 |

Register-indexed loads and stores in `slhdsa::hash::prf_msg` (base + index register):

- `str q0, [x20, x8]` x1
- `ldr q3, [x23, x8, lsl #4]` x1
- `ldr q2, [x9, x11, lsl #4]` x1
- `ldr q3, [x9, x12, lsl #4]` x1
- `ldr q3, [x9, x13, lsl #4]` x1
- `ldr q5, [x9, x12, lsl #4]` x1
- `str q4, [x9, x11, lsl #4]` x1
- `ldr q1, [x23, x9, lsl #4]` x1
- `ldr q0, [x8, x11, lsl #4]` x1
- `ldr q1, [x8, x12, lsl #4]` x1
- `ldr q1, [x8, x13, lsl #4]` x1
- `ldr q3, [x8, x12, lsl #4]` x1
- `str q2, [x8, x11, lsl #4]` x1

## Object-code comparison of slhdsa

- A: `target-hw/release/build/slhdsa/c23c362924e7fb82/out/libslhdsa-c23c362924e7fb82.rlib`
- B: `target-hw/parent/release/build/slhdsa/892bdcef6834ff45/out/libslhdsa-892bdcef6834ff45.rlib`

Constant-data sections of the object files (`__const`, `__literal*`, `__cstring`; unlinked, so independent of addresses):

- `__TEXT,__literal16`: 432 bytes, identical
- `__TEXT,__const`: 256 bytes, identical
- `__TEXT,__cstring`: 2 strings, the source-file paths of the panic locations; identical except that A has them absolute and B relative to the crate directory (44 bytes longer each)
- `__DATA,__const`: 168 bytes, identical except 7 8-byte fields that are larger in A by exactly 44: the lengths of those path strings in the panic-location records
- `__TEXT,__literal16`: 464 bytes, identical
- `__TEXT,__cstring`: 5 strings, the source-file paths of the panic locations; identical except that A has them absolute and B relative to the crate directory (44 bytes longer each)
- `__DATA,__const`: 288 bytes, identical except 12 8-byte fields that are larger in A by exactly 44: the lengths of those path strings in the panic-location records
- `__TEXT,__const`: 708 bytes, identical

constant data: same numeric constants and tables in A and B.

55 functions identical instruction-for-instruction (incl. relocation targets), 0 different, 0 present in only one; 9004 disassembly lines (instructions + relocation records) compared in A; 0 code ranges left unnamed.

