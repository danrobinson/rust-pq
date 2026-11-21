## Static summary of slhdsa functions in target/release/cttrace

| function | insns | conditional branches | indirect br/blr | udiv/sdiv | crypto-ext insns | SIMD/FP-register insns | csel-family |
|---|---|---|---|---|---|---|---|
| `slhdsa::slh::with_context` | 86 | 6 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::slh::slh_sign` | 47 | 3 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::util::base_2b` | 87 | 8 | 0 | 0 | 0 | 2 | 1 |
| `slhdsa::wots::wots_digits` | 141 | 8 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::wots::wots_pk_from_sig` | 150 | 11 | 0 | 0 | 0 | 13 | 0 |
| `slhdsa::wots::chain` | 41 | 2 | 0 | 0 | 0 | 10 | 0 |
| `slhdsa::sha256::hmac_sha256` | 136 | 13 | 0 | 0 | 0 | 2 | 0 |
| `slhdsa::sha256::sha256` | 642 | 85 | 0 | 0 | 0 | 9 | 0 |
| `<alloc::raw_vec instantiation in slhdsa> h` | 34 | 2 | 0 | 0 | 0 | 0 | 3 |
| `<alloc::raw_vec instantiation in slhdsa> h` | 25 | 1 | 0 | 0 | 0 | 0 | 1 |
| `<alloc::raw_vec instantiation in slhdsa> h` | 44 | 5 | 0 | 0 | 0 | 0 | 1 |
| `slhdsa::ht::ht_sign` | 100 | 6 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::slh::slh_sign_internal` | 171 | 12 | 0 | 0 | 0 | 7 | 0 |
| `slhdsa::slh::slh_keygen_internal` | 35 | 0 | 0 | 0 | 0 | 10 | 0 |
| `slhdsa::fors::fors_sk_gen` | 21 | 0 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::fors::fors_pk_from_sig` | 259 | 16 | 0 | 0 | 0 | 23 | 0 |
| `slhdsa::fors::fors_node` | 65 | 1 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::fors::fors_sign` | 138 | 9 | 0 | 0 | 0 | 6 | 0 |
| `slhdsa::hash::h_msg` | 184 | 11 | 0 | 0 | 0 | 17 | 0 |
| `slhdsa::hash::thash` | 151 | 6 | 0 | 0 | 0 | 21 | 0 |
| `slhdsa::hash::prf_msg` | 75 | 4 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::wots::wots_pk_gen` | 286 | 4 | 0 | 0 | 0 | 32 | 0 |
| `slhdsa::wots::wots_sign` | 135 | 9 | 0 | 0 | 0 | 15 | 0 |
| `slhdsa::xmss::xmss_pk_from_sig` | 75 | 3 | 0 | 0 | 0 | 4 | 1 |
| `slhdsa::xmss::hash2` | 68 | 3 | 0 | 0 | 0 | 4 | 0 |
| `slhdsa::xmss::xmss_node` | 55 | 1 | 0 | 0 | 0 | 0 | 0 |
| `slhdsa::xmss::xmss_sign` | 258 | 10 | 0 | 0 | 0 | 20 | 0 |
| **total** | 3509 | 239 | 0 | 0 | 0 | 215 | 7 |

SIMD/FP-register instructions used in slhdsa code (mnemonic: count): str: 79, ldr: 77, stp: 20, ldur: 17, stur: 6, ldp: 5, mov.s: 3, movi.2d: 2, ushl.4s: 2, dup.4s: 1, zip1.4s: 1, uzp1.8h: 1, xtn.8b: 1

### Conditional branches inside the compiled `sha256` (compress/schedule/pad are inlined into it)

| branch | condition set by (registers abstracted to R) | direction | count |
|---|---|---|---|
| `b.hs` | `cmp R, R` | forward | 64 |
| `b.ne` | `cmp R, R` | forward | 9 |
| `cbz` | `cbz R` | forward | 3 |
| `cbnz` | `cbnz R` | forward | 1 |
| `b.ne` | `cmp R, #0x38` | forward | 1 |
| `b.eq` | `cmp R, R` | forward | 1 |
| `b.eq` | `cmp R, #0x38` | forward | 1 |
| `b.ne` | `cmp R, R` | backward (loop) | 1 |
| `b.ne` | `subs R, R, #0x1` | backward (loop) | 1 |
| `b.ne` | `cmp R, #0x100` | backward (loop) | 1 |
| `b.lo` | `cmp R, R` | backward (loop) | 1 |
| `b.eq` | `cmp R, R` | backward (loop) | 1 |

Register-indexed loads in `sha256` (base + index register):

- `ldr w10, [x20, x10]` x15
- `ldr w10, [x20, x0]` x1
- `ldr w30, [x9, x6]` x1
- `ldr w28, [x4, x6]` x1

## Object-code comparison of slhdsa

- A: `target/release/build/slhdsa/71d522cffa462b8f/out/libslhdsa-71d522cffa462b8f.rlib`
- B: `../target/release/build/slhdsa/b5f420dc9e5ca955/out/libslhdsa-b5f420dc9e5ca955.rlib`


31 functions identical instruction-for-instruction (incl. relocation targets), 0 different, 0 present in only one; 4171 disassembly lines (instructions + relocation records) compared in A.

