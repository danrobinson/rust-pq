# Trusted statements review

Independent review, 2026-11-21, of (A) the Arm instruction model, (B) the eighteen intrinsic
wrappers and their Lean definitions, and (C) the ideal-compression security statements for
sign/verify with context strings. Read-only on the repository; nothing was changed except this
file. `lake` and `lean` were not run (another build was in progress), so nothing below is a
re-check by the Lean kernel.

## Summary

- **No definition in `lean-hw/Arm.lean`, `lean-hw/Slhdsa/TypesExternal.lean` or
  `lean-hw/Slhdsa/FunsExternal.lean` was found to be wrong.** Every instruction definition matches
  Arm's pseudocode, and every wrapper definition matches its Rust function, including the failure
  conditions.
- **No error was found in the context-string security statements.** The game, the adversary
  class, the hypotheses and the bound are what the documentation says.
- **One statement in the documentation is wrong** (finding 1): `hw::arm` is not the crate's only
  `unsafe` code.
- **One claim is weaker than it reads** (finding 2): the proofs for the `hw-sha2` build do not
  establish that the SHA-256 instructions are executed only on a CPU that has them. The six
  theorems would hold unchanged for a crate whose feature test was inverted.
- The remaining findings are notes on coverage of the evidence, stale text, and things I could
  not verify without running Lean.

## Sources consulted

| What | Source | Remark |
|---|---|---|
| `SHA256H`, `SHA256H2`, `SHA256SU0`, `SHA256SU1`, `EXT`, `ADD`, `USHR`, `SHL`, `REV32` instruction pages; shared pseudocode `SHA256hash`, `SHAchoose`, `SHAmajority`, `SHA256hashSIGMA0/1` | `https://www.scs.stanford.edu/~zyedidia/arm64/` (`sha256h_advsimd.html` etc., `shared_pseudocode.html`) | **Mirror**, not Arm's site. It is Arm's HTML export of the A64 XML, footer `2026-03_rel`, © Arm Limited. Arm's own pages did not render: `developer.arm.com/documentation/ddi0602/...` returns a JavaScript shell (only the page title), and the XML tarballs return 403/404. |
| The same shared functions under their older names (`SHAhashSIGMA0/1`), plus `ROR`, `ROL`, `LSR` | `rems-project/sail-arm`, `arm-v9.4-a/src/v8_base.sail` and `builtins.sail` (Sail translation of Arm's ASL, © Arm Limited 2023) | Second source. In the 2026-03 release `ROR`/`ROL`/`LSR` are ASL built-ins and not in the shared pseudocode, so their definitions were taken from here. |
| Intrinsic to instruction and operand mapping | `ARM-software/acle`, `neon_intrinsics/advsimd.md` (Arm's ACLE repository) | Lines 4852–4855 for the four SHA-256 intrinsics. |
| What the Rust intrinsics do | `stdarch` source in the local toolchain `nightly-2026-09-17` (`core_arch/src/arm_shared/neon/generated.rs`, `aarch64/neon/generated.rs`) | The stable toolchain used to build (rustc 1.100.0) has no `rust-src`; the nightly's copy was read instead. |

All fetched pages were treated as data only.

## Experiments run

All inside
`/private/tmp/claude-501/-Users-danrobinson-Projects-formal-sig/aa936096-0075-48f4-b18f-ef8efe20006c/scratchpad/review/`.
Machine: Apple M5 Ultra, rustc 1.100.0. This is the same CPU model the record was taken from,
so none of these is evidence about other hardware.

| # | Experiment | Result |
|---|---|---|
| E1 | `tools/armcheck.py`: Arm's pseudocode transcribed literally onto Python integers (128-bit values, bit slices, `ROL(Y:X, 32)` on 256 bits), replayed on `vectors/arm-wrappers.txt`. Independent of the Lean model. | 1,745 cases, 0 mismatches. |
| E2 | `tools/mutate.py`: eleven deliberate errors in E1's model (operand swaps for `SHA256H`, `SHA256H2`, `SU0`, `SU1`, `EXT`; wrong rotation constants; wrong `choose`; no byte reversal). | Every one is detected (96 to 512 mismatches). |
| E3 | `tools/leanmodel.py`: a hand transliteration of `Arm.lean`, the plain functions of `Proofs/Hw/Wrappers.lean` and the dispatch of `ArmTest.lean`, element-wise as the Lean text is written. A check of my reading, not a run of Lean. | 1,745 cases, 0 mismatches. |
| E4 | Copy of `rust/` and `vectors/` in `copy/`; `cargo test --release --features hw-sha2`. Run twice: default flags (instructions enabled at compile time, the `inline(always)` arm of `kernel!`), and `RUSTFLAGS="-C target-feature=-sha2"` (the `target_feature(enable = "neon,sha2")` arm with runtime detection). | `arm_wrappers_match_the_record` passes in both. In the second configuration the whole suite passes (6 ACVP tests, 7 `compress.rs` tests including `hardware_backend_is_active_where_the_cpu_has_it`). |
| E5 | Test added to the copy only: `load_words`, `load_be`, `store_be` on every length 0..=66 and every offset 0..=70 plus nine large offsets (`2^32`, `2^62 + 1`, `2^63`, and six within 16 of `usize::MAX`). Compared with the condition in the Lean definition (`4 ≤ len ∧ at ≤ len − 4`, `16 ≤ len ∧ at ≤ len − 16`). | 4,668 in-bounds calls return the value the Lean definition gives; 11,412 out-of-bounds calls panic; no disagreement. On a panic `store_be` leaves the buffer untouched. Same in release, release with `-sha2`, and debug. |
| E6 | One out-of-line `extern "C"` function per wrapper, disassembled. | `sha256h q0, q1, v2`; `sha256h2 q0, q1, v2`; `sha256su0 v0, v1`; `sha256su1 v0, v1, v2`; `ext v0, v0, v1, #8` and `#12`; `ushr #16`; `shl #16`; `mov v0.s[0], w0` / `mov v0.s[1], w1` on a zeroed register; `ldr q0` + `rev32.16b`; `ldr q0`. First argument is `Qd` in every case. (`zero`, `store_words`, `store_be`, `available` were not disassembled.) |
| E7 | `rustc --print cfg -C target-feature=+sha2` on two AArch64 targets. | `sha2` implies `neon`, so `kernel!` testing only `target_feature = "sha2"` is sufficient. |
| E8 | Second copy (`copy2/`) with the `unsafe` removed from `rust/src/sha256.rs:379`, built both ways. | With `-C target-feature=-sha2`: error E0133, "call to function `compress_block` with `#[target_feature]` is unsafe … requires … neon and sha2". With default flags on this Mac it compiles: there the block is a no-op and nothing but the target guarantees the features. |

## Findings

### 1. `hw::arm` is not the crate's only `unsafe` code — **wrong** (documentation)

- **Where.** `README.md:86-89` ("`hw::arm`: eighteen functions … This is the crate's only
  `unsafe` code, and the only code Aeneas does not translate"); `HANDOFF.md:214` ("eighteen
  wrappers … the crate's only `unsafe`"); `rust/src/sha256.rs:248-250` (the comment on
  `mod arm`: "This is the only `unsafe` code").
- **What is there.** Two more `unsafe` blocks in non-test code, both outside `hw::arm` and both
  in functions Aeneas translates: `rust/src/sha256.rs:379`
  (`Some(unsafe { compress_block(state, &block) })` in `hw::compress`) and `:469`
  (`unsafe { chain_all(state, blocks, start, end) }` in `hw::chain_blocks`). Three more in the
  test module (`:749`, `:752`, `:766`). The lint exemption `#[allow(unsafe_code)]` is on the whole
  of `mod hw` (`:229`), not on `mod arm`, so the compiler does not confine `unsafe` to the
  wrappers.
- **What it should say.** `hw::arm` is the only code Aeneas does not translate. The `unsafe`
  code is `hw::arm` plus the two calls that enter the kernel.
- **Why it matters.** On a target that does not have the instructions at compile time these two
  blocks are the only place the obligation "this CPU has `neon` and `sha2`" is discharged. Aeneas
  erases `unsafe`, so the translation (`lean-hw/Slhdsa/Funs.lean:310-327`, `:1482-1502`) shows
  ordinary calls. See finding 2.
- **How established.** Reading the source; `grep -n unsafe rust/src/sha256.rs`.

### 2. Nothing proves the instructions run only where the CPU has them — **weaker than claimed**

- **Where.** `lean-hw/Arm.lean:157-159` (`opaque haveSha2 : Bool`, "Nothing is assumed about it:
  every statement is proved for both answers"); `lean-hw/Slhdsa/FunsExternal.lean:43`
  (`available := ok Arm.haveSha2`) and `:46-140` (the seventeen other wrappers, none of which
  mentions `haveSha2`); `README.md:99-101` ("the six theorems above are proved for this build
  too, whichever answer the feature test gives"); `README.md:110-120` (the list of what the
  `hw-sha2` proof rests on).
- **What the Lean says.** The wrappers are total functions of their arguments whatever
  `haveSha2` is. `sha256h` returns `ok (Arm.SHA256H …)` also when `haveSha2 = false`. The top
  proofs split on `haveSha2` (`lean-hw/Slhdsa/Proofs/CompressTop.lean:15-17`,
  `ChainTop.lean:20-21`) and prove each branch on its own; the kernel's specification
  (`hw_compress_block_spec`, `hw_chain_all_spec`) has no hypothesis about `haveSha2`.
- **Consequence.** The proofs are symmetric in the feature test. If `rust/src/sha256.rs:372`
  read `if arm::available() { return None; }` (test inverted), or if the test were removed, the
  same six theorems would be provable in the same way. On a real CPU without the instructions
  that crate would raise an illegal-instruction fault. So "returns normally, whichever answer
  the feature test gives" is established for the model, in which an absent instruction still
  computes; it is not established that the code consults the test correctly.
- **What the documentation claims instead.** That beyond the default build the proof rests on
  (i) the instruction model and (ii) each wrapper matching its definition. A third item is
  missing: the two guarded calls at `rust/src/sha256.rs:372-379` and `:465-469` are correct by
  reading. `HANDOFF.md:276-277` lists "the behaviour when `std`'s feature detection is wrong" as
  not covered; that is a different point (detection itself), and `HANDOFF.md:287` says the
  fall-through on a CPU without the instructions was never tested. So this property currently
  has neither a proof nor a test.
- **The code itself is right.** Both sites test `!arm::available()` and return before the
  `unsafe` call (`:372-374`, `:465-467`), and the translation agrees
  (`if b then <kernel> else ok none`). On targets without compile-time `sha2` the compiler also
  enforces that the `target_feature` functions are reached only through those `unsafe` calls
  (E8); it does not check that the guard in front of them is the right way round.
- **Possible repair, for the author to judge.** Let each wrapper's definition fail when
  `Arm.haveSha2 = false`. The top theorems then force a proof that the kernel is unreachable in
  that case, and the inverted test is no longer provable.
- **How established.** Reading the files named; the translation in `Funs.lean`.

### 3. The trusted definitions are twenty-one, in three files — **note**

- **Where.** `HANDOFF.md:233-236` ("`lean-hw/Arm.lean` … `FunsExternal.lean` … These two files
  are the trusted addition"); `README.md:98-99` ("defines each of the eighteen functions").
- **What is there.** `FunsExternal.lean` has twenty definitions: the eighteen wrappers,
  `uint32x4_t`'s `Clone::clone` (`:33-35`, `ok v`) and `core::panicking::panic_bounds_check`
  (`:38-39`, `fail .panic`). `TypesExternal.lean:12` is a third trusted file with one definition
  (`uint32x4_t := Arm.V`).
- **Assessment.** All three extra definitions are correct. `panic_bounds_check` is not referenced
  anywhere in `lean-hw/Slhdsa/Funs.lean` or the proofs (grep), so it is dead.

### 4. What the recorded vectors do and do not cover — **note**

- **Covered.** Seventeen of the eighteen wrappers, 1,745 lines: `zero` 1; `pair`, `load_words`,
  `store_words` 48 each; `load_be`, `store_be`, `shr16`, `shl16` 64 each; `add`, `or`, `and`,
  `ext2`, `ext3`, `sha256su0` 96 each; `sha256h`, `sha256h2`, `sha256su1` 256 each. Words are
  zero, all-ones, a single bit, or random. `load_words` uses lengths 4–12 with the offset at the
  last legal position in 20 of 48 cases; `load_be` uses lengths 16–64 and `store_be` 17–63, with
  the offset at the last legal position in 7 and 6 cases. `store_be` records the whole buffer, so bytes
  outside the sixteen written are checked. The record discriminates the obvious transcription
  errors (E2).
- **Not covered.**
  - `available`: no record, and none is possible in this format.
  - Every failure case. No line has an out-of-range offset or a short slice; the format
    `name args = result` cannot express a panic, and `ArmTest.lean:46,50,53` re-states the bounds
    condition and would report a mismatch on such a line. The `fail .panic` branches of
    `load_words`, `load_be`, `store_be` therefore rest on reading. E5 closes this on the Rust
    side for this machine.
  - `load_words` on slices longer than 12 words (the kernel calls it on `K`, 64 words, at
    offsets up to 60). Not a real gap: the function does not depend on the length beyond the
    check.
  - Any other processor. The record, the Rust replay and my replay are all one CPU model.
  - A CPU without the instructions.
- **How the Lean test is tied to the definitions.** `Proofs/Hw/Wrappers.lean` proves, for each
  wrapper, an equation with the definition in `FunsExternal.lean` on the left: thirteen by `rfl`
  (`wr_zero` … `wr_sha256su1`), `wr_load_words` and `wr_load_be` as an `if`-equation,
  `wr_store_words` and `wr_store_be` through the list of byte or word values. Those statements
  are adequate. The remaining link is by eye: `ArmTest.lean:40-65` types out the right-hand
  sides again (`Arm.USHR (vec a) 16`, `⟨a, b, 0, 0⟩`, argument order for `SHA256H2`) rather than
  calling something the theorems mention by name. I compared all seventeen branches with the
  `wr_*` right-hand sides and with the Rust recorder (`rust/src/sha256.rs:767-815`); they agree,
  argument order included. `Wrappers.lean` is not imported by the default target; `scripts/check.sh:20`
  builds it explicitly.
- **How established.** Counting the file; reading `ArmTest.lean`, `Wrappers.lean` and the Rust
  test; E1–E5.

### 5. Results I could not reproduce — **unverifiable by me**

Blocked by the rule against running `lake`/`lean`:

- That `ArmTest.lean` reports 0 mismatches, and 320 for a deliberately wrong model
  (`HANDOFF.md:272-273`). Substitute evidence: E1 and E3.
- That the four new security files and `lean-hw` compile, and that `#print axioms` prints only
  the three standard axioms for `Ideal.suf_ideal_pure_closed`, `Ideal.euf_ideal_pure_closed`,
  `Ideal.rust_ideal_security_closed_pure` and the six `lean-hw` theorems. Substitute evidence:
  `.olean` files newer than their sources exist for `Ideal/Realize/{PureReduce,PureForger,FinalPure}`
  and `Ideal/RustFinalClosedPure` under both `security/.lake` and `security-hw/.lake`, and for
  `Arm`, `Slhdsa/FunsExternal`, `Proofs/Hw/Wrappers`, `Proofs/CompressTop`, `Proofs/ChainTop`,
  `Slhdsa/Theorems` under `lean-hw/.lake`; and a grep for `sorry`, `native_decide`, `axiom`,
  `bv_decide`, `implemented_by`, `extern` over all 256 `.lean` files of
  `security/{Ideal,Reduction,Link,E2E}` and over the `lean-hw` files reviewed finds none.
- A non-vacuity witness for the pure theorems compiled in Lean. By reading, the forger
  `main _ := pure (([], []), none)` satisfies every hypothesis at `qf = qs = ℓ = 0`
  (`QcAll 0 0 257 = 2^25 + 8`).

### 6. `scripts/check.sh` does not police axioms for the security libraries reviewed here — **note**

- **Where.** `scripts/check.sh:24-25`. The placeholder search covers `lean/Slhdsa/Proofs`,
  `lean/Slhdsa/Theorems.lean`, `lean/Spec`, `security/Link`, `security/E2E`, `lean-hw/Arm.lean`,
  `lean-hw/ArmTest.lean`, `lean-hw/Slhdsa`. It does not cover `security/Ideal` or
  `security/Reduction`, and nothing parses the `#print axioms` output of the build.
  `HANDOFF.md:208-210` describes the script as running "the placeholder search" without that
  limit.
- **Consequence.** A `sorry` in `security/Ideal` would leave the script printing "All checks
  passed". For the context-string theorems the claim "standard axioms only" rests on someone
  reading the build output.
- **Current state.** My grep over those directories is clean (finding 5).

### 7. Text in the Rust sources that contradicts the README — **note**

These say the proofs do not cover the `hw-sha2` build at all, which is no longer the claim:

- `rust/src/lib.rs:12-15`: "one module of `unsafe` intrinsics … which the proofs do not cover:
  they are about the default build".
- `rust/src/sha256.rs:203-216`: "**not covered by the Lean proofs**: Aeneas translates the
  default build, in which this module does not exist … That statement is tested … but not
  proved."
- `rust/Cargo.toml:11-14`: "the crate's only `unsafe` code, which the Lean proofs do not cover".
- `rust/src/sha256.rs:250-251`: "the proofs take the meaning of these functions from the model in
  `lean/SlhdsaHw/FunsExternal.lean`". No such path exists; the file is
  `lean-hw/Slhdsa/FunsExternal.lean`.

### 8. Smaller points — **note**

- `HANDOFF.md:215-216`: "The four that touch memory (`load_words`, `load_be`, `store_be`, and
  `store_words` on its own array) check their bounds with an overflow-free `assert!`."
  `store_words` (`rust/src/sha256.rs:289-296`) has no `assert!` and needs none: it writes two
  four-word vectors at constant offsets 0 and 4 of a local `[u32; 8]`.
- `lean-hw/Slhdsa/FunsExternal.lean:127` quotes the prototype
  `vsha256h2q_u32(hash_efgh, hash_abcd, wk)`. That is the ACLE (C) prototype. Rust's `stdarch`
  declares the same function with the parameter **names** the other way round,
  `vsha256h2q_u32(hash_abcd, hash_efgh, wk)` (`generated.rs:54906` in the nightly source), and
  passes them positionally to `llvm.aarch64.crypto.sha256h2`. Position is what counts, the first
  argument is `Qd` (E6), and the wrapper and its definition are right. A reader checking the
  wrapper against Rust's documentation will see names that appear to contradict it.
- `lean-hw/Arm.lean:12-14` names the shared functions `SHAhashSIGMA0`/`SHAhashSIGMA1`. Those are
  the names in the older pseudocode (as in the Sail translation); Arm's current release calls
  them `SHA256hashSIGMA0`/`SHA256hashSIGMA1` and writes `XOR` for `EOR`. Same functions.
- The model has no counterpart of `AArch64_CheckFPAdvSIMDEnabled()` or of the decode check
  `if !IsFeatureImplemented(FEAT_SHA256) then UNDEFINED`. This is the instruction-level form of
  finding 2.
- `HANDOFF.md:261-263` lists the statements checked in `security-hw`; the list stops at
  `Ideal.rust_ideal_security_closed`. A compiled `Ideal/RustFinalClosedPure.olean` exists under
  `security-hw/.lake` (14:27), so the context-string statement appears to have been built there
  too, but no document says so.

## Checked and found correct

### Part A — `lean-hw/Arm.lean` against Arm's pseudocode

| Item | Arm | Lean | Verdict |
|---|---|---|---|
| Vector layout (`:25-32`) | `Elem[v, e, 32]` is bits `32e+31 : 32e` | `e0` is bits 31:0 | correct |
| `ROR` (`:35`) | rotate right, `LSR(x,m) OR LSL(x,N−m)` | `BitVec.rotateRight` | correct |
| `LSR` (`:38`) | logical shift right | `>>>` on `BitVec` | correct |
| `SHAchoose` (`:41`) | `((y XOR z) AND x) XOR z` | same | correct |
| `SHAmajority` (`:44`) | `(x AND y) OR ((x OR y) AND z)` | same | correct |
| `SHAhashSIGMA0` (`:47`) | `ROR 2, 13, 22` | same | correct |
| `SHAhashSIGMA1` (`:50`) | `ROR 6, 11, 25` | same | correct |
| `SHA256hashStep` (`:63-69`) | `chs` from `y[31:0], y[63:32], y[95:64]`; `maj` from the same slices of `x`; `t = y[127:96] + SIGMA1(y[31:0]) + chs + w[e]`; `x[127:96] = t + x[127:96]`; `y[127:96] = t + SIGMA0(x[31:0]) + maj`; `(y, x) = ROL(y :: x, 32)` | new `X = ⟨y3, X.e0, X.e1, X.e2⟩`, new `Y = ⟨x3, Y.e0, Y.e1, Y.e2⟩` | correct: the rotation moves every element up one place and the top of `y` to the bottom of `x`; `SIGMA0` reads `x[31:0]`, which the preceding assignment to `x[127:96]` does not touch |
| `SHA256hash` (`:73-78`) | `for e = 0 to 3`, word `e` of `w`; `part1 ? x : y` | four steps on `W.e0..e3`; `if part1 then X else Y` | correct |
| `SHA256H` (`:82`) | `V[d] = SHA256hash(V[d], V[n], V[m], TRUE)` | `SHA256hash d n m true` | correct; `Qd` is source and destination |
| `SHA256H2` (`:86`) | `V[d] = SHA256hash(V[n], V[d], V[m], FALSE)` | `SHA256hash n d m false` | correct; operands swapped relative to `SHA256H` as Arm has them |
| `SHA256SU0` (`:97-99`) | `T = op2[31:0] :: op1[127:32]`; `elt = ROR 7 XOR ROR 18 XOR LSR 3`; `result[e] = elt + op1[e]`; `op1 = V[d]`, `op2 = V[n]` | `⟨f d.e1 + d.e0, f d.e2 + d.e1, f d.e3 + d.e2, f n.e0 + d.e3⟩` | correct |
| `SHA256SU1` (`:118-124`) | `T0 = op3[31:0] :: op2[127:32]`; `T1 = op3[127:64]`; `e = 0,1`: `ROR 17 XOR ROR 19 XOR LSR 10` of `T1[e]`, plus `op1[e] + T0[e]`; then `T1 = result[63:0]` for `e = 2,3` | `r0 = g m.e2 + d.e0 + n.e1`, `r1 = g m.e3 + d.e1 + n.e2`, `r2 = g r0 + d.e2 + n.e3`, `r3 = g r1 + d.e3 + m.e0` | correct |
| `ADD`, `ORR`, `AND` (`:127-133`) | element-wise | element-wise | correct |
| `USHR`, `SHL` (`:136-139`) | per-element logical shifts | per-element `>>>`, `<<<` | correct; defined for any `n`, used only at 16, which is inside both immediates' ranges (1–32, 0–31) |
| `EXT2`, `EXT3` (`:143-147`) | `concat = V[m] :: V[n]`; result `concat[position+127 : position]`, `position = 8·imm4`; `vextq_u32(a, b, n)` is `EXT Vd.16B, Vn = a, Vm = b, #(n<<2)` | `⟨a.e2, a.e3, b.e0, b.e1⟩`, `⟨a.e3, b.e0, b.e1, b.e2⟩` | correct |
| `beWord`, `beBytes` (`:151-155`) | `LD1` byte `i` to bits `8i+7:8i`; `REV32` reverses the bytes of each 32-bit container | first byte most significant | correct |
| `haveSha2` (`:159`) | — | opaque `Bool`, no axiom | sound; see finding 2 for what it does not give |

E1 confirms that the processor record agrees with a literal execution of the pseudocode, and E3
that my reading of the Lean text agrees with the record.

### Part B — the eighteen wrappers (`rust/src/sha256.rs:263-363`) against `FunsExternal.lean`

For each: intrinsic and argument order, lane and byte order, failure condition, safety of the
`unsafe` block.

| Wrapper | Rust | Lean (`FunsExternal.lean`) | Verdict |
|---|---|---|---|
| `available` (`:263-265`) | `is_aarch64_feature_detected!("neon") && …("sha2")`; compile-time `true` where the target has them | `ok Arm.haveSha2` (`:43`) | correct as a model of a constant; never panics; safe code |
| `zero` | `vdupq_n_u32(0)` | `⟨0,0,0,0⟩` | correct |
| `pair` | `vsetq_lane_u32(b, vsetq_lane_u32(a, zero, 0), 1)` | `⟨a.bv, b.bv, 0, 0⟩` | correct (`vsetq_lane_u32(value, vector, lane)`) |
| `load_words` | `assert!(w.len() >= 4 && at <= w.len() - 4)`; `vld1q_u32(w.as_ptr().add(at))` | `if 4 ≤ w.length ∧ at ≤ w.length − 4 then ok ⟨w[at], …, w[at+3]⟩ else fail .panic` | correct. `&&` short-circuits, so `w.len() - 4` is never evaluated on a short slice (in release that subtraction would wrap). The read is 16 bytes inside the slice. Little-endian: element `i` is word `at + i`. Fails exactly where Rust panics (E5). |
| `store_words` | two `vst1q_u32` into a local `[u32; 8]` at offsets 0 and 4 | `Array.make 8 [a.e0..a.e3, e.e0..e.e3]` | correct; cannot fail; writes are inside the local array |
| `load_be` | `assert!(b.len() >= 16 && at <= b.len() - 16)`; `vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p)))` | same condition; four `beWord`s of bytes `at..at+16` | correct; fails exactly where Rust panics (E5) |
| `store_be` | same `assert!`; `vst1q_u8(p, vrev32q_u8(vreinterpretq_u8_u32(v)))` | same condition; `b.setSlice! at (be_bytes v)` | correct; sixteen bytes written inside the `&mut` slice, the rest unchanged, length preserved; fails exactly where Rust panics and writes nothing then (E5) |
| `add`, `or`, `and` | `vaddq_u32`, `vorrq_u32`, `vandq_u32` | `Arm.ADD`, `ORR`, `AND` | correct |
| `shr16`, `shl16` | `vshrq_n_u32(a, 16)`, `vshlq_n_u32(a, 16)` | `Arm.USHR a 16`, `Arm.SHL a 16` | correct (`USHR`, `SHL` with `#16`, E6) |
| `ext2`, `ext3` | `vextq_u32(a, b, 2)`, `(a, b, 3)` | `Arm.EXT2 a b`, `Arm.EXT3 a b` | correct |
| `sha256h` | `vsha256hq_u32(abcd, efgh, wk)`; ACLE: `hash_abcd → Qd`, `hash_efgh → Qn`, `wk → Vm` | `Arm.SHA256H abcd efgh wk` | correct |
| `sha256h2` | `vsha256h2q_u32(efgh, abcd, wk)`; ACLE: `hash_efgh → Qd`, `hash_abcd → Qn`, `wk → Vm` | `Arm.SHA256H2 efgh abcd wk` | correct (see finding 8 on Rust's parameter names) |
| `sha256su0` | `vsha256su0q_u32(w0_3, w4_7)`; `Vd`, `Vn` | `Arm.SHA256SU0 w0_3 w4_7` | correct |
| `sha256su1` | `vsha256su1q_u32(tw0_3, w8_11, w12_15)`; `Vd`, `Vn`, `Vm` | `Arm.SHA256SU1 tw0_3 w8_11 w12_15` | correct |

Also correct: `uint32x4_t := Arm.V` (`TypesExternal.lean:12`); `Clone::clone = ok v`; the
signatures match what the translation calls (`store_be` returns the updated slice; all eighteen
are used in `Funs.lean`).

Safety of the `unsafe` blocks:

- Memory: the three `assert!`s cover exactly the bytes touched; `store_words` writes its own
  array; NEON loads and stores here are `read_unaligned`/`write_unaligned`, so alignment is not
  an obligation.
- CPU features, target with `sha2` at compile time (`aarch64-apple-darwin`): `kernel!` gives
  `inline(always)` and no `target_feature`; the features are guaranteed by the target, and
  `available()` is the constant `true`.
- CPU features, other AArch64 targets: `kernel!` gives `#[target_feature(enable = "neon,sha2")]`.
  Such a function can be called without `unsafe` only from another function with the same
  attribute; every kernel function has it (`compress_block`, `chain_all`, `enter`, `leave`,
  `lane_tick`, `lane_step`, `tick`, `period` through `kernel!`, and `run` through its own
  attribute at `:680`). The two entries from ordinary code are the `unsafe` calls of finding 1,
  each directly after `if !arm::available() { return … }`. This configuration compiles and
  passes the test suite (E4).
- The test module calls the wrappers after `assert!(arm::available())` (`:823`), and its
  `transmute`s are between `[u32; 4]` and `uint32x4_t`.

`haveSha2` and `available` in the top-level theorems: the six statements in
`lean-hw/Slhdsa/Theorems.lean` (a symbolic link to the default build's file) have no hypothesis
beyond `Room`, and none mentions `haveSha2`. It enters only through `available` in
`sha256.hw.compress`, `sha256.hw.chain_blocks` and `sha256.hw_active`, and is eliminated by a
case split. It is an `opaque` constant, not an axiom, and nothing in the reviewed files could
learn its value (no `native_decide`, no `implemented_by`). `sha256.compress` and
`hash.chain_blocks` in `lean-hw/Slhdsa/Funs.lean:540-547`, `:1616-1624` do call the hardware
functions, so the theorems are about the `hw-sha2` code. No hypothesis or constant makes a
headline theorem say less than its text, apart from finding 2, which is about what the model
leaves out.

### Part C — context-string security statements

Read: `Ideal/Realize/PureReduce.lean`, `PureForger.lean`, `FinalPure.lean`,
`Ideal/RustFinalClosedPure.lean`, the note in `security/IDEAL_STATUS.md`, and the definitions
they use in `Reduction/Bytes.lean`, `Reduction/External.lean`, `Ideal/Compose.lean`,
`Ideal/Core/Defs.lean`, `Ideal/Realize/Port.lean`, `Ideal/Realize/Final.lean`,
`Ideal/Realize/FinalCore.lean`, `Ideal/ComposeFinal.lean`, `Ideal/RustFinalClosed.lean`,
`E2E/Bytes.lean`, and VCVio's `SignatureAlg.lean` and `QueryBound/Basic.lean`.

- **The game is the standard one.** `sufP`/`eufP` (`PureForger.lean:75-80`) are the probability,
  over a uniform table `g` and the game's coins, that VCVio's `strongUnforgeableExperiment` /
  `unforgeableExperiment` returns `true` for `pureBytesAlg` at `primsG (liftC g)`. That experiment
  is: key generation, the forger with a logging signing oracle under the generated key pair,
  verification of its output, and freshness (`SignatureAlg.lean:222-227`, `:338-344`). SUF
  freshness is "the exact pair `((M, ctx), some σ)` was not returned"; EUF freshness is
  "`(M, ctx)` was not submitted". A forgery that keeps the message and changes the context
  counts.
- **The scheme is the pure interface.** `pureBytesAlg` (`Reduction/Bytes.lean:467-485`): signing
  `(M, ctx)` returns `none` if `|ctx| > 255` and otherwise draws `opt_rand` and returns
  `byteSignPure M ctx sk opt_rand`; verification is `byteVerifyPure`; `none` is rejected.
  Message is the first component and context the second throughout (`pureEncode mc =
  encodePureMessage mc.2 mc.1`, `isLongQP` on `mc.1`, `hout` on `z.1.1`). The scheme is complete
  at every table for contexts of at most 255 bytes (`pureBytesAlg_complete`, generic in the
  primitives), so verification is not trivially false.
- **The adversary class is the intended one.** `ForgerP` (`PureForger.lean:35-39`) is one
  program, with no table in its type, that gets the public-key bytes and has uniform sampling,
  the compression table on `Bytes 32 × Bytes 64`, and a signing oracle from `(message, context)`
  to `Option (List Byte)`; it outputs a pair and an optional signature. It is adaptive and
  randomised. `sufInst`/`eufInst` answer its compression queries with the same `g` the scheme
  uses and forward signing queries to the game's oracle (`instImpl`, `Core/Defs.lean:54-58`).
  Nothing restricts it beyond the four stated caps, and it is not disabled.
- **Hypotheses.** `hqf`, `hqs`, `hlong`, `hout` and one arithmetic inequality; all concern the
  forger. `IsQueryBoundP` is a worst-case bound over every path; `hout` ranges over `support`,
  i.e. every possible oracle answer. Both are as in the audited internal theorems and as
  `HANDOFF.md:38-40` says. None is unsatisfiable and none restates the conclusion. `pureAgree`
  (`PureReduce.lean:248-285`) is a definition whose fields are proved, not assumed.
- **The bound matches the documentation.** `FinalPure.lean:37-46` is `Final.lean:74-83` with
  `ℓ + 257` for `ℓ` in all five places it occurs (`itsrLc`, the last argument of `epsItsrF`,
  `QcAll` twice, `ellB`) and in `hQ`; `qf`, `qs` are unchanged. The numeric points require
  `ℓ + 257 ≤ 2^26`, which is the README's "messages up to 2^26 − 257 bytes".
  `rust_ideal_security_closed_pure` has the same three conjuncts as
  `rust_ideal_security_closed`, with `E2E.PureBytesEndToEnd` (about `slh_sign` / `slh_verify`),
  the equality of the scheme at the real table, and the bounds for `ForgerP`.
- **`ℓ + 257` is the right accounting.** The framed message is `[0, |ctx|] ++ ctx ++ M`
  (`encodePureMessage_ok_iff`), of length `|M| + |ctx| + 2 ≤ ℓ + 255 + 2`, with equality
  possible (`length_of_pureEncode`, `toI_long`, `toI_out`). `ℓ` bounds the message part only;
  the context is not counted, which the file headers say.
- **The reduction is tight and covers colliding framings.** `ForgerP.toI`
  (`PureForger.lean:99-109`) forwards sampling and compression queries one for one, turns a
  signing query with `|ctx| ≤ 255` into exactly one internal signing query on the framed
  message, answers `none` without a query otherwise, and outputs the framed pair. Hence the
  same `qf` and `qs` (`toI_port`, `toI_sign`). Freshness transfers by
  `pureEncode_injective` (`Reduction/External.lean:250-268`): two pairs with the same successful
  encoding are equal, because the length byte fixes `|ctx|` when it is below 256. So two
  different `(message, context)` pairs with contexts of at most 255 bytes never have the same
  framed message, and a pair with a longer context can be neither signed nor accepted
  (`verify_error`). No forgery of the external game is lost
  (`OptGuard.strongUnforgeableAdvantage_le`, `unforgeableAdvantage_le`).
- **The `IDEAL_STATUS.md` note** (lines 3–7) is accurate.

Points that are true and documented, repeated here because they bound what the statement means:
the table is a uniformly random function, not SHA-256's; `opt_rand` may depend only on
`(PK.seed, PK.root)`; `hout` excludes forgeries on messages longer than `ℓ`; a signing query
with an over-long context still counts towards `qs`; the Rust conjuncts and the security
conjunct share the scheme, not a security claim.

## Not done

- No run of `lake` or `lean`: see finding 5.
- The proofs were not read: not those in `lean-hw/Slhdsa/Proofs/Hw/`, nor the proof bodies of
  the Part C files beyond following their structure. The kernel checks those.
- The internal-interface theorems that the context-string statements reduce to
  (`suf_ideal_closed`, the realisers, `epsItsrF`, `polyP`, `QcAll`) were read as statements only,
  and their numeric points were not recomputed. They are the subject of
  `security/status/AUDIT-closed.md`.
- VCVio's `External.encodePureMessage` and `signPureWithRandomizer` were not read; I relied on
  the project's proved characterisation `encodePureMessage_ok_iff`.
- Arm's own site could not be read; the instruction pages come from a mirror of Arm's export.
- LLVM's lowering of the intrinsics was checked only by disassembling fourteen probes on one
  toolchain (E6) and by the processor record.
- No hardware other than one Apple M5 Ultra; no CPU without the instructions.
- Aeneas's and Charon's handling of `--opaque` and of the erased `unsafe` blocks was taken as
  given.
