# multi/ — SLH-DSA-SHA2, all six parameter sets: status

Self-contained copy of `rust/` and `lean/` extended from SLH-DSA-SHA2-128s to
SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}. Nothing outside `multi/` was
modified. Re-run everything with `multi/scripts/check.sh` (about 2.5 minutes
from a clean proof build on this machine; `check.sh full` also runs the slow
spec keygen/signing vectors).

## State: closed

Everything in the goal is done; there are no `sorry`s, no named hypotheses
standing in for unproven parts, and no unproven functions.

| Item | State |
|---|---|
| Spec parameterised by `Spec.Params`, six instances of Table 2, SHA-512, HMAC-SHA-512, §11.2.2 hash functions | done |
| Spec executable against NIST vectors, six sets | 34/34 per set: 28 verification, 2 keygen, 4 signing (one per signing group) |
| Rust generic over `&Params`, SHA-512, HMAC-SHA-512, MGF1 loop | done; all NIST ACVP non-pre-hash vectors pass for six sets |
| 128s identical to `../rust` | cross-test passes (keygen, sign, verdicts incl. corrupt/truncated signatures) |
| Aeneas extraction | no opaque functions, no axioms, no `FunsExternal` |
| Refinement proofs, every function, generic under `Spec.Params.Valid` | done |
| `Valid` holds for the six instances | proved (`Spec.sha2_*_valid`, `slhdsa.valid_*`) |
| Headline theorems, 5 per set + generic + sha256 + sha512 | 37 theorems, each `[propext, Classical.choice, Quot.sound]` |

## Design

- **Rust** (`rust/src`): one implementation taking `p: &Params` (`n, h, d, hp,
  a, k, m`; `lg_w = 4`, `w = 16`, `len_2 = 3` are constants since Table 2 fixes
  them). Hash values, keys and seeds are `&[u8]` / `Vec<u8>`. Derived sizes are
  methods (`len1`, `len`, `md_bytes`, `tree_bits`, `tree_bytes`, `leaf_bytes`,
  `xmss_sig_bytes`, `fors_sig_bytes`, `sig_bytes`). `sets.rs` instantiates the
  generic functions at each parameter set with fixed-size array key types
  (`sha2_128s::slh_keygen_internal(&[u8;16], …) -> ([u8;64],[u8;32])`, …), so
  the headline theorems have no length hypotheses. A runtime struct was chosen
  over const generics because key sizes `2n`, `4n` are not expressible with
  stable const generics and Aeneas translated the struct version with no
  opaque items on the first attempt.
- Hash selection branches on `p.n == 16` (public). `thash_f` = F/PRF (always
  SHA-256, `64 − n` zero bytes); `thash_h` = H/T_l (SHA-256 for n = 16, else
  SHA-512 with `128 − n` zero bytes); `prf_msg`, `h_msg` likewise; MGF1 is a
  real loop (128f has m = 34 > 32, two SHA-256 blocks).
- `digest_tree` masks with `u64::MAX >> (64 − (h − h'))` (256f has a 64-bit
  tree index). `ht_verify` compares roots with `util::bytes_eq` (OR of XORs).
  No secret-dependent branches or indices were introduced: all branches are on
  parameters, lengths, public digest digits and public indices, as before.
- SHA-512 uses a `u128` bit length, so its only precondition is that the
  padded buffer fits in memory.
- **Spec** (`lean/Spec`): `Sha512.lean` (FIPS 180-4 SHA-512, HMAC-SHA-512);
  `SlhDsa.lean` mirrors the original file with `(p : Params)` first on every
  function; `Params` has fields `n h d hp a k lgw m` (same names as VCVio's
  `Params` plus `m`), derived `w len1 len2 len mdBytes treeBytes leafBytes
  xmssSigBytes forsSigBytes sigBytes` computed by the formulas of the standard
  (`len2` with `Nat.log2`). `F`, `PRF`, `H`, `T`, `PRFmsg`, `Hmsg` follow
  §11.2.1 for `n = 16` and §11.2.2 otherwise; checked against the PDF
  (Table 2, §11.2.1, §11.2.2) rather than the task summary.
- **Validity predicate** `Spec.Params.Valid`: `n ∈ {16,24,32}`, `lgw = 4`,
  `2 ≤ d ≤ 22`, `1 ≤ h' ≤ 9`, `h = d·h'`, `h − h' ≤ 64`, `1 ≤ a ≤ 14`,
  `1 ≤ k ≤ 35`, `m = mdBytes + treeBytes + leafBytes`. Arithmetic, not an
  enumeration; the proofs are generic in it.
- **Proofs** (`lean/Slhdsa/Proofs`): `Basic`, `Params` (new), `Sha256`
  (unchanged), `Sha512` (new), `Hash`, `Util`, `Wots`, `Xmss`, `Fors`, `Ht`,
  `Slh`, `Sets` (new: the 30 typed instances), then `Theorems.lean`.

## Headline statements (`lean/Slhdsa/Theorems.lean`)

For each `S` in `sha2_128s … sha2_256f` with `N = n`, `PK = 2n`, `SK = 4n`:

```lean
theorem slhdsa.S.keygen_correct (sk_seed sk_prf pk_seed : Array U8 N#usize) :
    ∃ sk pk, sets.S.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      (bytes sk.val, bytes pk.val) =
        Spec.slhKeygenInternal Spec.S (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val)
theorem slhdsa.S.sign_internal_correct (m : Slice U8) (sk : Array U8 SK#usize)
    (addrnd : Array U8 N#usize) (hm : Room m.length 304) :
    ∃ sig, sets.S.slh_sign_internal m sk addrnd = ok sig ∧
      bytes sig.val = Spec.slhSignInternal Spec.S (bytes m.val) (bytes sk.val) (bytes addrnd.val)
theorem slhdsa.S.verify_internal_correct (m sig : Slice U8) (pk : Array U8 PK#usize)
    (hm : Room m.length 304) :
    sets.S.slh_verify_internal m sig pk =
      ok (Spec.slhVerifyInternal Spec.S (bytes m.val) (bytes sig.val) (bytes pk.val))
theorem slhdsa.S.sign_correct (m ctx : Slice U8) (sk : Array U8 SK#usize)
    (addrnd : Array U8 N#usize) (hm : Room m.length 561) :
    ∃ r, sets.S.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        Spec.slhSign Spec.S (bytes m.val) (bytes ctx.val) (bytes sk.val) (bytes addrnd.val)
theorem slhdsa.S.verify_correct (m sig ctx : Slice U8) (pk : Array U8 PK#usize)
    (hm : Room m.length 561) :
    sets.S.slh_verify m sig ctx pk =
      ok (Spec.slhVerify Spec.S (bytes m.val) (bytes sig.val) (bytes ctx.val) (bytes pk.val))
```

plus

```lean
theorem slhdsa.sha256_correct (msg : Slice U8) (h : Room msg.length 72) :
    ∃ d, sha256.sha256 msg = ok d ∧ bytes d.val = Spec.sha256 (bytes msg.val)
theorem slhdsa.sha512_correct (msg : Slice U8) (h : msg.length + 144 ≤ Usize.max) :
    ∃ d, sha512.sha512 msg = ok d ∧ bytes d.val = Spec.sha512 (bytes msg.val)
```

and `slhdsa.generic.{keygen,sign_internal,verify_internal,sign,verify}_correct`
for the slice-typed functions of `slh.rs`, for any `p` with
`(paramsS p).Valid`, with the key/seed lengths (`n`, `2n`, `4n`) as
hypotheses, since slices do not fix them. Verification is proven for every
byte string `sig` in both groups. `Room len slack` is unchanged:
`len + slack ≤ Usize.max ∧ len + slack < 2^61`.

## Tests

- `cargo test --release` (about 45 s): per set, keyGen 10/10, sigGen 28/28
  (deterministic and randomised, internal and pure interfaces), sigVer 28/28;
  SHA-256, SHA-512, HMAC-SHA-256/512 against the `sha2`/`hmac` crates; Table 2
  sizes; typed-module round trips and tamper tests for six sets; 128s
  cross-test against `../rust`.
- Lean spec executable (`lean/.lake/build/bin/spectest <set> [ver|all]`), per
  set: all 28 sigVer cases, the first 2 keyGen cases and the first case of
  each of the 4 sigGen groups, 0 failures in all six sets. `all` mode run
  times: 128f 110 s, 192f 219 s, 256f 406 s, 128s 33 min, 192s 65 min,
  256s 61 min. `ver` mode (what `check.sh` runs by default) takes seconds.
  The run also checks SHA-256/SHA-512 of "abc" and that `sigBytes`, `m`,
  `len1`, `len2`, `h = d·h'` computed from the record match Table 2.

## Build

```
multi/scripts/check.sh        # cargo test, extract, lake build, axiom audit, spec sigVer ×6
cd multi/lean && lake build   # proofs only; about 1 minute from clean (Mathlib/Aeneas prebuilt)
```

`multi/lean/.lake/packages` is an APFS clone of `lean/.lake/packages`; the
Aeneas library is used by path (`../../.tools/aeneas/backends/lean`).

## Not done / caveats

- The link to VCVio (`security/`) is not redone for the parameterised spec;
  that was out of scope. The spec keeps the structure of the original file to
  make it mechanical.
- The spec remains a hand transcription checked by vectors, as before.
- `Room` slack constants grew (152 → 304, 409 → 561) because SHA-512 pads and
  HMAC-SHA-512 keys are longer; one uniform constant is used for all six sets.
- Constant-time analysis was not run here; see Design for what was preserved.

## Swapping multi/ in for rust/ and lean/

1. Copy `multi/rust` → `rust`, `multi/lean/{Spec,Slhdsa,Spec.lean,Slhdsa.lean,SpecTest.lean}`
   → `lean`, `multi/vectors/*` → `vectors`, `multi/scripts/extract_vectors.py`
   → `scripts`. Keep the main tree's `lakefile.toml`, `scripts/extract.sh`
   (the `multi/` copies differ only in relative paths). Replace
   `scripts/check.sh` by the `multi/` one with paths adjusted, re-adding the
   `security` build.
2. In `rust/Cargo.toml` drop the dev-dependency `slhdsa_ref` (it points at the
   old crate) and delete the test `cross_128s_against_original_crate`.
3. Rust API change: `slhdsa::slh_keygen_internal` etc. become
   `slhdsa::sha2_128s::slh_keygen_internal` etc. (same signatures for 128s);
   the generic functions are `slhdsa::slh::*` with a leading `&Params`.
4. Statements in `lean/Slhdsa/Theorems.lean` that change shape (128s):
   - names: `slhdsa.keygen_correct` → `slhdsa.sha2_128s.keygen_correct`, and
     likewise `sign_internal_correct`, `verify_internal_correct`,
     `sign_correct`, `verify_correct`;
   - the Rust function: `slh.slh_keygen_internal` → `sets.sha2_128s.slh_keygen_internal` (etc.);
   - the spec function takes the parameter set: `Spec.slhKeygenInternal …` →
     `Spec.slhKeygenInternal Spec.sha2_128s …` (etc.);
   - `Room m.length 152` → `Room m.length 304`, `Room m.length 409` → `Room m.length 561`;
   - `sha256_correct` is unchanged; `sha512_correct` is new.
   Argument and result types (`Array U8 16/32/64`, `Slice U8`) are unchanged.
5. `security/Link` and `security/E2E` must be re-proved against the new spec:
   `Spec.n`, `Spec.len`, … are now `Spec.sha2_128s.n`, `.len`, …; `Spec.thash`
   is split into `Spec.F`/`PRF`/`H`/`T`; `Spec.mgf1` takes the hash and its
   output length; `Spec.block` takes `p`; `Spec.xmssSigBytes` etc. are
   `Spec.Params.xmssSigBytes`. For 128s every one of these unfolds to the old
   definition, so the existing Link lemmas should carry over after
   specialising at `Spec.sha2_128s`; the other five sets need
   `Spec.sha512`/`hmacSha512` linked to VCVio's SHA-512 first.
