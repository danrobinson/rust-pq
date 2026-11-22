# Package E (E2E) — report

Done for all six sets. `lake build ME2E` succeeds; no `sorry`/`axiom`/`native_decide`/`bv_decide`
in `ME2E/`; all 121 `#print axioms` lines of `ME2E` (13 generic + 18 per set) are within
`[propext, Classical.choice, Quot.sound]` (`wire_injective`, `wire_surjective`: `[propext, Quot.sound]`).
Nothing outside `ME2E/`, `ME2E.lean`, `status/E.md` was touched. No problem found in `lean`.

## Files

| file | content |
|---|---|
| `ME2E/Basic.lean` | generic over `S : MLink.Sha2Set`: `wire`, `node`, the five transfer lemmas `Spec` → byte cores, key parsing, `BytesScheme`/`PureBytesScheme` |
| `ME2E/Sha2_<set>.lean` (generated, six) | namespace `ME2E.sha2_<set>`: Rust = cores, `bytes_end_to_end`, `pure_bytes_end_to_end`, the ten headlines |
| `ME2E/gen/gen.py` | generator (not in the build); `python3 ME2E/gen/gen.py` from `security` rewrites the six files and `ME2E.lean` |
| `ME2E.lean` | root: imports the seven modules |

`ME2E/Basic.lean` imports `MLink.Sign` (not the root `MLink`), `MReduction.Instances`, `Reduction.Bytes`, `Slhdsa`.

## Generic part (`ME2E/Basic.lean`, `variable (S : Sha2Set)`)

```lean
def wire (l : List U8) : List SLHDSA.Byte := cv (bytes l)
theorem wire_length, wire_injective, wire_surjective
def nodeOfBytes (n : ℕ) (l : Spec.Bytes) : Bytes n
def node {N : Usize} (x : Array U8 N) : S.Node := nodeOfBytes S.vp.params.n (bytes x.val)
theorem nd_node {N} (x : Array U8 N) (h : N.val = S.vp.params.n) : nd (node S x) = bytes x.val

theorem keygen_transfer {N} (hN : N.val = S.vp.params.n) (sk_seed sk_prf pk_seed : Array U8 N) (sk pk : List U8)
    (h : (bytes sk, bytes pk) = Spec.slhKeygenInternal S.spec (bytes sk_seed.val) (bytes sk_prf.val) (bytes pk_seed.val)) :
    (wire pk, wire sk) = byteKeygen S.vp S.prims (codec S) (node S sk_seed) (node S sk_prf) (node S pk_seed)
theorem sign_transfer {N} (hN) (m sk sig : List U8) (addrnd : Array U8 N) (hsk : sk.length = 4 * S.spec.n)
    (h : bytes sig = Spec.slhSignInternal S.spec (bytes m) (bytes sk) (bytes addrnd.val)) :
    wire sig = byteSign S.vp S.prims (codec S) (wire m) (wire sk) (node S addrnd)
theorem verify_transfer (m sig pk : List U8) (hpk : pk.length = 2 * S.spec.n) :
    Spec.slhVerifyInternal S.spec (bytes m) (bytes sig) (bytes pk) =
      byteVerify S.vp S.prims (codec S) (wire m) (wire sig) (wire pk)
theorem signPure_transfer …  (r.map wire = byteSignPure … from r.map bytes = Spec.slhSign S.spec …)
theorem verifyPure_transfer … (Spec.slhVerify S.spec … = byteVerifyPure …)
theorem byteSign_length (m sk) (addrnd) (hsk : sk.length = 4 * S.spec.n) :
    (byteSign S.vp S.prims (codec S) m sk addrnd).length = S.spec.sigBytes
theorem decodePk_wire, decodeSk_wire     -- every 2n / 4n-byte string parses
theorem key_lengths, w_sub_two (= 14), sign_bad_pk
structure BytesScheme S optRand pkSeedDist      -- keygen_alg, sign_alg, sign_alg_bad, verify_alg, correct
structure PureBytesScheme S optRand pkSeedDist  -- keygen_alg, sign_alg, sign_alg_tooLong, verify_alg, correct
theorem bytes_scheme, pure_bytes_scheme         -- hold for every S, optRand, pkSeedDist
```
Completeness came generically (`Reduction.bytesAlg_perfectlyComplete`, `pureBytesAlg_complete`).
The transfer lemmas follow from package C's `keygen_eq_bytes`, `sign_eq_bytes`, `slhSign_eq_bytes` and B's
`verify_eq`, `slhVerify_eq`, as C predicted.

## Per set (`ME2E.sha2_<set>.*`, <set> ∈ 128s, 128f, 192s, 192f, 256s, 256f) — all proved

`rust_keygen_bytes`, `rust_sign_internal_bytes`, `rust_sign_internal_length`, `rust_verify_internal_bytes`,
`rust_sign_bytes`, `rust_verify_bytes`, `numerals`, `bytes_end_to_end`, `pure_bytes_end_to_end`, and the ten headlines
`rust_security`, `rust_pure_security`, `rust_security_linear`, `rust_pure_security_linear`,
`rust_security_deterministic`, `rust_security_hedged`, `rust_pure_security_deterministic`,
`rust_pure_security_hedged`, `rust_security_resources`, `rust_pure_security_resources`.

Numerals used per set (arrays seed/`addrnd`, pk, sk; signature bytes; `len`, `k`; `bTcrArM` phase-2 count):

| set | n | pk | sk | sig | len | k | resources last argument |
|---|---|---|---|---|---|---|---|
| 128s | 16 | 32 | 64 | 7856 | 35 | 14 | 269824 + qs·2007385 + 7857 |
| 128f | 16 | 32 | 64 | 17088 | 35 | 33 | 4216 + qs·108847 + 23741 |
| 192s | 24 | 48 | 96 | 16224 | 51 | 17 | 392704 + qs·3311666 + 11363 |
| 192f | 24 | 48 | 96 | 35664 | 51 | 33 | 6136 + qs·169105 + 34433 |
| 256s | 32 | 64 | 128 | 29792 | 67 | 22 | 257792 + qs·2791676 + 16887 |
| 256f | 32 | 64 | 128 | 49856 | 67 | 35 | 16112 + qs·327266 + 35043 |

`Room` slacks 304 (internal) and 561 (pure) at every set; `w − 2 = 14` at every set.

### `ME2E.sha2_192f.rust_security`, verbatim

```lean
theorem rust_security (optRand : PublicKeyCore Sha2Set.s192f.prims.core → ProbComp Sha2Set.s192f.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s192f.prims.PkSeed) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 24#usize,
        ∃ sk pk, slhdsa.sets.sha2_192f.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen Sha2Set.s192f.vp Sha2Set.s192f.prims (codec Sha2Set.s192f) (node Sha2Set.s192f sk_seed) (node Sha2Set.s192f sk_prf) (node Sha2Set.s192f pk_seed)) ∧
      (∀ (m : Slice U8) (sk : Array U8 96#usize) (addrnd : Array U8 24#usize),
        Room m.length 304 →
        ∃ sig, slhdsa.sets.sha2_192f.slh_sign_internal m sk addrnd = ok sig ∧
          wire sig.val = byteSign Sha2Set.s192f.vp Sha2Set.s192f.prims (codec Sha2Set.s192f) (wire m.val) (wire sk.val) (node Sha2Set.s192f addrnd)) ∧
      (∀ (m sig : Slice U8) (pk : Array U8 48#usize), Room m.length 304 →
        slhdsa.sets.sha2_192f.slh_verify_internal m sig pk =
          ok (byteVerify Sha2Set.s192f.vp Sha2Set.s192f.prims (codec Sha2Set.s192f) (wire m.val) (wire sig.val) (wire pk.val)))) ∧
    (∀ F : SignatureAlg.StrongUnforgeableAdversary
        (bytesAlg Sha2Set.s192f.vp Sha2Set.s192f.prims (codec Sha2Set.s192f) optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp F ≤
        (Reduction.skPrfC Sha2Set.s192f.vp Sha2Set.s192f.prims).prfAdvantage (bPrfWC sufCheck (bytesToTypedS F).toUnforgeableAdversary) +
        (Reduction.msgPrf Sha2Set.s192f.vp Sha2Set.s192f.prims).prfAdvantage (bPrfMsgWL sufCheck (bytesToTypedS F).toUnforgeableAdversary) +
        KeyedHash.ITSRAdvantage (bItsrL (bytesToTypedS F).toUnforgeableAdversary) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (bytesToTypedS F).toUnforgeableAdversary)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (bytesToTypedS F).toUnforgeableAdversary))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (bytesToTypedS F).toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM 2 (bytesToTypedS F).toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM 51 (bytesToTypedS F).toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM 33 (bytesToTypedS F).toUnforgeableAdversary)) +
        ((Sha2Set.s192f.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (bytesToTypedS F).toUnforgeableAdversary)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (bytesToTypedS F).toUnforgeableAdversary)) +
        SM_DT_TCR_Advantage (rTcrT (vp := Sha2Set.s192f.vp) pkSeedDist (bWotsS (bytesToTypedS F).toUnforgeableAdversary))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (bytesAlg Sha2Set.s192f.vp Sha2Set.s192f.prims (codec Sha2Set.s192f) optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        … the same twelve terms with bPrfC / bPrfMsgL and (bytesToTyped A) …
```
Proof: `⟨⟨rust_keygen_bytes, rust_sign_internal_bytes, rust_verify_internal_bytes⟩,
fun F => MReduction.slhdsa_sha2_192f_bytes_suf_cma_final optRand pkSeedDist F, fun A => …euf…⟩` — the written-out
sum with the numerals `51`, `33` is definitionally `betaSufFinalMemo …` (accepted by the kernel at all six sets).

### Statement shape versus the old `E2E.*`

The ten statements are produced from the text of `security/E2E/Headline.lean` by the substitutions in
`gen.py:tr`; `gen.py:check128s` asserts (at every run) that undoing them on the generated 128s statements returns the
old statements. So `ME2E.sha2_128s.rust_security` (and the other nine) differ from `E2E.rust_security` only in:
Rust function names (`slhdsa.sets.sha2_128s.slh_*` for `slhdsa.slh.slh_*`), `Room` slack (304/561 for 152/409),
spelling `Sha2Set.s128s.vp`/`.prims`/`codec Sha2Set.s128s`/`node Sha2Set.s128s x` for `vp`/`prims`/`codec128s`/`node x`
(definitionally equal: `MReduction/Instances.lean`), `MReduction.directCounts128s` for
`Reduction.Resources2.directCounts128s` (`rfl`, package D), forger variable `F` for `S`.
This is a textual check, not a Lean theorem (security's `E2E` cannot be imported here: name clashes).

## The remaining gap (docstring of every `rust_security`, items (i)–(vi), with the set's numbers)

(i) Sampling: seeds and `addrnd` are arguments of the Rust functions; the game samples them (`pkSeedDist`, uniform
`SK.seed`/`SK.prf`, `optRand`). (ii) `Room m.length 304` for internal sign/verify, `561` for `slh_sign`/`slh_verify`;
keygen unconditional. (iii) Fixed lengths: pk `[u8; 2n]`, sk `[u8; 4n]`, seeds `[u8; n]`; the scheme takes arbitrary
strings (wrong-length pk: verify rejects, sign returns `[]`; wrong-length sk: `[]`/`none`; every 2n/4n string parses,
no well-formedness check of the secret key). (iv) `U8` ↔ `UInt8` via `wire` (bijection), arrays ↔ `Vector UInt8 n`
via `node`; `(pk, sk)` vs `(sk, pk)`. (v) `B.sign` parses the pk only for `optRand`. (vi) Outside: the twelve
advantages are assumptions (per set: which of SHA-256 / SHA-512 each term is about, as in D's table), no running time,
single key, compiler, Aeneas extraction, side channels; pure mode only (no pre-hash).

Difference from the single-set development: in `rust` the signers return `Vec<u8>` (Aeneas
`alloc.vec.Vec U8`), not an array; the length (7856 … 49856) is the separate theorem `rust_sign_internal_length`.
The docstrings say so. (No length theorem was stated for the `Some` result of `slh_sign`.)

## Not done

- The random-oracle statements of the old `E2E/Main.lean` (`EndToEnd`, `end_to_end`, `end_to_end_verify`, with
  `securityBound`) and its typed-value forms (`rust_verify_internal`, `rust_keygen`, `rust_sign_internal(')`,
  `rust_sign`, `secretKey`) are not ported; D's `MLink.security_sha2` / `romScheme_map_romAnswer_sha2` would supply
  the ROM part. Only what the ten final headlines need was ported.
- The superseded intermediate forms (`E2E/Reduction.lean`, `External.lean`, `Final.lean`, `FinalSplit.lean`,
  `bytes_standard_model_security` with `bTcrArS`/`rTcr`, `counts128s` resources) are not ported.
- The 128s-shape check is textual (see above).
