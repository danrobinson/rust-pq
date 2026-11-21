import E2E.Bytes
import Reduction.ResourcesFinal

/-!
# The final end-to-end statements: the Rust functions and the security of the scheme they compute

Summary theorems of the whole development for SLH-DSA-SHA2-128s (existing E2E theorems are
unchanged and remain proved):

* `E2E.rust_security` — internal interface (`slh_keygen_internal`, `slh_sign_internal`,
  `slh_verify_internal`; FIPS 205 Alg. 18–20);
* `E2E.rust_pure_security` — external pure interface (`slh_sign`, `slh_verify`; Alg. 22/24);

each a conjunction of
(a) the pointwise equalities between the Aeneas-extracted Rust functions and the deterministic
    cores `byteKeygen`, `byteSign`, `byteVerify` (`byteSignPure`, `byteVerifyPure`) of the
    byte-level scheme in the game,
(b) the SUF-CMA bound for that byte-level scheme, twelve standard-model advantages written out,
    every SM game at its tight target cap, with the final adversaries (`bTcrArM`, `rTcrT`),
(c) the EUF-CMA bound, likewise;

* `E2E.rust_security_linear`, `E2E.rust_pure_security_linear` — the same with the linear
  (signed-pair) form of the bounds: no absolute values, no truncated subtraction;
* `E2E.rust_security_deterministic`, `E2E.rust_security_hedged`,
  `E2E.rust_pure_security_deterministic`, `E2E.rust_pure_security_hedged` — (b) and (c) for
  uniform `PK.seed` and the two FIPS choices of `opt_rand` (part (a) does not mention the
  sampling and is the same);
* `E2E.rust_security_resources`, `E2E.rust_pure_security_resources` — the resource bundle
  `Reduction.FinalResourcesFinal` at SHA2-128s numerals for the typed forger built from a
  byte-level forger with at most `qs` signing queries.

`w − 2 = 14`, `len = 35`, `k = 14` at this parameter set.
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims cv sp sigBytes pkBytes skBytes)
open Reduction (bPrfC bPrfWC sufCheck rUd rPre rTcrT toDspr toTcr toInternal bTcrArM codec128s
  byteKeygen byteSign byteVerify byteSignPure byteVerifyPure bytesAlg pureBytesAlg bytesToTyped
  bytesToTypedS pureBytesToTyped prfRealPr prfIdealPr msgRealPr msgIdealPr)
open Reduction.Lazy (bPrfMsgL bPrfMsgWL bItsrL bOpenPreS bWotsS)
open TweakableHash

/-- **The Rust internal functions and the standard-model security of the scheme they compute
(SLH-DSA-SHA2-128s, FIPS 205 Alg. 18–20) — final statement.**

Fix how `opt_rand` and `PK.seed` are sampled (`optRand`, `pkSeedDist`; arbitrary — for a
degenerate `pkSeedDist` the statement is about games with a known seed: still true, but the
assumptions are then implausible; see `rust_security_deterministic` / `_hedged` for uniform
`PK.seed`).  Let `B = Reduction.bytesAlg vp prims codec128s optRand pkSeedDist`, the signature
scheme on byte strings with

  `B.keygen = do pkSeed ← pkSeedDist; skSeed ← $ᵗ; skPrf ← $ᵗ; pure (byteKeygen skSeed skPrf pkSeed)`,
  `B.sign pk sk m = do addrnd ← optRand (parsed pk); pure (byteSign m sk addrnd)`,
  `B.verify pk m sig = pure (byteVerify m sig pk)`

(`bytes_end_to_end`: fields `keygen_alg`, `sign_alg`, `verify_alg`, and perfect completeness
`correct`).

(a) The Aeneas translations of the Rust `slh_keygen_internal`, `slh_sign_internal`,
    `slh_verify_internal` never panic and are **pointwise equal** to `byteKeygen`, `byteSign`,
    `byteVerify`, for all inputs under the `Room` length bound.
(b) For **every** strong forger `S` against `B` — it receives the 32 public-key bytes, has a
    signing oracle from message bytes to signature bytes, and wins if it outputs a message and a
    byte string that `byteVerify` accepts and that the oracle never returned for that message —
    the SUF-CMA advantage is at most the sum of twelve standard-model advantages:
    PRF on secret-key addresses, PRF_msg, ITSR, SM-DSPR(F) + 3·SM-TCR(F) at the FORS leaves,
    SM-TCR on `F`, `H`, `T_len`, `T_k` (each game capped at the exact number of calls of that
    function in the key structure), 14·SM-UD(F), SM-PRE(F), SM-TCR(F) on the WOTS+ chains
    (capped at `#inst·len·(w−1)`), each at an explicit adversary built from the typed forger
    `bytesToTypedS S` (one typed signing query per query of `S`).
(c) The same for every chosen-message forger `A` (EUF-CMA: the message was never queried).

Resources of the twelve adversaries: `rust_security_resources`.

**The remaining gap between "the scheme in the game" (`B`) and "the Rust functions"** — each
item checked against the statements of (a) and of `bytes_end_to_end`:

(i) *Sampling.*  `B.keygen` draws `PK.seed ← pkSeedDist` and `SK.seed`, `SK.prf` uniformly;
    `B.sign` draws `opt_rand ← optRand pk`.  The Rust functions take `sk_seed`, `sk_prf`,
    `pk_seed`, `addrnd` as *arguments* (quantified in (a)); no Rust code that samples them is
    covered.  The caller must supply them with the distributions of the game (for the
    deterministic variant: pass `addrnd = pk_seed`).
(ii) *Length bounds.*  The Rust equalities for signing and verification are under
    `Room m.length 152` (`m.length + 152 ≤ usize::MAX` and `< 2^61`); key generation has no
    side condition; `B` is defined on all byte strings.
(iii) *Fixed-length arrays.*  The Rust public key is a `[u8; 32]`, the secret key a `[u8; 64]`,
    the returned signature an array; `B` takes arbitrary byte strings.  On a public key that is
    not 32 bytes `B.verify` rejects (`Reduction.byteVerify_of_pk_length_ne`) and `B.sign`
    returns `[]` (`sign_bad_pk`); on a secret key that is not 64 bytes `byteSign` returns `[]`
    (`Reduction.byteSign_of_sk_length_ne`); `[]` is never accepted (`Reduction.byteVerify_nil`).
    Such inputs cannot be passed to the Rust functions and do not arise in the games (keys come
    from `B.keygen`).  Every 32-byte / 64-byte string parses (`Link.decodePk_ok`,
    `decodeSecretKey_wire`): no well-formedness of the secret key is checked — `byteSign` and
    the Rust signer use the `PK.seed`, `PK.root` stored in the secret key as they are.  The
    signature argument of the Rust verifier is a slice of any length, as in `B`.
(iv) *Byte representations.*  Rust bytes are Aeneas `U8`, the scheme's bytes Lean `UInt8`,
    identified by `wire = Link.cv ∘ slhdsa.bytes`, a length-preserving bijection of lists
    (`wire_length`, `wire_injective`, `wire_surjective`).  The 16-byte seed and `addrnd` arrays
    are read as `Vector UInt8 16` by `node` (`nd_node`: same bytes), which is the carrier of
    `prims.SkSeed`, `prims.SkPrf`, `prims.PkSeed`, `prims.Y`.  `byteKeygen` returns `(pk, sk)`,
    the Rust function `(sk, pk)`.  Every Rust `Result` is `ok` (no panic).
(v) *The public key in signing.*  `B.sign pk sk m` parses the public-key argument only to
    evaluate `optRand` on it; `slh_sign_internal` has no public-key argument.  In the games the
    two copies of `PK.seed` (in `pk` and in `sk`) agree, both coming from `byteKeygen`.
(vi) *Outside the statement.*  The twelve advantages on the right are not bounded (they are
    assumptions on the SHA-256-based functions of FIPS 205); no running-time claim (resources
    are counted in oracle queries, samples and hash evaluations; nine of the twelve adversaries
    walk the whole key structure); single key; the Rust compiler, the Aeneas extraction and
    side channels. -/
theorem rust_security (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
        ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 152 →
        ∃ sig, slhdsa.slh.slh_sign_internal m sk addrnd = ok sig ∧
          wire sig.val = byteSign vp prims codec128s (wire m.val) (wire sk.val) (node addrnd)) ∧
      (∀ (m sig : Slice U8) (pk : Array U8 32#usize), Room m.length 152 →
        slhdsa.slh.slh_verify_internal m sig pk =
          ok (byteVerify vp prims codec128s (wire m.val) (wire sig.val) (wire pk.val)))) ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (bytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfWC sufCheck (bytesToTypedS S).toUnforgeableAdversary) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgWL sufCheck (bytesToTypedS S).toUnforgeableAdversary) +
        KeyedHash.ITSRAdvantage (bItsrL (bytesToTypedS S).toUnforgeableAdversary) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (bytesToTypedS S).toUnforgeableAdversary)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (bytesToTypedS S).toUnforgeableAdversary))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (bytesToTypedS S).toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM 2 (bytesToTypedS S).toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM 35 (bytesToTypedS S).toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM 14 (bytesToTypedS S).toUnforgeableAdversary)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (bytesToTypedS S).toUnforgeableAdversary)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (bytesToTypedS S).toUnforgeableAdversary)) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (bytesToTypedS S).toUnforgeableAdversary))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (bytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfC (bytesToTyped A)) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgL (bytesToTyped A)) +
        KeyedHash.ITSRAdvantage (bItsrL (bytesToTyped A)) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (bytesToTyped A))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (bytesToTyped A)))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (bytesToTyped A)) +
          SM_DT_TCR_Advantage (bTcrArM 2 (bytesToTyped A)) +
          SM_DT_TCR_Advantage (bTcrArM 35 (bytesToTyped A)) +
          SM_DT_TCR_Advantage (bTcrArM 14 (bytesToTyped A))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (bytesToTyped A))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (bytesToTyped A))) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (bytesToTyped A))) :=
  ⟨⟨rust_keygen_bytes, rust_sign_internal_bytes, rust_verify_internal_bytes⟩,
    fun S => Reduction.slhdsa_sha2_128s_bytes_suf_cma_final optRand pkSeedDist S,
    fun A => Reduction.slhdsa_sha2_128s_bytes_euf_cma_final optRand pkSeedDist A⟩

/-- **The Rust public API and the standard-model security of the scheme it computes
(SLH-DSA-SHA2-128s, external pure interface, FIPS 205 Alg. 21/22/24) — final statement.**

Let `X = Reduction.pureBytesAlg vp prims codec128s optRand pkSeedDist`: messages are
`(message, context)` pairs of byte strings, a signature is `Option (List UInt8)` — the return
type of the Rust `slh_sign`, `none` for a context longer than 255 bytes — with key generation as
in `rust_security`, `X.sign pk sk (M, ctx) = do addrnd ← optRand (parsed pk);
pure (byteSignPure M ctx sk addrnd)` for `|ctx| ≤ 255` and `pure none` (nothing sampled)
otherwise, `X.verify pk (M, ctx) (some sig) = pure (byteVerifyPure M sig ctx pk)`, `none`
rejected (`pure_bytes_end_to_end`; complete for contexts of at most 255 bytes).

(a) The Rust `slh_keygen_internal`, `slh_sign`, `slh_verify` never panic and are pointwise equal
    to `byteKeygen`, `byteSignPure`, `byteVerifyPure` under `Room m.length 409` (the Rust
    `Option` of `slh_sign` is the scheme's `Option`).
(b) For every strong forger `S` against `X` — a forgery is `((message, context), some bytes)`
    accepted by `byteVerifyPure` and never returned for that pair; `none` is never accepted —
    the SUF-CMA advantage is at most the twelve advantages of `rust_security`, at the internal
    typed forger `toInternal (pureBytesToTyped S.toUnforgeableAdversary)` (at most one internal
    signing query per query of `S`; `Reduction.toInternal_pureBytesToTyped_queryBound`).
(c) The same for every chosen-message forger `A` (EUF-CMA).

The gap between `X` and the Rust functions is that of `rust_security`, items (i)–(vi), with
these changes: (ii) the `Room` slack is 409; (iii) `X.sign` returns `none` when the context is
over-long (before sampling; `byteSignPure` is `none` there for every `addrnd`,
`Reduction.byteSignPure_tooLong`) or the public key does not parse, and `byteSignPure` returns
`none` when the secret key is not 64 bytes; contexts are slices on the Rust side and arbitrary
byte strings in `X`.  Pure mode only: the pre-hash interface (`HashSLH-DSA`) and mixed use of
one key in both modes are not covered. -/
theorem rust_pure_security (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
        ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.slh.slh_sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node addrnd)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.slh.slh_verify m sig ctx pk =
          ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (pureBytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfWC sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgWL sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 2 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 35 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 14 (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (pureBytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfC (toInternal (pureBytesToTyped A))) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgL (toInternal (pureBytesToTyped A))) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal (pureBytesToTyped A))) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (toInternal (pureBytesToTyped A)))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal (pureBytesToTyped A))))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 2 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 35 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 14 (toInternal (pureBytesToTyped A)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) :=
  ⟨⟨rust_keygen_bytes, rust_sign_bytes, rust_verify_bytes⟩,
    fun S => Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_final optRand pkSeedDist S,
    fun A => Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_final optRand pkSeedDist A⟩

/-! ## Linear form -/

/-- **`rust_security` in linear (signed-pair) form.**  Same scheme, same games, same twelve
adversaries; the four distinguishing advantages are replaced by their two sides:

  `Adv + [Pr_ideal(PRF) + Pr_ideal(PRF_msg) + SPprob(DSPR) + 14·Pr_ideal(UD)]`
  `  ≤ Pr_real(PRF) + Pr_real(PRF_msg) + ITSR + (Succ(DSPR) + 3·TCR) + (four TCR) +`
  `      14·Pr_real(UD) + PRE + TCR`.

`prfRealPr B` / `prfIdealPr B`: probability that the PRF distinguisher `B` outputs `true` with
the real function resp. a lazy random function (`msgRealPr`, `msgIdealPr`: the same for
PRF_msg); `SM_DT_UD_RealSuccess` / `SM_DT_UD_IdealSuccess`: the SM-UD experiment in the real /
ideal world; `SM_DT_DSPR_SourceFinalValidity.Success` / `.SPProbability`: the DSPR experiment
and the second-preimage-existence experiment of the same adversary.  Every term is the
probability of `true` of an explicit experiment (`≤ 1`); there is no absolute value and no
truncated subtraction.  The absolute-value statement `rust_security` follows by cancelling the
finite left bracket (`Reduction.boundFinalTight_of_linear`). -/
theorem rust_security_linear (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
        ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 152 →
        ∃ sig, slhdsa.slh.slh_sign_internal m sk addrnd = ok sig ∧
          wire sig.val = byteSign vp prims codec128s (wire m.val) (wire sk.val) (node addrnd)) ∧
      (∀ (m sig : Slice U8) (pk : Array U8 32#usize), Room m.length 152 →
        slhdsa.slh.slh_verify_internal m sig pk =
          ok (byteVerify vp prims codec128s (wire m.val) (wire sig.val) (wire pk.val)))) ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (bytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
          (prfIdealPr (bPrfWC sufCheck (bytesToTypedS S).toUnforgeableAdversary) +
            msgIdealPr (bPrfMsgWL sufCheck (bytesToTypedS S).toUnforgeableAdversary) +
            SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr (bOpenPreS (bytesToTypedS S).toUnforgeableAdversary)) +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
              SM_DT_UD_IdealSuccess (rUd pkSeedDist (bWotsS (bytesToTypedS S).toUnforgeableAdversary))) ≤
        prfRealPr (bPrfWC sufCheck (bytesToTypedS S).toUnforgeableAdversary) +
        msgRealPr (bPrfMsgWL sufCheck (bytesToTypedS S).toUnforgeableAdversary) +
        KeyedHash.ITSRAdvantage (bItsrL (bytesToTypedS S).toUnforgeableAdversary) +
        (SM_DT_DSPR_SourceFinalValidity.Success (toDspr (bOpenPreS (bytesToTypedS S).toUnforgeableAdversary)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (bytesToTypedS S).toUnforgeableAdversary))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (bytesToTypedS S).toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM 2 (bytesToTypedS S).toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM 35 (bytesToTypedS S).toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArM 14 (bytesToTypedS S).toUnforgeableAdversary)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_RealSuccess (rUd pkSeedDist (bWotsS (bytesToTypedS S).toUnforgeableAdversary)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (bytesToTypedS S).toUnforgeableAdversary)) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (bytesToTypedS S).toUnforgeableAdversary))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (bytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A +
          (prfIdealPr (bPrfC (bytesToTyped A)) +
            msgIdealPr (bPrfMsgL (bytesToTyped A)) +
            SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr (bOpenPreS (bytesToTyped A))) +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
              SM_DT_UD_IdealSuccess (rUd pkSeedDist (bWotsS (bytesToTyped A)))) ≤
        prfRealPr (bPrfC (bytesToTyped A)) +
        msgRealPr (bPrfMsgL (bytesToTyped A)) +
        KeyedHash.ITSRAdvantage (bItsrL (bytesToTyped A)) +
        (SM_DT_DSPR_SourceFinalValidity.Success (toDspr (bOpenPreS (bytesToTyped A))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (bytesToTyped A)))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (bytesToTyped A)) +
          SM_DT_TCR_Advantage (bTcrArM 2 (bytesToTyped A)) +
          SM_DT_TCR_Advantage (bTcrArM 35 (bytesToTyped A)) +
          SM_DT_TCR_Advantage (bTcrArM 14 (bytesToTyped A))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_RealSuccess (rUd pkSeedDist (bWotsS (bytesToTyped A))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (bytesToTyped A))) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (bytesToTyped A))) :=
  ⟨⟨rust_keygen_bytes, rust_sign_internal_bytes, rust_verify_internal_bytes⟩,
    fun S => Reduction.slhdsa_bytes_suf_cma_linear_128s optRand pkSeedDist S,
    fun A => Reduction.slhdsa_bytes_euf_cma_linear_128s optRand pkSeedDist A⟩

/-- **`rust_pure_security` in linear (signed-pair) form** (legend: `rust_security_linear`). -/
theorem rust_pure_security_linear (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
        ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.slh.slh_sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node addrnd)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.slh.slh_verify m sig ctx pk =
          ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (pureBytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S +
          (prfIdealPr (bPrfWC sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
            msgIdealPr (bPrfMsgWL sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
            SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
              SM_DT_UD_IdealSuccess (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) ≤
        prfRealPr (bPrfWC sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        msgRealPr (bPrfMsgWL sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
        (SM_DT_DSPR_SourceFinalValidity.Success (toDspr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 2 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 35 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) +
          SM_DT_TCR_Advantage (bTcrArM 14 (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_RealSuccess (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (pureBytesAlg vp prims codec128s optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A +
          (prfIdealPr (bPrfC (toInternal (pureBytesToTyped A))) +
            msgIdealPr (bPrfMsgL (toInternal (pureBytesToTyped A))) +
            SM_DT_DSPR_SourceFinalValidity.SPProbability (toDspr (bOpenPreS (toInternal (pureBytesToTyped A)))) +
            ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
              SM_DT_UD_IdealSuccess (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped A))))) ≤
        prfRealPr (bPrfC (toInternal (pureBytesToTyped A))) +
        msgRealPr (bPrfMsgL (toInternal (pureBytesToTyped A))) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal (pureBytesToTyped A))) +
        (SM_DT_DSPR_SourceFinalValidity.Success (toDspr (bOpenPreS (toInternal (pureBytesToTyped A)))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal (pureBytesToTyped A))))) +
        (SM_DT_TCR_Advantage (bTcrArM 1 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 2 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 35 (toInternal (pureBytesToTyped A))) +
          SM_DT_TCR_Advantage (bTcrArM 14 (toInternal (pureBytesToTyped A)))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_RealSuccess (rUd pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) +
        SM_DT_TCR_Advantage (rTcrT (vp := vp) pkSeedDist (bWotsS (toInternal (pureBytesToTyped A)))) :=
  ⟨⟨rust_keygen_bytes, rust_sign_bytes, rust_verify_bytes⟩,
    fun S => Reduction.slhdsa_pure_bytes_suf_cma_linear_128s optRand pkSeedDist S,
    fun A => Reduction.slhdsa_pure_bytes_euf_cma_linear_128s optRand pkSeedDist A⟩

/-! ## Uniform `PK.seed`; deterministic and hedged `opt_rand`

Parts (b) and (c) at the FIPS 205 sampling: `PK.seed` uniform (in the scheme and in all twelve
games) and `opt_rand = PK.seed` (deterministic) or uniform and fresh per signature (hedged).
Part (a) of `rust_security` / `rust_pure_security` does not involve the sampling.  The bound is
`Reduction.betaSufFinalMemo` / `betaEufFinalMemo` at the displayed typed forger: by definition
the twelve terms written out in `rust_security`. -/

/-- **SUF-CMA and EUF-CMA of the byte-level scheme computed by the Rust code, internal interface;
uniform `PK.seed`; deterministic signing: `opt_rand = PK.seed` (`sha2RandomizerOfPkSeed` is the identity on `Bytes 16`, `Reduction.detRand_128s`).**  Instance of `rust_security` (b), (c), which hold for arbitrary
`pkSeedDist` and `optRand`. -/
theorem rust_security_deterministic :
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (bytesAlg vp prims codec128s
          (fun pk => (pure (sha2RandomizerOfPkSeed vp.params pk.pkSeed) : ProbComp prims.Y))
          ($ᵗ prims.PkSeed)),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        Reduction.betaSufFinalMemo (bytesToTypedS S).toUnforgeableAdversary) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (bytesAlg vp prims codec128s
          (fun pk => (pure (sha2RandomizerOfPkSeed vp.params pk.pkSeed) : ProbComp prims.Y))
          ($ᵗ prims.PkSeed)),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        Reduction.betaEufFinalMemo (bytesToTyped A) :=
  ⟨fun S => Reduction.slhdsa_sha2_128s_bytes_suf_cma_deterministic S,
    fun A => Reduction.slhdsa_sha2_128s_bytes_euf_cma_deterministic A⟩

/-- **SUF-CMA and EUF-CMA of the byte-level scheme computed by the Rust code, internal interface;
uniform `PK.seed`; hedged signing: `opt_rand` uniform, fresh per signature.**  Instance of `rust_security` (b), (c), which hold for arbitrary
`pkSeedDist` and `optRand`. -/
theorem rust_security_hedged :
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (bytesAlg vp prims codec128s
          (fun _ => $ᵗ prims.Y)
          ($ᵗ prims.PkSeed)),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        Reduction.betaSufFinalMemo (bytesToTypedS S).toUnforgeableAdversary) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (bytesAlg vp prims codec128s
          (fun _ => $ᵗ prims.Y)
          ($ᵗ prims.PkSeed)),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        Reduction.betaEufFinalMemo (bytesToTyped A) :=
  ⟨fun S => Reduction.slhdsa_sha2_128s_bytes_suf_cma_hedged S,
    fun A => Reduction.slhdsa_sha2_128s_bytes_euf_cma_hedged A⟩

/-- **SUF-CMA and EUF-CMA of the byte-level scheme computed by the Rust code, external pure interface;
uniform `PK.seed`; deterministic signing: `opt_rand = PK.seed` (`sha2RandomizerOfPkSeed` is the identity on `Bytes 16`, `Reduction.detRand_128s`).**  Instance of `rust_pure_security` (b), (c), which hold for arbitrary
`pkSeedDist` and `optRand`. -/
theorem rust_pure_security_deterministic :
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (pureBytesAlg vp prims codec128s
          (fun pk => (pure (sha2RandomizerOfPkSeed vp.params pk.pkSeed) : ProbComp prims.Y))
          ($ᵗ prims.PkSeed)),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        Reduction.betaSufFinalMemo (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (pureBytesAlg vp prims codec128s
          (fun pk => (pure (sha2RandomizerOfPkSeed vp.params pk.pkSeed) : ProbComp prims.Y))
          ($ᵗ prims.PkSeed)),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        Reduction.betaEufFinalMemo (toInternal (pureBytesToTyped A)) :=
  ⟨fun S => Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_deterministic S,
    fun A => Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_deterministic A⟩

/-- **SUF-CMA and EUF-CMA of the byte-level scheme computed by the Rust code, external pure interface;
uniform `PK.seed`; hedged signing: `opt_rand` uniform, fresh per signature.**  Instance of `rust_pure_security` (b), (c), which hold for arbitrary
`pkSeedDist` and `optRand`. -/
theorem rust_pure_security_hedged :
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (pureBytesAlg vp prims codec128s
          (fun _ => $ᵗ prims.Y)
          ($ᵗ prims.PkSeed)),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        Reduction.betaSufFinalMemo (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (pureBytesAlg vp prims codec128s
          (fun _ => $ᵗ prims.Y)
          ($ᵗ prims.PkSeed)),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        Reduction.betaEufFinalMemo (toInternal (pureBytesToTyped A)) :=
  ⟨fun S => Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_hedged S,
    fun A => Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_hedged A⟩

/-! ## Resources -/

/-- **Resources of the adversaries of `rust_security`**: if the byte-level forger makes at most
`qs` signing queries (on every public key), so does the typed forger `bytesToTyped A`, and the
resource bundle `Reduction.FinalResourcesFinal` holds for it with the SHA2-128s numerals (table
and formal/argued flags: `Reduction/ResourcesFinal.lean`), together with the tight caps of the
five re-capped games.  For a strong forger `S` use `A := S.toUnforgeableAdversary` (the same
program; `(bytesToTypedS S).toUnforgeableAdversary = bytesToTyped S.toUnforgeableAdversary` by
`rfl`). -/
theorem rust_security_resources (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary (bytesAlg vp prims codec128s optRand pkSeedDist))
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ pk, IsQueryBoundP ((bytesToTyped A).main pk) (fun i => i.isRight = true) qs) ∧
      Reduction.FinalResourcesFinal (bytesToTyped A) qs (Reduction.Resources2.directCounts128s qs)
        (269824 + qs * 2007385 + 7857) :=
  ⟨Reduction.bytesToTyped_queryBound A qs hA,
    (Reduction.final_resources_final_128s optRand pkSeedDist (bytesToTyped A) qs
      (Reduction.bytesToTyped_queryBound A qs hA)).1⟩

/-- **Resources of the adversaries of `rust_pure_security`.** -/
theorem rust_pure_security_resources (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary (pureBytesAlg vp prims codec128s optRand pkSeedDist))
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ pk, IsQueryBoundP ((toInternal (pureBytesToTyped A)).main pk)
        (fun i => i.isRight = true) qs) ∧
      Reduction.FinalResourcesFinal (toInternal (pureBytesToTyped A)) qs
        (Reduction.Resources2.directCounts128s qs) (269824 + qs * 2007385 + 7857) :=
  ⟨Reduction.toInternal_pureBytesToTyped_queryBound A qs hA,
    (Reduction.final_resources_final_128s optRand pkSeedDist (toInternal (pureBytesToTyped A)) qs
      (Reduction.toInternal_pureBytesToTyped_queryBound A qs hA)).1⟩

end E2E

#print axioms E2E.rust_security
#print axioms E2E.rust_pure_security
#print axioms E2E.rust_security_linear
#print axioms E2E.rust_pure_security_linear
#print axioms E2E.rust_security_deterministic
#print axioms E2E.rust_security_hedged
#print axioms E2E.rust_pure_security_deterministic
#print axioms E2E.rust_pure_security_hedged
#print axioms E2E.rust_security_resources
#print axioms E2E.rust_pure_security_resources
