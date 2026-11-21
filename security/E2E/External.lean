import E2E.Reduction
import Reduction.External

/-!
# End to end, external interface: the Rust `slh_sign` / `slh_verify` and EUF-CMA security

The Rust crate's public API is the external *pure* interface with context strings (FIPS 205
Algorithms 22 and 24).  `Reduction.externalAlg` is that interface as a signature scheme over
`(message, context)` pairs, and `Reduction.slhdsa_pure_euf_cma` bounds the EUF-CMA advantage of
every forger against it.  This file attaches both to the Rust code at SLH-DSA-SHA2-128s:
`PureEndToEnd` (the functional link, from `E2E.rust_keygen`, `E2E.rust_sign`, `E2E.rust_verify`)
and `pure_standard_model_security` (link + security bound in one statement).
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims cv sigBytes pkBytes skBytes)
open Reduction (bPrf bPrfMsg bItsr bOpenPre bTcr bWots rUd rPre rTcr externalAlg toInternal)

/-- **The Rust external API computes the external pure scheme.**  Fix how `opt_rand` and
`PK.seed` are sampled (`optRand`, `pkSeedDist`; arbitrary).  Let
`X = Reduction.externalAlg vp prims optRand pkSeedDist`: FIPS 205 Algorithms 21/22/24 at
SLH-DSA-SHA2-128s as a signature scheme on `(message, context)` pairs, whose signatures are
`Except External.Error _` (an over-long context makes signing return an error value).

* `keygen_alg`, `keygen`: `X.keygen` draws `PK.seed ← pkSeedDist` and `SK.seed`, `SK.prf`
  uniformly and returns `keygenInternal` of them; on given seeds the Rust `slh_keygen_internal`
  returns the FIPS encodings of that key pair.
* `sign_alg`, `sign_alg_tooLong`, `sign`: for a context of at most 255 bytes `X.sign` draws
  `addrnd ← optRand pk` and returns `External.signPureWithRandomizer … addrnd`; for a longer
  context it returns the error.  On a given `addrnd`, the Rust `slh_sign` does not panic and
  returns `none` exactly when `signPureWithRandomizer` returns an error, and otherwise the FIPS
  encoding of its signature.
* `verify`: the Rust `slh_verify` does not panic and returns `b` with
  `X.verify k (M, ctx) (.ok s) = pure b` for the decoded signature `s` and public key `k`
  (`b = false` if the signature bytes have the wrong length).
* `correct`: `X` is a functioning scheme — for contexts of at most 255 bytes honest signatures
  under honestly generated keys verify.

All Rust-level items are functional statements about the Aeneas translation, under the `Room`
bound on the message length (length + 409 fits in `usize` and is below `2^61`). -/
structure PureEndToEnd (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : Prop where
  keygen_alg : (externalAlg vp prims optRand pkSeedDist).keygen = do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    pure (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed)
  keygen : ∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
    ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
      bytes sk.val =
        skBytes (GeneralScheme.keygenInternal vp prims (node sk_seed) (node sk_prf)
          (node pk_seed)).2 ∧
      bytes pk.val =
        pkBytes (GeneralScheme.keygenInternal vp prims (node sk_seed) (node sk_prf)
          (node pk_seed)).1
  sign_alg : ∀ pk sk (message context : List SLHDSA.Byte), context.length ≤ 255 →
    (externalAlg vp prims optRand pkSeedDist).sign pk sk (message, context) =
      (do let addrnd ← optRand pk
          pure (External.signPureWithRandomizer vp prims message context sk addrnd))
  sign_alg_tooLong : ∀ pk sk (message context : List SLHDSA.Byte), 255 < context.length →
    (externalAlg vp prims optRand pkSeedDist).sign pk sk (message, context) =
        pure (.error (.contextTooLong context.length)) ∧
      ∀ addrnd, External.signPureWithRandomizer vp prims message context sk addrnd =
        .error (.contextTooLong context.length)
  sign : ∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
    Room m.length 409 →
    ∃ r, slhdsa.slh.slh_sign m ctx sk addrnd = ok r ∧
      r.map (fun v => bytes v.val) =
        (External.signPureWithRandomizer vp prims (cv (bytes m.val)) (cv (bytes ctx.val))
          (secretKey sk) (node addrnd)).toOption.map sigBytes
  verify : ∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
    ∃ b, slhdsa.slh.slh_verify m sig ctx pk = ok b ∧
      match Link.decodeSig (cv (bytes sig.val)), Link.decodePk (cv (bytes pk.val)) with
      | .ok s, .ok k =>
        (externalAlg vp prims optRand pkSeedDist).verify k
          (cv (bytes m.val), cv (bytes ctx.val)) (.ok s) = pure b
      | _, _ => b = false
  correct : ∀ (message context : List SLHDSA.Byte), context.length ≤ 255 →
    ∀ (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) (addrnd : prims.Y),
    ∃ σ, External.signPureWithRandomizer vp prims message context
        (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).2 addrnd = .ok σ ∧
      (externalAlg vp prims optRand pkSeedDist).verify
        (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).1 (message, context) (.ok σ) =
          pure true

/-- `PureEndToEnd` holds for every `opt_rand` source and every `PK.seed` distribution. -/
theorem pure_end_to_end (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) : PureEndToEnd optRand pkSeedDist where
  keygen_alg := rfl
  keygen := rust_keygen
  sign_alg := fun pk sk message context h =>
    Reduction.externalAlg_sign vp prims optRand pkSeedDist pk sk message context h
  sign_alg_tooLong := fun pk sk message context h =>
    Reduction.externalAlg_sign_tooLong vp prims optRand pkSeedDist pk sk message context h
  sign := rust_sign
  verify := fun m sig ctx pk hm => by
    refine ⟨_, rust_verify m sig ctx pk hm, ?_⟩
    split
    · rename_i s k hs hk
      rw [hs, hk]
      exact Reduction.externalAlg_verify_ok vp prims optRand pkSeedDist k _ _ s
    · simp_all
  correct := fun message context hc skSeed skPrf pkSeed addrnd =>
    Reduction.externalAlg_correct vp prims optRand pkSeedDist message context hc skSeed skPrf
      pkSeed addrnd

/-- **The Rust public API and standard-model EUF-CMA security, in one statement.**
(Phase 1 form; superseded by `E2E.pure_standard_model_security_split` in `E2E/FinalSplit.lean`
(and `E2E.pure_standard_model_security_final` in `E2E/Final.lean`), which use the PRF game on
secret-key addresses, table-free adversaries, the FORS term `SM-DSPR + 3·SM-TCR`, and also cover
SUF-CMA.)

Fix how `opt_rand` and `PK.seed` are sampled (`optRand`, `pkSeedDist`; arbitrary — deterministic
and hedged signing are both covered).  Let `X = Reduction.externalAlg vp prims optRand
pkSeedDist`: the external pure interface of SLH-DSA-SHA2-128s (FIPS 205 Algorithms 21, 22, 24) as
a signature scheme whose messages are `(message, context)` pairs.

1. `PureEndToEnd optRand pkSeedDist`: the Rust `slh_keygen_internal`, `slh_sign`, `slh_verify`
   (Aeneas translation) never panic and compute the deterministic cores of `X.keygen`, `X.sign`,
   `X.verify` on the FIPS byte encodings, and `X` is correct (see `PureEndToEnd`).
2. For **every** chosen-message forger `A` against `X` (no bound on its queries or running
   time) — `A` gets the public key and a signing oracle for `(message, context)` pairs of its
   choice, and wins if it outputs a pair `(message, context)` it never submitted, with a
   signature that `X.verify` (i.e. `External.verifyPure`) accepts — its advantage is at most the
   sum of the eight standard-model advantages of `E2E.standard_model_security`, taken at the
   internal forger `Reduction.toInternal A`.  `toInternal A` is an explicit program: it runs `A`
   once, answers a signing query `(M, ctx)` by one query `0x00 ‖ |ctx| ‖ ctx ‖ M` to its own
   oracle (and by the error value, without a query, if `|ctx| > 255`), and so makes at most as
   many signing queries as `A` (`Reduction.toInternal_queryBound`).  The step from `X` to the
   internal scheme loses nothing and uses only injectivity of `(ctx, M) ↦ 0x00 ‖ |ctx| ‖ ctx ‖ M`
   for `|ctx| ≤ 255` (`Reduction.encodePureMessage_injective`).

**What is covered.**  Pure mode with arbitrary context strings: two different contexts for the
same message are different messages of the game, so a signature obtained for `(M, ctx)` is not a
forgery-free pass for `(M, ctx')`.

**What this does not say.**

* **Pure mode only.**  The pre-hash interfaces (`HashSLH-DSA`, FIPS 205 Algorithms 23/25) are
  not covered; nothing is proved about a signer that offers both pure and pre-hash signing under
  one key (domain separation between them is by the first byte `0x00`/`0x01` of `M'`, which this
  theorem does not use).
* **This theorem is EUF-CMA, not SUF-CMA**: a forgery must be on a `(message, context)` pair
  never submitted to the signing oracle; a new signature on a signed pair is not excluded by
  this statement (it is by the SUF-CMA item of `E2E.pure_standard_model_security_split`).
  Single key.
* The eight advantages are **not bounded here**: that PRF, ITSR, SM-OpenPRE, SM-TCR, SM-UD,
  SM-PRE advantages are small for the SHA-256-based functions of FIPS 205 §11.2.1 is an unproven
  cryptographic assumption.  No running-time claim is made for the reductions (five of them
  carry an eager `2^256`-indexed table; see `standard_model_security`).
* The Rust code computes only the deterministic cores.  Sampling `SK.seed`, `SK.prf` uniformly,
  and `PK.seed`, `opt_rand` according to `pkSeedDist`, `optRand`, is the caller's obligation and
  is not verified; for the assumptions to be plausible `pkSeedDist` must be (close to) uniform.
  The Rust `slh_keygen_internal` takes the seeds as inputs (there is no Rust function sampling
  them in the statement).
* The Rust-level items hold under the `Room` message-length bound; byte-level parsing of
  signatures and public keys is part of item 1 (`verify`), while the game of item 2 is on typed
  signatures and keys.  Side channels, the Rust compiler and the Aeneas extraction are outside
  the statement. -/
theorem pure_standard_model_security (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    PureEndToEnd optRand pkSeedDist ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (externalAlg vp prims optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrf vp prims).prfAdvantage (bPrf (toInternal A)) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsg (toInternal A)) +
        KeyedHash.ITSRAdvantage (bItsr (toInternal A)) +
        TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre (toInternal A)) +
        TweakableHash.SM_DT_TCR_Advantage (bTcr (toInternal A)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          TweakableHash.SM_DT_UD_Advantage (rUd pkSeedDist (bWots (toInternal A))) +
        TweakableHash.SM_DT_PRE_Advantage (rPre pkSeedDist (bWots (toInternal A))) +
        TweakableHash.SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots (toInternal A))) :=
  ⟨pure_end_to_end optRand pkSeedDist,
    fun A => Reduction.slhdsa_pure_euf_cma Reduction.structural_128s A⟩

/-- **Resources**: if the external forger makes at most `qs` signing queries, so does
`toInternal A`, and the `qs`-dependent reductions built from it obey the bounds of
`standard_model_resources`. -/
theorem pure_standard_model_resources (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary (externalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ pk, IsQueryBoundP ((toInternal A).main pk) (fun i => i.isRight = true) qs) ∧
      IsQueryBoundP (bPrf (toInternal A)) (fun i => i.isRight = true)
        (2 ^ vp.params.hp * vp.params.len + qs * Reduction.signReads vp) ∧
      IsQueryBoundP (bPrfMsg (toInternal A)) (fun i => i.isRight = true) qs ∧
      IsQueryBoundP (bItsr (toInternal A)).main (fun i => i.isRight = true) qs :=
  ⟨Reduction.toInternal_queryBound A qs hA,
    standard_model_resources optRand pkSeedDist (toInternal A) qs
      (Reduction.toInternal_queryBound A qs hA)⟩

end E2E

#print axioms E2E.pure_end_to_end
#print axioms E2E.pure_standard_model_security
#print axioms E2E.pure_standard_model_resources
