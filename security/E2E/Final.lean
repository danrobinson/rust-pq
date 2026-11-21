import E2E.External
import Reduction.Headline

/-!
# End to end, final form: the Rust code and the phase-2 security theorems

(The documented headline is `E2E/FinalSplit.lean`: the same statements with the cross-arity
SM-TCR(`Thash`) term replaced by four per-function SM-TCR terms.  This file is unchanged.)

Attaches the final theorems of `Reduction/Headline.lean` to the Rust functions at
SLH-DSA-SHA2-128s, with the bounds written out term by term:

* `standard_model_security_final` — `slh_keygen_internal` / `slh_sign_internal` /
  `slh_verify_internal` (`EndToEnd`) with the SUF-CMA and the EUF-CMA bound for the internal
  scheme;
* `pure_standard_model_security_final` — `slh_sign` / `slh_verify` (`PureEndToEnd`) with the
  SUF-CMA and the EUF-CMA bound for the external pure scheme (context strings);
* `standard_model_resources_final`, `pure_standard_model_resources_final` — the resource counts
  of every adversary of the bounds, as numerals.

These supersede `E2E.standard_model_security` and `E2E.pure_standard_model_security` (which stay,
unchanged): the PRF game is on the secret-key address domain (the phase-1 game is false at
SHA2-128s), no adversary samples the eager `2^256`-cell table, the FORS-leaf term is
`SM-DSPR + 3·SM-TCR` on `F` instead of SM-DT-OpenPRE, and strong unforgeability is covered.
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open Link (vp prims)
open Reduction (bPrfC bPrfWC sufCheck rUd rPre rTcr toDspr toTcr externalAlg toInternal)
open Reduction.Lazy (bPrfMsgL bPrfMsgWL bItsrL bOpenPreS bTcrS bWotsS)
open TweakableHash

/-- **The Rust internal functions and standard-model SUF-CMA / EUF-CMA security, final form.**

Fix how `opt_rand` and `PK.seed` are sampled (`optRand`, `pkSeedDist`; arbitrary — deterministic
and hedged signing are both covered).  Let `S₀ = internalAlg vp prims optRand pkSeedDist`: FIPS 205
Algorithms 18–20 at SLH-DSA-SHA2-128s, with `SK.seed`, `SK.prf` uniform.

1. `EndToEnd optRand pkSeedDist`: the Rust `slh_keygen_internal`, `slh_sign_internal`,
   `slh_verify_internal` (Aeneas translation) never panic and compute the deterministic cores of
   `S₀.keygen`, `S₀.sign`, `S₀.verify` on the FIPS byte encodings.
2. **SUF-CMA.**  For every strong forger `S` against `S₀` (it wins with a valid
   `(message, signature)` pair that the signing oracle never returned; no bound on queries or
   running time), with `A = S.toUnforgeableAdversary` (the same program), the advantage is at
   most the sum of nine advantages in eight standard-model games on the SHA-256-based functions
   of `prims`:
   * PRF security of `prims.PRF` keyed by `SK.seed`, on inputs `(PK.seed, ADRS)` with `ADRS` a
     secret-key address of the parameter set (`Reduction.skPrfC`), and of `prims.PRFmsg`
     (HMAC-SHA-256) keyed by `SK.prf`;
   * interleaved target-subset resilience (ITSR) of `prims.Hmsg`;
   * for the tweakable hash `prims.Thash` under `pkSeedDist`: decisional second-preimage
     resistance (SM-DSPR, advantage `max 0 (Pr[DSPR] − Pr[SPprob])`) and, with coefficient 3,
     target-collision resistance (SM-TCR) of `F` at the `2^h·k·2^a` FORS leaves; SM-TCR of
     `Thash` over all hash calls of the key structure; undetectability (SM-UD, coefficient
     `w − 2 = 14`), preimage resistance (SM-PRE) and SM-TCR of `F` on the WOTS+ chains.
3. **EUF-CMA.**  For every chosen-message forger `A` against `S₀`, the same bound with the PRF
   distinguishers of the EUF-CMA check.

**What this does not say.**

* The nine advantages are *not* bounded here; that they are small for the SHA-256-based
  functions is an unproven cryptographic assumption.
* **No running-time claim.**  No adversary of the bound uses a choice principle or the eager
  `2^256`-cell table, and all have proved query/target/sample counts
  (`standard_model_resources_final`); the PRF, PRF_msg and ITSR adversaries are polynomial in the
  number `qs` of signing queries.  The six adversaries of the SM games walk the whole key
  structure (`≈ 2^68`–`2^80` targets, independent of `qs`), as in the paper's reduction, because
  the SM games register all targets before `PK.seed` is revealed.  Local computation is not
  counted here (VCVio has no cost model for it); it is not small: the SM-TCR(`Thash`) adversary
  also recomputes the whole key structure after the seed reveal (`≈ 2^79.81` own hash
  evaluations, `Reduction.Resources2.tcr_structure_exact`).
* One SM-TCR term on the variable-arity `Thash` (cross-arity collisions count) instead of the
  paper's four per-function terms (split in `E2E.standard_model_security_split`).  Single key.
* The Rust-level items are functional statements under the `Room` message-length bound; sampling
  `SK.seed`, `SK.prf` uniformly and `PK.seed`, `opt_rand` according to `pkSeedDist`, `optRand`
  is the caller's obligation.  Side channels, the Rust compiler and the Aeneas extraction are
  outside the statement. -/
theorem standard_model_security_final (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    EndToEnd optRand pkSeedDist ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfWC sufCheck S.toUnforgeableAdversary) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgWL sufCheck S.toUnforgeableAdversary) +
        KeyedHash.ITSRAdvantage (bItsrL S.toUnforgeableAdversary) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS S.toUnforgeableAdversary)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage
            (toTcr (bOpenPreS S.toUnforgeableAdversary))) +
        SM_DT_TCR_Advantage (bTcrS S.toUnforgeableAdversary) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS S.toUnforgeableAdversary)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS S.toUnforgeableAdversary)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS S.toUnforgeableAdversary))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfC A) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgL A) +
        KeyedHash.ITSRAdvantage (bItsrL A) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS A)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS A))) +
        SM_DT_TCR_Advantage (bTcrS A) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS A)) :=
  ⟨end_to_end optRand pkSeedDist,
    fun S => Reduction.slhdsa_sha2_128s_suf_cma_final optRand pkSeedDist S,
    fun A => Reduction.slhdsa_sha2_128s_euf_cma_final optRand pkSeedDist A⟩

/-- **The Rust public API and standard-model SUF-CMA / EUF-CMA security, final form.**

Let `X = Reduction.externalAlg vp prims optRand pkSeedDist`: the external pure interface of
SLH-DSA-SHA2-128s (FIPS 205 Algorithms 21, 22, 24) as a signature scheme on `(message, context)`
pairs, with signatures of type `Except External.Error _`.

1. `PureEndToEnd optRand pkSeedDist`: the Rust `slh_keygen_internal`, `slh_sign`, `slh_verify`
   never panic and compute the deterministic cores of `X.keygen`, `X.sign`, `X.verify` on the
   FIPS byte encodings, and `X` is correct.
2. **SUF-CMA.**  For every strong forger `S` against `X` — it gets the public key and a signing
   oracle for `(message, context)` pairs and wins with a `((message, context), signature)` pair
   that `X.verify` accepts and that the oracle never returned; the error value returned for a
   context of more than 255 bytes is never accepted, so it is never a forgery — the advantage is
   at most the bound of `standard_model_security_final` (item 2) at the internal forger
   `I = toInternal S.toUnforgeableAdversary`, which runs `S` once and makes at most as many
   signing queries.
3. **EUF-CMA.**  For every chosen-message forger `A` against `X` (a forgery is on a
   `(message, context)` pair never submitted), the bound of item 3 there at `toInternal A`.

Scope and caveats: pure mode only (not the pre-hash interfaces, and nothing about one key used
in both modes); single key; the game is on typed signatures and keys (byte-level parsing is
part of item 1); all caveats of `standard_model_security_final` carry over. -/
theorem pure_standard_model_security_final
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    PureEndToEnd optRand pkSeedDist ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary (externalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage
          (bPrfWC sufCheck (toInternal S.toUnforgeableAdversary)) +
        (Reduction.msgPrf vp prims).prfAdvantage
          (bPrfMsgWL sufCheck (toInternal S.toUnforgeableAdversary)) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal S.toUnforgeableAdversary)) +
        (SM_DT_DSPR_SourceFinalValidity.advantage
            (toDspr (bOpenPreS (toInternal S.toUnforgeableAdversary))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage
            (toTcr (bOpenPreS (toInternal S.toUnforgeableAdversary)))) +
        SM_DT_TCR_Advantage (bTcrS (toInternal S.toUnforgeableAdversary)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal S.toUnforgeableAdversary))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal S.toUnforgeableAdversary))) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS (toInternal S.toUnforgeableAdversary)))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (externalAlg vp prims optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfC (toInternal A)) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgL (toInternal A)) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal A)) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (toInternal A))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal A)))) +
        SM_DT_TCR_Advantage (bTcrS (toInternal A)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal A))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal A))) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS (toInternal A))) :=
  ⟨pure_end_to_end optRand pkSeedDist,
    fun S => Reduction.slhdsa_sha2_128s_pure_suf_cma_final optRand pkSeedDist S,
    fun A => Reduction.slhdsa_sha2_128s_pure_euf_cma_final optRand pkSeedDist A⟩

/-- **Resources of every adversary of the final bounds at SLH-DSA-SHA2-128s**, for an internal
forger with at most `qs` signing queries (for a strong forger `S` take
`A = S.toUnforgeableAdversary`, the same program).  See `Reduction.FinalResources` for the
fields and `Reduction.counts128s` for the numerals: `≤ 17920 + qs·182784` PRF queries / fresh
draws, `≤ qs` PRF_msg queries and ITSR targets, `≤ 269824 + qs·2007385` hash evaluations of the
lazy adversaries, `≤ 14·qs` openings — and, independently of `qs`, `14·2^75 ≈ 2^78.81` FORS-leaf
commitments/targets, `≈ 2^79.81` SM-TCR(Thash) targets, `≈ 2^63.003` WOTS+ instances,
`≈ 2^68.13` SM-UD/SM-PRE challenges, `≈ 2^72.04` SM-TCR(F) targets.  No running-time statement. -/
theorem standard_model_resources_final (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    Reduction.FinalResources A qs (Reduction.counts128s qs) :=
  Reduction.final_resources_128s optRand pkSeedDist A qs hA

/-- **Resources for the external interface**: if the external forger makes at most `qs` signing
queries, so does `toInternal A`, and the counts of `standard_model_resources_final` hold for
the adversaries built from it (for an external strong forger `S` take
`A = S.toUnforgeableAdversary`). -/
theorem pure_standard_model_resources_final
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary (externalAlg vp prims optRand pkSeedDist)) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    (∀ pk, IsQueryBoundP ((toInternal A).main pk) (fun i => i.isRight = true) qs) ∧
      Reduction.FinalResources (toInternal A) qs (Reduction.counts128s qs) :=
  ⟨Reduction.toInternal_queryBound A qs hA,
    Reduction.final_resources_128s optRand pkSeedDist (toInternal A) qs
      (Reduction.toInternal_queryBound A qs hA)⟩

end E2E

#print axioms E2E.standard_model_security_final
#print axioms E2E.pure_standard_model_security_final
#print axioms E2E.standard_model_resources_final
#print axioms E2E.pure_standard_model_resources_final
