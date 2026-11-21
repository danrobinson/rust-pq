import E2E.Final
import Reduction.HeadlineSplit

/-!
# End to end, headline form: the Rust code and the security theorems with per-function TCR terms

Attaches the theorems of `Reduction/HeadlineSplit.lean` to the Rust functions at
SLH-DSA-SHA2-128s, with the bounds written out term by term (twelve advantages):

* `standard_model_security_split` — `slh_keygen_internal` / `slh_sign_internal` /
  `slh_verify_internal` (`EndToEnd`) with the SUF-CMA and the EUF-CMA bound for the internal
  scheme;
* `pure_standard_model_security_split` — `slh_sign` / `slh_verify` (`PureEndToEnd`) with the
  SUF-CMA and the EUF-CMA bound for the external pure scheme (context strings);
* `tcr_split_targets_128s` — the target counts of the four class adversaries, as numerals
  (the other adversaries are those of `standard_model_resources_final`, unchanged).

Compared with `E2E/Final.lean` (which stays): the single SM-TCR term on the variable-arity
`Thash`, in which cross-arity collisions count, is replaced by four SM-TCR terms on `Thash`
restricted to inputs of `1`, `2`, `len = 35`, `k = 14` blocks, i.e. on the FIPS 205 functions
`F`, `H`, `T_len`, `T_k` (`Reduction.thashArityProblem`; a win is a second input of the same
length).  The `H` term covers the FORS-tree and the XMSS-tree nodes together, and the `F` term at
this place has no counterpart in the paper's bound; see `Reduction/HeadlineSplit.lean`.
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open Link (vp prims)
open Reduction (bPrfC bPrfWC sufCheck rUd rPre rTcr toDspr toTcr externalAlg toInternal bTcrArS)
open Reduction.Lazy (bPrfMsgL bPrfMsgWL bItsrL bOpenPreS bWotsS)
open TweakableHash

/-- **The Rust internal functions and standard-model SUF-CMA / EUF-CMA security, per-function
TCR terms.**  As `standard_model_security_final` (same `EndToEnd`, same games and adversaries for
the other eight terms, same caveats: the advantages on the right are not bounded here, no
running-time claim, single key), with the SM-TCR(`Thash`) term replaced by
`SM-TCR(F) + SM-TCR(H) + SM-TCR(T_len) + SM-TCR(T_k)` at the adversaries
`bTcrArS n ·`, `n = 1, 2, 35, 14`, each of which runs the sparse collision finder once and
registers only the arity-`n` hash calls of the key structure as targets.  These four are not
cheap in their own hashing either: after the seed is revealed each recomputes the whole key
structure (`≈ 2^79.81` own hash evaluations, `Reduction.Resources2.tcr_structure_exact`). -/
theorem standard_model_security_split (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    EndToEnd optRand pkSeedDist ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfWC sufCheck S.toUnforgeableAdversary) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgWL sufCheck S.toUnforgeableAdversary) +
        KeyedHash.ITSRAdvantage (bItsrL S.toUnforgeableAdversary) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS S.toUnforgeableAdversary)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS S.toUnforgeableAdversary))) +
        (SM_DT_TCR_Advantage (bTcrArS 1 S.toUnforgeableAdversary) + SM_DT_TCR_Advantage (bTcrArS 2 S.toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArS 35 S.toUnforgeableAdversary) + SM_DT_TCR_Advantage (bTcrArS 14 S.toUnforgeableAdversary)) +
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
        (SM_DT_TCR_Advantage (bTcrArS 1 A) + SM_DT_TCR_Advantage (bTcrArS 2 A) +
          SM_DT_TCR_Advantage (bTcrArS 35 A) + SM_DT_TCR_Advantage (bTcrArS 14 A)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS A)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS A)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS A)) :=
  ⟨end_to_end optRand pkSeedDist,
    fun S => Reduction.slhdsa_sha2_128s_suf_cma_final_split optRand pkSeedDist S,
    fun A => Reduction.slhdsa_sha2_128s_euf_cma_final_split optRand pkSeedDist A⟩

/-- **The Rust public API and standard-model SUF-CMA / EUF-CMA security, per-function TCR
terms.**  As `pure_standard_model_security_final` (external pure interface, FIPS 205
Algorithms 21, 22, 24, `(message, context)` pairs; same `PureEndToEnd`, same caveats), with the
bounds of `standard_model_security_split` at the internal forger `toInternal ·`. -/
theorem pure_standard_model_security_split
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    PureEndToEnd optRand pkSeedDist ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary (externalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfWC sufCheck (toInternal S.toUnforgeableAdversary)) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgWL sufCheck (toInternal S.toUnforgeableAdversary)) +
        KeyedHash.ITSRAdvantage (bItsrL (toInternal S.toUnforgeableAdversary)) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS (toInternal S.toUnforgeableAdversary))) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS (toInternal S.toUnforgeableAdversary)))) +
        (SM_DT_TCR_Advantage (bTcrArS 1 (toInternal S.toUnforgeableAdversary)) + SM_DT_TCR_Advantage (bTcrArS 2 (toInternal S.toUnforgeableAdversary)) +
          SM_DT_TCR_Advantage (bTcrArS 35 (toInternal S.toUnforgeableAdversary)) + SM_DT_TCR_Advantage (bTcrArS 14 (toInternal S.toUnforgeableAdversary))) +
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
        (SM_DT_TCR_Advantage (bTcrArS 1 (toInternal A)) + SM_DT_TCR_Advantage (bTcrArS 2 (toInternal A)) +
          SM_DT_TCR_Advantage (bTcrArS 35 (toInternal A)) + SM_DT_TCR_Advantage (bTcrArS 14 (toInternal A))) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS (toInternal A))) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS (toInternal A))) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS (toInternal A))) :=
  ⟨pure_end_to_end optRand pkSeedDist,
    fun S => Reduction.slhdsa_sha2_128s_pure_suf_cma_final_split optRand pkSeedDist S,
    fun A => Reduction.slhdsa_sha2_128s_pure_euf_cma_final_split optRand pkSeedDist A⟩

/-- **Targets of the four class adversaries at SLH-DSA-SHA2-128s.**  In its class game,
`bTcrArS n A` runs the `choose` phase of the sparse collision finder once (first item, for every
`n`); the challenge oracle then holds exactly the arity-`n` hash calls of the key structure:

* `F` (`n = 1`): `533756792467910173399552 ≈ 2^78.82` (FORS leaves and WOTS+ chain steps);
* `H` (`n = 2`): `528785142244921151848447 ≈ 2^78.81` (FORS-tree and XMSS-tree nodes);
* `T_len` (`n = 35`): `9241421688590303744 ≈ 2^63.003`;
* `T_k` (`n = 14`): `9223372036854775808 = 2^63`;

together the `1062560399506556770327551 ≈ 2^79.81` calls of the structure; the calls of the other
arities go to the collection oracle.  Independent of the number of signing queries. -/
theorem tcr_split_targets_128s (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    (∀ n pk, (simulateQ (SM_DT_TCR_oracles (Reduction.thashArityProblem vp prims pkSeedDist n) pk)
        (bTcrArS n A).choose).run ([], []) =
      (fun tbl => ((tbl, Reduction.honestCalls tbl pk),
        Reduction.TcrSplit.gState (fun xs => xs.length = n) (Reduction.honestCalls tbl pk))) <$>
          Reduction.Lazy.sparseTable vp prims) ∧
    ∀ (tbl : Reduction.SecretTable vp prims) (pk : prims.PkSeed),
      (Reduction.TcrSplit.gState (fun xs => xs.length = 1)
        (Reduction.honestCalls tbl pk)).1.length = 533756792467910173399552 ∧
      (Reduction.TcrSplit.gState (fun xs => xs.length = 2)
        (Reduction.honestCalls tbl pk)).1.length = 528785142244921151848447 ∧
      (Reduction.TcrSplit.gState (fun xs => xs.length = 35)
        (Reduction.honestCalls tbl pk)).1.length = 9241421688590303744 ∧
      (Reduction.TcrSplit.gState (fun xs => xs.length = 14)
        (Reduction.honestCalls tbl pk)).1.length = 9223372036854775808 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := Reduction.arityTargets_128s
  refine ⟨fun n pk => Reduction.bTcrArS_choose_run Reduction.structural_128s n A pk,
    fun tbl pk => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (Reduction.bTcrArS_targets Reduction.structural_128s 1 tbl pk).1.trans h1
  · exact (Reduction.bTcrArS_targets Reduction.structural_128s 2 tbl pk).1.trans h2
  · exact (Reduction.bTcrArS_targets Reduction.structural_128s 35 tbl pk).1.trans h3
  · exact (Reduction.bTcrArS_targets Reduction.structural_128s 14 tbl pk).1.trans h4

end E2E

#print axioms E2E.standard_model_security_split
#print axioms E2E.pure_standard_model_security_split
#print axioms E2E.tcr_split_targets_128s
