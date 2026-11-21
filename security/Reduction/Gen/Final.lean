import Reduction.Gen.Headline
import Reduction.HeadlineFinal

/-!
# Standard-model security of SLH-DSA against forgers over a general sampling spec

Headline theorems of package GEN.  The forger's private randomness is `ds + unifSpec` for an
arbitrary oracle spec `ds` with an `AnswerMeasure` and finite answer types; its advantage is
`eufAdvG ds A = 𝒟[SignatureAlg.unforgeableExperiment A] {true}` (VCVio's experiment for the scheme
`liftAlg ds alg`, VCVio's measure semantics), `sufAdvG` likewise.

* linear forms `slhdsa_{,pure_}{,bytes_}{euf,suf}_cma_linearG`;
* absolute-value forms `slhdsa_{,pure_}{,bytes_}{euf,suf}_cmaG` (right side `betaEufG`/`betaSufG`:
  the twelve wrapper-game advantages of the reduction adversaries around the forger);
* `betaEufG_embed`, `betaSufG_embed` and the `…_recovered` theorems: on classical forgers the
  general statements are the existing ones.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction.Gen

attribute [local irreducible] arityTargets tcrTargets

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

lemma simulateQ_idW {ιx : Type} {X : OracleSpec ιx} {α : Type} (t : OracleComp (unifSpec + X) α) :
    simulateQ (idW X) t = t := by
  induction t using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact bind_congr fun u ↦ ih u

/-! ## Typed internal scheme -/

/-- **EUF-CMA, linear form, forgers over `ds + unifSpec`.** -/
theorem slhdsa_euf_cma_linearG (hS : Structural vp prims)
    (A : GForger ds vp prims optRand pkSeedDist) :
    eufAdvG ds A + linIdealEufG ds optRand pkSeedDist A.main ≤
      linRealEufG ds optRand pkSeedDist A.main := by
  have key := lin_transfer_eufG (optRand := optRand) (pkSeedDist := pkSeedDist) ds (idW _) id id
    (fun F' ↦ eufAdvG ds (sigAlg := internalAlg vp prims optRand pkSeedDist) ⟨F'⟩)
    (isLin_eufAdvG ds _) (fun F₀ ↦ ?_) A.main
  · rw [wrapFam_id] at key; exact key
  · have hc : clsFam optRand pkSeedDist (idW _) id id F₀ =
        (⟨F₀⟩ : Forger vp prims optRand pkSeedDist) := by
      unfold clsFam
      congr 1
      funext pk
      simp [simulateQ_idW]
    rw [hc]
    have h1 := eufAdvG_embedAdv ds (⟨F₀⟩ : Forger vp prims optRand pkSeedDist)
    change eufAdvG ds (embedAdv ds (⟨F₀⟩ : Forger vp prims optRand pkSeedDist)) + _ ≤ _
    rw [h1]
    exact slhdsa_euf_cma_final_linear' hS ⟨F₀⟩

/-- **SUF-CMA, linear form, forgers over `ds + unifSpec`.** -/
theorem slhdsa_suf_cma_linearG (hS : Structural vp prims)
    (S : GStrongForger ds vp prims optRand pkSeedDist) :
    sufAdvG ds S + linIdealSufG ds optRand pkSeedDist S.main ≤
      linRealSufG ds optRand pkSeedDist S.main := by
  have key := lin_transfer_sufG (optRand := optRand) (pkSeedDist := pkSeedDist) ds (idW _) id id
    (fun F' ↦ sufAdvG ds (sigAlg := internalAlg vp prims optRand pkSeedDist) ⟨F'⟩)
    (isLin_sufAdvG ds _) (fun F₀ ↦ ?_) S.main
  · rw [wrapFam_id] at key; exact key
  · have hc : clsFam optRand pkSeedDist (idW _) id id F₀ =
        (⟨F₀⟩ : Forger vp prims optRand pkSeedDist) := by
      unfold clsFam
      congr 1
      funext pk
      simp [simulateQ_idW]
    rw [hc]
    have h1 := sufAdvG_embedAdvS ds
      (⟨F₀⟩ : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist))
    change sufAdvG ds (embedAdvS ds (⟨F₀⟩ :
      SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist))) + _ ≤ _
    rw [h1]
    exact slhdsa_suf_cma_final_linear' hS ⟨F₀⟩

/-- **EUF-CMA of SLH-DSA (typed internal algorithms) against forgers over `ds + unifSpec`.** -/
theorem slhdsa_euf_cmaG (hS : Structural vp prims) (A : GForger ds vp prims optRand pkSeedDist) :
    eufAdvG ds A ≤ betaEufG ds optRand pkSeedDist A.main :=
  boundFinalTightG_of_linear ds pkSeedDist _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_euf_cma_linearG ds hS A)

/-- **SUF-CMA of SLH-DSA (typed internal algorithms) against forgers over `ds + unifSpec`.** -/
theorem slhdsa_suf_cmaG (hS : Structural vp prims)
    (S : GStrongForger ds vp prims optRand pkSeedDist) :
    sufAdvG ds S ≤ betaSufG ds optRand pkSeedDist S.main :=
  boundFinalTightG_of_linear ds pkSeedDist _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_suf_cma_linearG ds hS S)

/-! ## External pure interface, byte-level schemes -/

/-- **EUF-CMA of the external pure interface (typed), linear form, forgers over `ds + unifSpec`.** -/
theorem slhdsa_pure_euf_cma_linearG (hS : Structural vp prims) (A : GExtForger ds vp prims optRand pkSeedDist) :
    eufAdvG ds A + linIdealEufG ds optRand pkSeedDist (toInternalG ds A).main ≤
      linRealEufG ds optRand pkSeedDist (toInternalG ds A).main :=
  (add_le_add (external_advantage_leG ds A) le_rfl).trans (slhdsa_euf_cma_linearG ds hS (toInternalG ds A))

/-- **EUF-CMA of the external pure interface (typed) against forgers over `ds + unifSpec`.** -/
theorem slhdsa_pure_euf_cmaG (hS : Structural vp prims) (A : GExtForger ds vp prims optRand pkSeedDist) :
    eufAdvG ds A ≤ betaEufG ds optRand pkSeedDist (toInternalG ds A).main :=
  boundFinalTightG_of_linear ds pkSeedDist _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_pure_euf_cma_linearG ds hS A)

/-- **SUF-CMA of the external pure interface (typed), linear form, forgers over `ds + unifSpec`.** -/
theorem slhdsa_pure_suf_cma_linearG (hS : Structural vp prims) (A : GExtStrongForger ds vp prims optRand pkSeedDist) :
    sufAdvG ds A + linIdealSufG ds optRand pkSeedDist (toInternalSG ds A).main ≤
      linRealSufG ds optRand pkSeedDist (toInternalSG ds A).main :=
  (add_le_add (external_strong_advantage_leG ds A) le_rfl).trans (slhdsa_suf_cma_linearG ds hS (toInternalSG ds A))

/-- **SUF-CMA of the external pure interface (typed) against forgers over `ds + unifSpec`.** -/
theorem slhdsa_pure_suf_cmaG (hS : Structural vp prims) (A : GExtStrongForger ds vp prims optRand pkSeedDist) :
    sufAdvG ds A ≤ betaSufG ds optRand pkSeedDist (toInternalSG ds A).main :=
  boundFinalTightG_of_linear ds pkSeedDist _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_pure_suf_cma_linearG ds hS A)

/-- **EUF-CMA of SLH-DSA on byte strings (internal algorithms), linear form, forgers over `ds + unifSpec`.** -/
theorem slhdsa_bytes_euf_cma_linearG (hS : Structural vp prims) (A : GBytesForger ds vp prims codec optRand pkSeedDist) :
    eufAdvG ds A + linIdealEufG ds optRand pkSeedDist (bytesToTypedG ds A).main ≤
      linRealEufG ds optRand pkSeedDist (bytesToTypedG ds A).main :=
  (add_le_add (bytes_advantage_leG ds A) le_rfl).trans (slhdsa_euf_cma_linearG ds hS (bytesToTypedG ds A))

/-- **EUF-CMA of SLH-DSA on byte strings (internal algorithms) against forgers over `ds + unifSpec`.** -/
theorem slhdsa_bytes_euf_cmaG (hS : Structural vp prims) (A : GBytesForger ds vp prims codec optRand pkSeedDist) :
    eufAdvG ds A ≤ betaEufG ds optRand pkSeedDist (bytesToTypedG ds A).main :=
  boundFinalTightG_of_linear ds pkSeedDist _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_bytes_euf_cma_linearG ds hS A)

/-- **SUF-CMA of SLH-DSA on byte strings (internal algorithms), linear form, forgers over `ds + unifSpec`.** -/
theorem slhdsa_bytes_suf_cma_linearG (hS : Structural vp prims) (A : GBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    sufAdvG ds A + linIdealSufG ds optRand pkSeedDist (bytesToTypedSG ds A).main ≤
      linRealSufG ds optRand pkSeedDist (bytesToTypedSG ds A).main :=
  (add_le_add (bytes_strong_advantage_leG ds A) le_rfl).trans (slhdsa_suf_cma_linearG ds hS (bytesToTypedSG ds A))

/-- **SUF-CMA of SLH-DSA on byte strings (internal algorithms) against forgers over `ds + unifSpec`.** -/
theorem slhdsa_bytes_suf_cmaG (hS : Structural vp prims) (A : GBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    sufAdvG ds A ≤ betaSufG ds optRand pkSeedDist (bytesToTypedSG ds A).main :=
  boundFinalTightG_of_linear ds pkSeedDist _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_bytes_suf_cma_linearG ds hS A)

/-- **EUF-CMA of the external pure interface on byte strings, linear form, forgers over `ds + unifSpec`.** -/
theorem slhdsa_pure_bytes_euf_cma_linearG (hS : Structural vp prims) (A : GPureBytesForger ds vp prims codec optRand pkSeedDist) :
    eufAdvG ds A + linIdealEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main ≤
      linRealEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main :=
  (add_le_add ((pure_bytes_advantage_leG ds A).trans (external_advantage_leG ds _)) le_rfl).trans (slhdsa_euf_cma_linearG ds hS (toInternalG ds (pureBytesToTypedG ds A)))

/-- **EUF-CMA of the external pure interface on byte strings against forgers over `ds + unifSpec`.** -/
theorem slhdsa_pure_bytes_euf_cmaG (hS : Structural vp prims) (A : GPureBytesForger ds vp prims codec optRand pkSeedDist) :
    eufAdvG ds A ≤ betaEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main :=
  boundFinalTightG_of_linear ds pkSeedDist _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_pure_bytes_euf_cma_linearG ds hS A)

/-- **SUF-CMA of the external pure interface on byte strings, linear form, forgers over `ds + unifSpec`.** -/
theorem slhdsa_pure_bytes_suf_cma_linearG (hS : Structural vp prims) (A : GPureBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    sufAdvG ds A + linIdealSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds A)).main ≤
      linRealSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds A)).main :=
  (add_le_add ((pure_bytes_strong_advantage_leG ds A).trans (external_strong_advantage_leG ds _)) le_rfl).trans (slhdsa_suf_cma_linearG ds hS (toInternalSG ds (pureBytesToTypedSG ds A)))

/-- **SUF-CMA of the external pure interface on byte strings against forgers over `ds + unifSpec`.** -/
theorem slhdsa_pure_bytes_suf_cmaG (hS : Structural vp prims) (A : GPureBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    sufAdvG ds A ≤ betaSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds A)).main :=
  boundFinalTightG_of_linear ds pkSeedDist _ _ _ _ _ _ _ _ _ _ _ _ (slhdsa_pure_bytes_suf_cma_linearG ds hS A)

/-! ## On classical forgers the general bound is the existing bound -/

theorem betaEufG_embed (A : Forger vp prims optRand pkSeedDist) :
    betaEufG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) = betaEufFinalMemo A := by
  unfold betaEufG boundFinalTightG betaEufFinalMemo boundFinalTight
  simp only [bPrfCG_embed, bPrfMsgLG_embed, bItsrLG_embed, toDsprG_embed, toTcrG_embed,
    bTcrArMG_embed, rUdG_embed, rPreG_embed, rTcrTG_embed, prfAdvantageG_embed,
    ITSRAdvantageG_ofClassical, dsprAdvantageG_ofClassical, tcrFVAdvantageG_ofClassical,
    SM_DT_TCR_AdvantageG_ofClassical, SM_DT_UD_AdvantageG_ofClassical,
    SM_DT_PRE_AdvantageG_ofClassical]

theorem betaSufG_embed (A : Forger vp prims optRand pkSeedDist) :
    betaSufG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) = betaSufFinalMemo A := by
  unfold betaSufG boundFinalTightG betaSufFinalMemo boundFinalTight
  simp only [bPrfWCG_embed, bPrfMsgWLG_embed, bItsrLG_embed, toDsprG_embed, toTcrG_embed,
    bTcrArMG_embed, rUdG_embed, rPreG_embed, rTcrTG_embed, prfAdvantageG_embed,
    ITSRAdvantageG_ofClassical, dsprAdvantageG_ofClassical, tcrFVAdvantageG_ofClassical,
    SM_DT_TCR_AdvantageG_ofClassical, SM_DT_UD_AdvantageG_ofClassical,
    SM_DT_PRE_AdvantageG_ofClassical]

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms slhdsa_euf_cma_linearG
#print axioms slhdsa_suf_cma_linearG
#print axioms slhdsa_euf_cmaG
#print axioms slhdsa_suf_cmaG
end Axioms
