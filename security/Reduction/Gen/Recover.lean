import Reduction.Gen.Final

/-!
# The existing headline theorems recovered from the general-spec theorems

Every general-spec theorem of `Reduction/Gen/Final.lean`, applied to an embedded classical forger
(`embedAdv ds A` / `embedAdvS ds S`), is the corresponding existing theorem: left sides by
`eufAdvG_embedAdv` / `sufAdvG_embedAdvS`, wrappers by naturality, right sides by `betaEufG_embed`,
`betaSufG_embed`, `lin*G_embed`.  The `…_recovered` theorems hold for every `ds`; the `…_viaG`
theorems instantiate `ds := noDs` (the empty sampling spec: then `noDs + unifSpec` has only the
uniform queries, the "`unifSpec` instance") and have LITERALLY the types of the existing theorems
(`type_of%`), so nothing drifts.

Note: the general-spec theorems are derived from the existing ones (derandomisation), so this is
a consistency check of the statements, not an independent proof.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction.Gen

attribute [local irreducible] arityTargets tcrTargets

set_option linter.unusedSectionVars false

/-- The empty sampling spec. -/
abbrev noDs : OracleSpec PEmpty.{1} := []ₒ

noncomputable instance : OracleSpec.AnswerMeasure noDs :=
  @PFunctor.AnswerMeasure.mk noDs.toPFunctor (fun _ ↦ ⊤) (fun d ↦ d.elim) (fun d ↦ d.elim)

instance (d : PEmpty.{1}) : Fintype (noDs.Range d) := d.elim

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

theorem slhdsa_euf_cma_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalMemo (A) := by
  have h := slhdsa_euf_cmaG ds hS (embedAdv ds A)
  rw [eufAdvG_embedAdv] at h
  exact h.trans (le_of_eq (betaEufG_embed ds (A)))

theorem slhdsa_euf_cma_linear_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A + linIdealEuf (A) ≤ linRealEuf (A) := by
  have h := slhdsa_euf_cma_linearG ds hS (embedAdv ds A)
  rw [eufAdvG_embedAdv] at h
  have e1 := linIdealEufG_embed ds (A)
  have e2 := linRealEufG_embed ds (A)
  change _ + linIdealEufG ds optRand pkSeedDist (fun pk ↦ embed ds ((A).main pk)) ≤
    linRealEufG ds optRand pkSeedDist (fun pk ↦ embed ds ((A).main pk)) at h
  rw [e1, e2] at h
  exact h

theorem slhdsa_suf_cma_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A ≤ betaSufFinalMemo (A.toUnforgeableAdversary) := by
  have h := slhdsa_suf_cmaG ds hS (embedAdvS ds A)
  rw [sufAdvG_embedAdvS] at h
  exact h.trans (le_of_eq (betaSufG_embed ds (A.toUnforgeableAdversary)))

theorem slhdsa_suf_cma_linear_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A + linIdealSuf (A.toUnforgeableAdversary) ≤ linRealSuf (A.toUnforgeableAdversary) := by
  have h := slhdsa_suf_cma_linearG ds hS (embedAdvS ds A)
  rw [sufAdvG_embedAdvS] at h
  have e1 := linIdealSufG_embed ds (A.toUnforgeableAdversary)
  have e2 := linRealSufG_embed ds (A.toUnforgeableAdversary)
  change _ + linIdealSufG ds optRand pkSeedDist (fun pk ↦ embed ds ((A.toUnforgeableAdversary).main pk)) ≤
    linRealSufG ds optRand pkSeedDist (fun pk ↦ embed ds ((A.toUnforgeableAdversary).main pk)) at h
  rw [e1, e2] at h
  exact h

theorem slhdsa_pure_euf_cma_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalMemo (toInternal A) := by
  have h := slhdsa_pure_euf_cmaG ds hS (embedAdv ds A)
  rw [eufAdvG_embedAdv, toInternalG_embed] at h
  exact h.trans (le_of_eq (betaEufG_embed ds (toInternal A)))

theorem slhdsa_pure_euf_cma_linear_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A + linIdealEuf (toInternal A) ≤ linRealEuf (toInternal A) := by
  have h := slhdsa_pure_euf_cma_linearG ds hS (embedAdv ds A)
  rw [eufAdvG_embedAdv, toInternalG_embed] at h
  have e1 := linIdealEufG_embed ds (toInternal A)
  have e2 := linRealEufG_embed ds (toInternal A)
  change _ + linIdealEufG ds optRand pkSeedDist (fun pk ↦ embed ds ((toInternal A).main pk)) ≤
    linRealEufG ds optRand pkSeedDist (fun pk ↦ embed ds ((toInternal A).main pk)) at h
  rw [e1, e2] at h
  exact h

theorem slhdsa_pure_suf_cma_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A ≤ betaSufFinalMemo (toInternal A.toUnforgeableAdversary) := by
  have h := slhdsa_pure_suf_cmaG ds hS (embedAdvS ds A)
  rw [sufAdvG_embedAdvS, toInternalSG_embed] at h
  exact h.trans (le_of_eq (betaSufG_embed ds (toInternal A.toUnforgeableAdversary)))

theorem slhdsa_pure_suf_cma_linear_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A + linIdealSuf (toInternal A.toUnforgeableAdversary) ≤ linRealSuf (toInternal A.toUnforgeableAdversary) := by
  have h := slhdsa_pure_suf_cma_linearG ds hS (embedAdvS ds A)
  rw [sufAdvG_embedAdvS, toInternalSG_embed] at h
  have e1 := linIdealSufG_embed ds (toInternal A.toUnforgeableAdversary)
  have e2 := linRealSufG_embed ds (toInternal A.toUnforgeableAdversary)
  change _ + linIdealSufG ds optRand pkSeedDist (fun pk ↦ embed ds ((toInternal A.toUnforgeableAdversary).main pk)) ≤
    linRealSufG ds optRand pkSeedDist (fun pk ↦ embed ds ((toInternal A.toUnforgeableAdversary).main pk)) at h
  rw [e1, e2] at h
  exact h

theorem slhdsa_bytes_euf_cma_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : BytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalMemo (bytesToTyped A) := by
  have h := slhdsa_bytes_euf_cmaG ds hS (embedAdv ds A)
  rw [eufAdvG_embedAdv, bytesToTypedG_embed] at h
  exact h.trans (le_of_eq (betaEufG_embed ds (bytesToTyped A)))

theorem slhdsa_bytes_euf_cma_linear_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : BytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A + linIdealEuf (bytesToTyped A) ≤ linRealEuf (bytesToTyped A) := by
  have h := slhdsa_bytes_euf_cma_linearG ds hS (embedAdv ds A)
  rw [eufAdvG_embedAdv, bytesToTypedG_embed] at h
  have e1 := linIdealEufG_embed ds (bytesToTyped A)
  have e2 := linRealEufG_embed ds (bytesToTyped A)
  change _ + linIdealEufG ds optRand pkSeedDist (fun pk ↦ embed ds ((bytesToTyped A).main pk)) ≤
    linRealEufG ds optRand pkSeedDist (fun pk ↦ embed ds ((bytesToTyped A).main pk)) at h
  rw [e1, e2] at h
  exact h

theorem slhdsa_bytes_suf_cma_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A ≤ betaSufFinalMemo ((bytesToTypedS A).toUnforgeableAdversary) := by
  have h := slhdsa_bytes_suf_cmaG ds hS (embedAdvS ds A)
  rw [sufAdvG_embedAdvS, bytesToTypedSG_embed] at h
  exact h.trans (le_of_eq (betaSufG_embed ds ((bytesToTypedS A).toUnforgeableAdversary)))

theorem slhdsa_bytes_suf_cma_linear_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A + linIdealSuf ((bytesToTypedS A).toUnforgeableAdversary) ≤ linRealSuf ((bytesToTypedS A).toUnforgeableAdversary) := by
  have h := slhdsa_bytes_suf_cma_linearG ds hS (embedAdvS ds A)
  rw [sufAdvG_embedAdvS, bytesToTypedSG_embed] at h
  have e1 := linIdealSufG_embed ds ((bytesToTypedS A).toUnforgeableAdversary)
  have e2 := linRealSufG_embed ds ((bytesToTypedS A).toUnforgeableAdversary)
  change _ + linIdealSufG ds optRand pkSeedDist (fun pk ↦ embed ds (((bytesToTypedS A).toUnforgeableAdversary).main pk)) ≤
    linRealSufG ds optRand pkSeedDist (fun pk ↦ embed ds (((bytesToTypedS A).toUnforgeableAdversary).main pk)) at h
  rw [e1, e2] at h
  exact h

theorem slhdsa_pure_bytes_euf_cma_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalMemo (toInternal (pureBytesToTyped A)) := by
  have h := slhdsa_pure_bytes_euf_cmaG ds hS (embedAdv ds A)
  rw [eufAdvG_embedAdv, pureBytesToTypedG_embed, toInternalG_embed] at h
  exact h.trans (le_of_eq (betaEufG_embed ds (toInternal (pureBytesToTyped A))))

theorem slhdsa_pure_bytes_euf_cma_linear_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A + linIdealEuf (toInternal (pureBytesToTyped A)) ≤ linRealEuf (toInternal (pureBytesToTyped A)) := by
  have h := slhdsa_pure_bytes_euf_cma_linearG ds hS (embedAdv ds A)
  rw [eufAdvG_embedAdv, pureBytesToTypedG_embed, toInternalG_embed] at h
  have e1 := linIdealEufG_embed ds (toInternal (pureBytesToTyped A))
  have e2 := linRealEufG_embed ds (toInternal (pureBytesToTyped A))
  change _ + linIdealEufG ds optRand pkSeedDist (fun pk ↦ embed ds ((toInternal (pureBytesToTyped A)).main pk)) ≤
    linRealEufG ds optRand pkSeedDist (fun pk ↦ embed ds ((toInternal (pureBytesToTyped A)).main pk)) at h
  rw [e1, e2] at h
  exact h

theorem slhdsa_pure_bytes_suf_cma_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A ≤ betaSufFinalMemo (toInternal (pureBytesToTyped A.toUnforgeableAdversary)) := by
  have h := slhdsa_pure_bytes_suf_cmaG ds hS (embedAdvS ds A)
  rw [sufAdvG_embedAdvS, pureBytesToTypedSG_embed, toInternalSG_embed] at h
  exact h.trans (le_of_eq (betaSufG_embed ds (toInternal (pureBytesToTyped A.toUnforgeableAdversary))))

theorem slhdsa_pure_bytes_suf_cma_linear_recovered {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A + linIdealSuf (toInternal (pureBytesToTyped A.toUnforgeableAdversary)) ≤ linRealSuf (toInternal (pureBytesToTyped A.toUnforgeableAdversary)) := by
  have h := slhdsa_pure_bytes_suf_cma_linearG ds hS (embedAdvS ds A)
  rw [sufAdvG_embedAdvS, pureBytesToTypedSG_embed, toInternalSG_embed] at h
  have e1 := linIdealSufG_embed ds (toInternal (pureBytesToTyped A.toUnforgeableAdversary))
  have e2 := linRealSufG_embed ds (toInternal (pureBytesToTyped A.toUnforgeableAdversary))
  change _ + linIdealSufG ds optRand pkSeedDist (fun pk ↦ embed ds ((toInternal (pureBytesToTyped A.toUnforgeableAdversary)).main pk)) ≤
    linRealSufG ds optRand pkSeedDist (fun pk ↦ embed ds ((toInternal (pureBytesToTyped A.toUnforgeableAdversary)).main pk)) at h
  rw [e1, e2] at h
  exact h

end Reduction.Gen

/-! ## The `unifSpec` instance: literally the existing statements -/

namespace Reduction.Gen

/-- `Reduction.slhdsa_bytes_suf_cma_final`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_bytes_suf_cma_final_viaG : type_of% @Reduction.slhdsa_bytes_suf_cma_final := by
  intros
  exact slhdsa_bytes_suf_cma_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_bytes_euf_cma_final`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_bytes_euf_cma_final_viaG : type_of% @Reduction.slhdsa_bytes_euf_cma_final := by
  intros
  exact slhdsa_bytes_euf_cma_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_pure_bytes_suf_cma_final`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_pure_bytes_suf_cma_final_viaG : type_of% @Reduction.slhdsa_pure_bytes_suf_cma_final := by
  intros
  exact slhdsa_pure_bytes_suf_cma_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_pure_bytes_euf_cma_final`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_pure_bytes_euf_cma_final_viaG : type_of% @Reduction.slhdsa_pure_bytes_euf_cma_final := by
  intros
  exact slhdsa_pure_bytes_euf_cma_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_suf_cma_final_memo`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_suf_cma_final_memo_viaG : type_of% @Reduction.slhdsa_suf_cma_final_memo := by
  intros
  exact slhdsa_suf_cma_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_euf_cma_final_memo`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_euf_cma_final_memo_viaG : type_of% @Reduction.slhdsa_euf_cma_final_memo := by
  intros
  exact slhdsa_euf_cma_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_pure_suf_cma_final_memo`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_pure_suf_cma_final_memo_viaG : type_of% @Reduction.slhdsa_pure_suf_cma_final_memo := by
  intros
  exact slhdsa_pure_suf_cma_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_pure_euf_cma_final_memo`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_pure_euf_cma_final_memo_viaG : type_of% @Reduction.slhdsa_pure_euf_cma_final_memo := by
  intros
  exact slhdsa_pure_euf_cma_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_bytes_suf_cma_linear`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_bytes_suf_cma_linear_viaG : type_of% @Reduction.slhdsa_bytes_suf_cma_linear := by
  intros
  exact slhdsa_bytes_suf_cma_linear_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_bytes_euf_cma_linear`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_bytes_euf_cma_linear_viaG : type_of% @Reduction.slhdsa_bytes_euf_cma_linear := by
  intros
  exact slhdsa_bytes_euf_cma_linear_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_pure_bytes_suf_cma_linear`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_pure_bytes_suf_cma_linear_viaG : type_of% @Reduction.slhdsa_pure_bytes_suf_cma_linear := by
  intros
  exact slhdsa_pure_bytes_suf_cma_linear_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_pure_bytes_euf_cma_linear`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_pure_bytes_euf_cma_linear_viaG : type_of% @Reduction.slhdsa_pure_bytes_euf_cma_linear := by
  intros
  exact slhdsa_pure_bytes_euf_cma_linear_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_suf_cma_final_linear`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_suf_cma_final_linear_viaG : type_of% @Reduction.slhdsa_suf_cma_final_linear := by
  intros
  exact slhdsa_suf_cma_linear_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_euf_cma_final_linear`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_euf_cma_final_linear_viaG : type_of% @Reduction.slhdsa_euf_cma_final_linear := by
  intros
  exact slhdsa_euf_cma_linear_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_pure_suf_cma_final_linear`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_pure_suf_cma_final_linear_viaG : type_of% @Reduction.slhdsa_pure_suf_cma_final_linear := by
  intros
  exact slhdsa_pure_suf_cma_linear_recovered noDs ‹_› ‹_›

/-- `Reduction.slhdsa_pure_euf_cma_final_linear`, re-derived as the `noDs` instance of the general-spec theorem. -/
theorem slhdsa_pure_euf_cma_final_linear_viaG : type_of% @Reduction.slhdsa_pure_euf_cma_final_linear := by
  intros
  exact slhdsa_pure_euf_cma_linear_recovered noDs ‹_› ‹_›

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms slhdsa_bytes_suf_cma_final_viaG
#print axioms slhdsa_bytes_euf_cma_final_viaG
#print axioms slhdsa_pure_bytes_suf_cma_final_viaG
#print axioms slhdsa_pure_bytes_euf_cma_final_viaG
#print axioms slhdsa_suf_cma_final_memo_viaG
#print axioms slhdsa_euf_cma_final_memo_viaG
#print axioms slhdsa_pure_suf_cma_final_memo_viaG
#print axioms slhdsa_pure_euf_cma_final_memo_viaG
#print axioms slhdsa_bytes_suf_cma_linear_viaG
#print axioms slhdsa_bytes_euf_cma_linear_viaG
#print axioms slhdsa_pure_bytes_suf_cma_linear_viaG
#print axioms slhdsa_pure_bytes_euf_cma_linear_viaG
#print axioms slhdsa_suf_cma_final_linear_viaG
#print axioms slhdsa_euf_cma_final_linear_viaG
#print axioms slhdsa_pure_suf_cma_final_linear_viaG
#print axioms slhdsa_pure_euf_cma_final_linear_viaG
end Axioms
