import Reduction.Gen.Recover
import Reduction.Gen.ResourcesB

/-!
# Corollaries: fixing the `ds`-coins; SLH-DSA-SHA2-128s

* `exists_resolution_euf` / `_suf`: for every forger over `ds + unifSpec` there is a CLASSICAL
  forger, obtained by fixing an answer at every `ds`-query (`IsResolution`; same signing-query
  bound, `IsResolution.queryBound`), whose advantage in VCVio's own game is at least as large.
  Hence the general-spec advantage is also bounded by the EXISTING bound (VCVio's games, no
  wrapper game) at that classical forger: `slhdsa_euf_cma_resolved`, `slhdsa_suf_cma_resolved`.
* `slhdsa_sha2_128s_*G`: the general-spec headlines at SLH-DSA-SHA2-128s (no hypothesis).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction.Gen

attribute [local irreducible] arityTargets tcrTargets

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]

section generic

variable {M PK SK S : Type} {sigAlg : SignatureAlg ProbComp M PK SK S}

/-- **Fixing the coins (EUF-CMA).** -/
theorem exists_resolution_euf (A : SignatureAlg.UnforgeableAdversary (liftAlg ds sigAlg)) :
    ∃ A₀ : SignatureAlg.UnforgeableAdversary sigAlg,
      (∀ pk, IsResolution ds (A.main pk) (A₀.main pk)) ∧
        eufAdvG ds A ≤ SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A₀ := by
  obtain ⟨F₀, hres, h⟩ := IsLin.le_resolution ds (wOf_sum ds) ENNReal.one_ne_top
    (isLin_eufAdvG ds sigAlg) A.main
  refine ⟨⟨F₀⟩, hres, ?_⟩
  have h1 := eufAdvG_embedAdv ds (⟨F₀⟩ : SignatureAlg.UnforgeableAdversary sigAlg)
  exact h.trans (le_of_eq h1)

/-- **Fixing the coins (SUF-CMA).** -/
theorem exists_resolution_suf (A : SignatureAlg.StrongUnforgeableAdversary (liftAlg ds sigAlg)) :
    ∃ A₀ : SignatureAlg.StrongUnforgeableAdversary sigAlg,
      (∀ pk, IsResolution ds (A.main pk) (A₀.main pk)) ∧
        sufAdvG ds A ≤ SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp A₀ := by
  obtain ⟨F₀, hres, h⟩ := IsLin.le_resolution ds (wOf_sum ds) ENNReal.one_ne_top
    (isLin_sufAdvG ds sigAlg) A.main
  refine ⟨⟨F₀⟩, hres, ?_⟩
  have h1 := sufAdvG_embedAdvS ds (⟨F₀⟩ : SignatureAlg.StrongUnforgeableAdversary sigAlg)
  exact h.trans (le_of_eq h1)

end generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- EUF-CMA against forgers over `ds + unifSpec`, right-hand side in VCVio's own games at a
classical forger obtained by fixing the `ds`-coins. -/
theorem slhdsa_euf_cma_resolved (hS : Structural vp prims)
    (A : GForger ds vp prims optRand pkSeedDist) :
    ∃ A₀ : Forger vp prims optRand pkSeedDist,
      (∀ pk, IsResolution ds (A.main pk) (A₀.main pk)) ∧ eufAdvG ds A ≤ betaEufFinalMemo A₀ := by
  obtain ⟨A₀, hres, h⟩ := exists_resolution_euf ds A
  exact ⟨A₀, hres, h.trans (slhdsa_euf_cma_final_memo' hS A₀)⟩

/-- SUF-CMA against forgers over `ds + unifSpec`, right-hand side in VCVio's own games at a
classical forger obtained by fixing the `ds`-coins. -/
theorem slhdsa_suf_cma_resolved (hS : Structural vp prims)
    (S : GStrongForger ds vp prims optRand pkSeedDist) :
    ∃ S₀ : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      (∀ pk, IsResolution ds (S.main pk) (S₀.main pk)) ∧
        sufAdvG ds S ≤ betaSufFinalMemo S₀.toUnforgeableAdversary := by
  obtain ⟨S₀, hres, h⟩ := exists_resolution_suf ds S
  exact ⟨S₀, hres, h.trans (slhdsa_suf_cma_final_memo' hS S₀)⟩

end Reduction.Gen

/-! ## SLH-DSA-SHA2-128s -/

namespace Reduction.Gen

variable {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
  [∀ d, Fintype (ds.Range d)]
  (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
  (pkSeedDist : ProbComp Link.prims.PkSeed)

theorem slhdsa_sha2_128s_bytes_suf_cmaG
    (S : GBytesStrongForger ds Link.vp Link.prims codec128s optRand pkSeedDist) :
    sufAdvG ds S ≤ betaSufG ds optRand pkSeedDist (bytesToTypedSG ds S).main :=
  slhdsa_bytes_suf_cmaG ds structural_128s S

theorem slhdsa_sha2_128s_bytes_euf_cmaG
    (A : GBytesForger ds Link.vp Link.prims codec128s optRand pkSeedDist) :
    eufAdvG ds A ≤ betaEufG ds optRand pkSeedDist (bytesToTypedG ds A).main :=
  slhdsa_bytes_euf_cmaG ds structural_128s A

theorem slhdsa_sha2_128s_pure_bytes_suf_cmaG
    (S : GPureBytesStrongForger ds Link.vp Link.prims codec128s optRand pkSeedDist) :
    sufAdvG ds S ≤
      betaSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds S)).main :=
  slhdsa_pure_bytes_suf_cmaG ds structural_128s S

theorem slhdsa_sha2_128s_pure_bytes_euf_cmaG
    (A : GPureBytesForger ds Link.vp Link.prims codec128s optRand pkSeedDist) :
    eufAdvG ds A ≤ betaEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main :=
  slhdsa_pure_bytes_euf_cmaG ds structural_128s A

theorem slhdsa_sha2_128s_bytes_suf_cma_linearG
    (S : GBytesStrongForger ds Link.vp Link.prims codec128s optRand pkSeedDist) :
    sufAdvG ds S + linIdealSufG ds optRand pkSeedDist (bytesToTypedSG ds S).main ≤
      linRealSufG ds optRand pkSeedDist (bytesToTypedSG ds S).main :=
  slhdsa_bytes_suf_cma_linearG ds structural_128s S

theorem slhdsa_sha2_128s_bytes_euf_cma_linearG
    (A : GBytesForger ds Link.vp Link.prims codec128s optRand pkSeedDist) :
    eufAdvG ds A + linIdealEufG ds optRand pkSeedDist (bytesToTypedG ds A).main ≤
      linRealEufG ds optRand pkSeedDist (bytesToTypedG ds A).main :=
  slhdsa_bytes_euf_cma_linearG ds structural_128s A

theorem slhdsa_sha2_128s_pure_bytes_suf_cma_linearG
    (S : GPureBytesStrongForger ds Link.vp Link.prims codec128s optRand pkSeedDist) :
    sufAdvG ds S +
        linIdealSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds S)).main ≤
      linRealSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds S)).main :=
  slhdsa_pure_bytes_suf_cma_linearG ds structural_128s S

theorem slhdsa_sha2_128s_pure_bytes_euf_cma_linearG
    (A : GPureBytesForger ds Link.vp Link.prims codec128s optRand pkSeedDist) :
    eufAdvG ds A +
        linIdealEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main ≤
      linRealEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main :=
  slhdsa_pure_bytes_euf_cma_linearG ds structural_128s A

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms exists_resolution_euf
#print axioms slhdsa_euf_cma_resolved
#print axioms slhdsa_suf_cma_resolved
#print axioms slhdsa_sha2_128s_bytes_suf_cmaG
#print axioms slhdsa_sha2_128s_pure_bytes_suf_cmaG
#print axioms slhdsa_sha2_128s_bytes_suf_cma_linearG
#print axioms slhdsa_sha2_128s_pure_bytes_euf_cma_linearG
end Axioms
