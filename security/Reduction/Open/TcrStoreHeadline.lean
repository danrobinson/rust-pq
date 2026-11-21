/-
Work package OPEN, O9: the final theorems with the ANSWER-STORING class adversaries
`bTcrArA n A` (`Reduction/Open/TcrStore.lean`) in place of `bTcrArM n A`.

The experiments are equal (`bTcrArA_experiment_eq`), so the bound is EQUAL to the existing
final bound (`betaSufFinalStore_eq`, `betaEufFinalStore_eq`); every theorem here is the existing
headline theorem rewritten with that equality.  Nothing existing is restated or changed.
-/
import Reduction.Open.TcrStore
import Reduction.HeadlineFinal

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Open

open TweakableHash

set_option linter.unusedSectionVars false

section Final

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

attribute [local irreducible] arityTargets tcrTargets

/-- **The bound with the answer-storing class adversaries equals the bound with `bTcrArM`**
(any PRF distinguishers `B₁`, `B₂`). -/
theorem boundFinalStore_eq (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist)
    (B₁ : PRFScheme.PRFAdversary (prims.PkSeed × SkAdrs vp) prims.Y) (B₂ : MsgPrfAdv prims) :
    boundFinalTight pkSeedDist B₁ B₂ (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArA 1 A) (bTcrArA 2 A) (bTcrArA vp.params.len A) (bTcrArA vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcrT pkSeedDist (Lazy.bWotsS A)) =
      boundFinalTight pkSeedDist B₁ B₂ (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArM 1 A) (bTcrArM 2 A) (bTcrArM vp.params.len A) (bTcrArM vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcrT pkSeedDist (Lazy.bWotsS A)) := by
  unfold boundFinalTight
  rw [bTcrArA_advantage_eq hS 1 A, bTcrArA_advantage_eq hS 2 A,
    bTcrArA_advantage_eq hS vp.params.len A, bTcrArA_advantage_eq hS vp.params.k A]

/-- The final EUF-CMA bound with the answer-storing class adversaries. -/
noncomputable def betaEufFinalStore (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundFinalTight pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArA 1 A) (bTcrArA 2 A) (bTcrArA vp.params.len A) (bTcrArA vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcrT pkSeedDist (Lazy.bWotsS A))

/-- The final SUF-CMA bound with the answer-storing class adversaries. -/
noncomputable def betaSufFinalStore (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundFinalTight pkSeedDist (bPrfWC sufCheck A) (Lazy.bPrfMsgWL sufCheck A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArA 1 A) (bTcrArA 2 A) (bTcrArA vp.params.len A) (bTcrArA vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
    (rTcrT pkSeedDist (Lazy.bWotsS A))

theorem betaEufFinalStore_eq (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    betaEufFinalStore A = betaEufFinalMemo A :=
  boundFinalStore_eq hS A _ _

theorem betaSufFinalStore_eq (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    betaSufFinalStore A = betaSufFinalMemo A :=
  boundFinalStore_eq hS A _ _

/-! ## Typed keys and signatures -/

/-- **SUF-CMA of SLH-DSA (FIPS 205 internal algorithms), tight caps, answer-storing class
adversaries.**  `slhdsa_suf_cma_final_memo` with `bTcrArM → bTcrArA`. -/
theorem slhdsa_suf_cma_final_store (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck S.toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)
        (Lazy.bItsrL S.toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (bTcrArA 1 S.toUnforgeableAdversary) (bTcrArA 2 S.toUnforgeableAdversary)
        (bTcrArA vp.params.len S.toUnforgeableAdversary)
        (bTcrArA vp.params.k S.toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rTcrT pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) :=
  le_of_le_of_eq (slhdsa_suf_cma_final_memo hS S)
    (boundFinalStore_eq hS S.toUnforgeableAdversary (bPrfWC sufCheck S.toUnforgeableAdversary)
      (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary)).symm

/-- `∀ S, Adv S ≤ β S`. -/
theorem slhdsa_suf_cma_final_store' (hS : Structural vp prims) :
    ∀ S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        betaSufFinalStore S.toUnforgeableAdversary :=
  fun S => slhdsa_suf_cma_final_store hS S

/-- **EUF-CMA of SLH-DSA (FIPS 205 internal algorithms), tight caps, answer-storing class
adversaries.**  `slhdsa_euf_cma_final_memo` with `bTcrArM → bTcrArA`. -/
theorem slhdsa_euf_cma_final_store (hS : Structural vp prims)
    (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalTight pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArA 1 A) (bTcrArA 2 A) (bTcrArA vp.params.len A) (bTcrArA vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcrT pkSeedDist (Lazy.bWotsS A)) :=
  le_of_le_of_eq (slhdsa_euf_cma_final_memo hS A)
    (boundFinalStore_eq hS A (bPrfC A) (Lazy.bPrfMsgL A)).symm

/-- `∀ A, Adv A ≤ β A`. -/
theorem slhdsa_euf_cma_final_store' (hS : Structural vp prims) :
    ∀ A : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalStore A :=
  fun A => slhdsa_euf_cma_final_store hS A

/-- **EUF-CMA of the external pure interface (Alg. 21/22/24)**, answer-storing class
adversaries, at the internal forger `toInternal A`. -/
theorem slhdsa_pure_euf_cma_final_store (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalStore (toInternal A) :=
  external_bound_of_internal_bound betaEufFinalStore (slhdsa_euf_cma_final_store' hS) A

/-- **SUF-CMA of the external pure interface**, answer-storing class adversaries, at the internal
forger `toInternal S.toUnforgeableAdversary`. -/
theorem slhdsa_pure_suf_cma_final_store (hS : Structural vp prims)
    (S : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalStore (toInternal S.toUnforgeableAdversary) :=
  le_of_le_of_eq (slhdsa_pure_suf_cma_final_memo hS S)
    (boundFinalStore_eq hS (toInternal S.toUnforgeableAdversary)
      (bPrfWC sufCheck (toInternal S.toUnforgeableAdversary))
      (Lazy.bPrfMsgWL sufCheck (toInternal S.toUnforgeableAdversary))).symm

/-! ## Byte-level schemes (the final headline of `Reduction/HeadlineFinal.lean`) -/

/-- **SUF-CMA of SLH-DSA on byte strings (FIPS 205 Alg. 18–20), final form, answer-storing
class adversaries.**  `slhdsa_bytes_suf_cma_final` with `bTcrArM → bTcrArA`. -/
theorem slhdsa_bytes_suf_cma_final_store (hS : Structural vp prims)
    (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck (bytesToTypedS S).toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck (bytesToTypedS S).toUnforgeableAdversary)
        (Lazy.bItsrL (bytesToTypedS S).toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS (bytesToTypedS S).toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS (bytesToTypedS S).toUnforgeableAdversary))
        (bTcrArA 1 (bytesToTypedS S).toUnforgeableAdversary)
        (bTcrArA 2 (bytesToTypedS S).toUnforgeableAdversary)
        (bTcrArA vp.params.len (bytesToTypedS S).toUnforgeableAdversary)
        (bTcrArA vp.params.k (bytesToTypedS S).toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary))
        (rTcrT pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary)) :=
  le_of_le_of_eq (slhdsa_bytes_suf_cma_final hS S)
    (boundFinalStore_eq hS (bytesToTypedS S).toUnforgeableAdversary
      (bPrfWC sufCheck (bytesToTypedS S).toUnforgeableAdversary)
      (Lazy.bPrfMsgWL sufCheck (bytesToTypedS S).toUnforgeableAdversary)).symm

/-- **EUF-CMA of SLH-DSA on byte strings, final form, answer-storing class adversaries.** -/
theorem slhdsa_bytes_euf_cma_final_store (hS : Structural vp prims)
    (A : BytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalStore (bytesToTyped A) :=
  le_of_le_of_eq (slhdsa_bytes_euf_cma_final hS A)
    (boundFinalStore_eq hS (bytesToTyped A) (bPrfC (bytesToTyped A))
      (Lazy.bPrfMsgL (bytesToTyped A))).symm

/-- **SUF-CMA of the external pure interface on byte strings (Alg. 21/22/24), final form,
answer-storing class adversaries.** -/
theorem slhdsa_pure_bytes_suf_cma_final_store (hS : Structural vp prims)
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalStore (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  le_of_le_of_eq (slhdsa_pure_bytes_suf_cma_final hS S)
    (boundFinalStore_eq hS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))
      (bPrfWC sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))
      (Lazy.bPrfMsgWL sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))).symm

/-- **EUF-CMA of the external pure interface on byte strings, final form, answer-storing class
adversaries.** -/
theorem slhdsa_pure_bytes_euf_cma_final_store (hS : Structural vp prims)
    (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalStore (toInternal (pureBytesToTyped A)) :=
  le_of_le_of_eq (slhdsa_pure_bytes_euf_cma_final hS A)
    (boundFinalStore_eq hS (toInternal (pureBytesToTyped A))
      (bPrfC (toInternal (pureBytesToTyped A)))
      (Lazy.bPrfMsgL (toInternal (pureBytesToTyped A)))).symm

end Final

/-! ## SLH-DSA-SHA2-128s (no hypothesis) -/

theorem slhdsa_sha2_128s_suf_cma_final_store
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : SignatureAlg.StrongUnforgeableAdversary
      (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalStore S.toUnforgeableAdversary :=
  slhdsa_suf_cma_final_store structural_128s S

theorem slhdsa_sha2_128s_euf_cma_final_store
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaEufFinalStore A :=
  slhdsa_euf_cma_final_store structural_128s A

theorem slhdsa_sha2_128s_bytes_suf_cma_final_store
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : BytesStrongForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalStore (bytesToTypedS S).toUnforgeableAdversary :=
  slhdsa_bytes_suf_cma_final_store structural_128s S

theorem slhdsa_sha2_128s_pure_bytes_suf_cma_final_store
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : PureBytesStrongForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalStore (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  slhdsa_pure_bytes_suf_cma_final_store structural_128s S

end Open

#print axioms Open.boundFinalStore_eq
#print axioms Open.slhdsa_suf_cma_final_store
#print axioms Open.slhdsa_euf_cma_final_store
#print axioms Open.slhdsa_pure_euf_cma_final_store
#print axioms Open.slhdsa_pure_suf_cma_final_store
#print axioms Open.slhdsa_bytes_suf_cma_final_store
#print axioms Open.slhdsa_bytes_euf_cma_final_store
#print axioms Open.slhdsa_pure_bytes_suf_cma_final_store
#print axioms Open.slhdsa_pure_bytes_euf_cma_final_store
#print axioms Open.slhdsa_sha2_128s_suf_cma_final_store
#print axioms Open.slhdsa_sha2_128s_euf_cma_final_store
#print axioms Open.slhdsa_sha2_128s_bytes_suf_cma_final_store
#print axioms Open.slhdsa_sha2_128s_pure_bytes_suf_cma_final_store

end Reduction
