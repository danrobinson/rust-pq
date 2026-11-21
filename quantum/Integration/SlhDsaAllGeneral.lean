import PQ.Interactive.GamesGeneral
import Integration.SlhDsaAll

/-!
# The final unconditional headlines with advantages in the GENERAL quantum games (integration)

NOT part of the default target; checked by `scripts/check-integration.sh`.

`PQ/Interactive/GamesGeneral.lean` defines the general quantum two-phase games (both phases
quantum machines on one workspace, workspace state carried across the seed reveal).  The machines
on the right-hand sides of the `…_quantum_all` headlines are restricted adversaries (classical
first phase); as general adversaries (`.toGeneral`) they have the same advantage.  Here the
headlines are restated with every two-phase term an advantage (or Born probability) in the
general quantum game — the games that serve as definitions of the quantum hardness assumptions:

* `qBoundMemoG`, `qBetaEufMemoG`, `qBetaSufMemoG` (`= qBetaEufMemo`, `qBetaSufMemo`);
* `qLinearIdealSideG`, `qLinearRealSideG`, `qLin{Ideal,Real}{Euf,Suf}G`;
* sixteen theorems `slhdsa_*_quantum_all_general` (four schemes, EUF/SUF, absolute/linear).

The PRF and ITSR games are single-stage: `qPrfAdvantage`, `qItsrAdvantage` are already the general
quantum games (the adversary is an arbitrary quantum machine with classical oracle access).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive
open scoped ComplexOrder

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

attribute [local irreducible] arityTargets tcrTargets

/-- `qBoundMemo` with every two-phase term an advantage in the general quantum game. -/
noncomputable def qBoundMemoG (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (P₁ P₂ : ℝ≥0∞) : ℝ≥0∞ :=
  P₁ + P₂ +
    qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ +
    (qDsprFV_AdvantageG (qToDspr Q).toGeneral + 3 * qTcrFV_AdvantageG (qToTcr Q).toGeneral) +
    (qSM_DT_TCR_AdvantageG (qbTcrArM 1 Q).toGeneral +
      qSM_DT_TCR_AdvantageG (qbTcrArM 2 Q).toGeneral +
      qSM_DT_TCR_AdvantageG (qbTcrArM vp.params.len Q).toGeneral +
      qSM_DT_TCR_AdvantageG (qbTcrArM vp.params.k Q).toGeneral) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_AdvantageG (qrUd Q).toGeneral +
    qSM_DT_PRE_AdvantageG (qrPre Q).toGeneral +
    qSM_DT_TCR_AdvantageG (qrTcrT Q).toGeneral

theorem qBoundMemo_eq_general (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (P₁ P₂ : ℝ≥0∞) : qBoundMemo Q P₁ P₂ = qBoundMemoG Q P₁ P₂ := by
  unfold qBoundMemo qBoundMemoG
  rw [qDsprFV_Advantage_toGeneral, qTcrFV_Advantage_toGeneral,
    qSM_DT_TCR_Advantage_toGeneral (qbTcrArM 1 Q), qSM_DT_TCR_Advantage_toGeneral (qbTcrArM 2 Q),
    qSM_DT_TCR_Advantage_toGeneral (qbTcrArM vp.params.len Q),
    qSM_DT_TCR_Advantage_toGeneral (qbTcrArM vp.params.k Q), qSM_DT_UD_Advantage_toGeneral,
    qSM_DT_PRE_Advantage_toGeneral, qSM_DT_TCR_Advantage_toGeneral (qrTcrT Q)]

/-- EUF-CMA bound, general games. -/
noncomputable def qBetaEufMemoG (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    ℝ≥0∞ :=
  qBoundMemoG Q (qPrfAdvantage (skPrfC vp prims) (qbPrfC Q) Q.ρ₀)
    (qPrfAdvantage (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀)

/-- SUF-CMA bound, general games. -/
noncomputable def qBetaSufMemoG (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    ℝ≥0∞ :=
  qBoundMemoG Q (qPrfAdvantage (skPrfC vp prims) (qbPrfWC sufCheck Q) Q.ρ₀)
    (qPrfAdvantage (msgPrf vp prims) (qbPrfMsgWL sufCheck Q) Q.ρ₀)

theorem qBetaEufMemo_eq_general (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qBetaEufMemo Q = qBetaEufMemoG Q := qBoundMemo_eq_general Q _ _

theorem qBetaSufMemo_eq_general (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qBetaSufMemo Q = qBetaSufMemoG Q := qBoundMemo_eq_general Q _ _

/-- Ideal side of the linear form, general games. -/
noncomputable def qLinearIdealSideG (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (I₁ I₂ : ℝ≥0∞) : ℝ≥0∞ :=
  I₁ + I₂ + qDsprFV_SPProbabilityG (qToDspr Q).toGeneral +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_IdealSuccessG (qrUd Q).toGeneral

/-- Real side of the linear form, general games. -/
noncomputable def qLinearRealSideG (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (R₁ R₂ : ℝ≥0∞) : ℝ≥0∞ :=
  R₁ + R₂ +
    qItsrAdvantage (itsrProblem vp prims) (qbItsrL Q) Q.ρ₀ +
    (qDsprFV_SuccessG (qToDspr Q).toGeneral + 3 * qTcrFV_AdvantageG (qToTcr Q).toGeneral) +
    (qSM_DT_TCR_AdvantageG (qbTcrArM 1 Q).toGeneral +
      qSM_DT_TCR_AdvantageG (qbTcrArM 2 Q).toGeneral +
      qSM_DT_TCR_AdvantageG (qbTcrArM vp.params.len Q).toGeneral +
      qSM_DT_TCR_AdvantageG (qbTcrArM vp.params.k Q).toGeneral) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * qSM_DT_UD_RealSuccessG (qrUd Q).toGeneral +
    qSM_DT_PRE_AdvantageG (qrPre Q).toGeneral +
    qSM_DT_TCR_AdvantageG (qrTcrT Q).toGeneral

theorem qLinearIdealSide_eq_general (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (I₁ I₂ : ℝ≥0∞) : qLinearIdealSide Q I₁ I₂ = qLinearIdealSideG Q I₁ I₂ := by
  unfold qLinearIdealSide qLinearIdealSideG
  rw [qDsprFV_SPProbability_toGeneral, qSM_DT_UD_IdealSuccess_toGeneral]

theorem qLinearRealSide_eq_general (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (R₁ R₂ : ℝ≥0∞) : qLinearRealSide Q R₁ R₂ = qLinearRealSideG Q R₁ R₂ := by
  unfold qLinearRealSide qLinearRealSideG
  rw [qDsprFV_Success_toGeneral, qTcrFV_Advantage_toGeneral,
    qSM_DT_TCR_Advantage_toGeneral (qbTcrArM 1 Q), qSM_DT_TCR_Advantage_toGeneral (qbTcrArM 2 Q),
    qSM_DT_TCR_Advantage_toGeneral (qbTcrArM vp.params.len Q),
    qSM_DT_TCR_Advantage_toGeneral (qbTcrArM vp.params.k Q), qSM_DT_UD_RealSuccess_toGeneral,
    qSM_DT_PRE_Advantage_toGeneral, qSM_DT_TCR_Advantage_toGeneral (qrTcrT Q)]

noncomputable def qLinIdealEufG (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) : ℝ≥0∞ :=
  qLinearIdealSideG Q (qPrfIdealPr (qbPrfC Q) Q.ρ₀) (qPrfIdealPr (qbPrfMsgL Q) Q.ρ₀)

noncomputable def qLinRealEufG (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) : ℝ≥0∞ :=
  qLinearRealSideG Q (qPrfRealPr (skPrfC vp prims) (qbPrfC Q) Q.ρ₀)
    (qPrfRealPr (msgPrf vp prims) (qbPrfMsgL Q) Q.ρ₀)

noncomputable def qLinIdealSufG (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) : ℝ≥0∞ :=
  qLinearIdealSideG Q (qPrfIdealPr (qbPrfWC sufCheck Q) Q.ρ₀)
    (qPrfIdealPr (qbPrfMsgWL sufCheck Q) Q.ρ₀)

noncomputable def qLinRealSufG (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) : ℝ≥0∞ :=
  qLinearRealSideG Q (qPrfRealPr (skPrfC vp prims) (qbPrfWC sufCheck Q) Q.ρ₀)
    (qPrfRealPr (msgPrf vp prims) (qbPrfMsgWL sufCheck Q) Q.ρ₀)

theorem qLinIdealEuf_eq_general (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qLinIdealEuf Q = qLinIdealEufG Q := qLinearIdealSide_eq_general Q _ _

theorem qLinRealEuf_eq_general (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qLinRealEuf Q = qLinRealEufG Q := qLinearRealSide_eq_general Q _ _

theorem qLinIdealSuf_eq_general (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qLinIdealSuf Q = qLinIdealSufG Q := qLinearIdealSide_eq_general Q _ _

theorem qLinRealSuf_eq_general (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qLinRealSuf Q = qLinRealSufG Q := qLinearRealSide_eq_general Q _ _

/-! ## The headlines -/

/-- **EUF-CMA of SLH-DSA (internal algorithms, typed) against every quantum forger, advantages in the
general quantum games.** -/
theorem slhdsa_euf_cma_final_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemoG Q := by
  rw [← qBetaEufMemo_eq_general]
  exact slhdsa_euf_cma_final_quantum_all hS Q

/-- **EUF-CMA of SLH-DSA (internal algorithms, typed) against every quantum forger, linear form, general
quantum games.** -/
theorem slhdsa_euf_cma_final_linear_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEufG Q ≤ qLinRealEufG Q := by
  rw [← qLinIdealEuf_eq_general, ← qLinRealEuf_eq_general]
  exact slhdsa_euf_cma_final_linear_quantum_all hS Q

/-- **SUF-CMA of SLH-DSA (internal algorithms, typed) against every quantum forger, advantages in the
general quantum games.** -/
theorem slhdsa_suf_cma_final_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemoG Q := by
  rw [← qBetaSufMemo_eq_general]
  exact slhdsa_suf_cma_final_quantum_all hS Q

/-- **SUF-CMA of SLH-DSA (internal algorithms, typed) against every quantum forger, linear form, general
quantum games.** -/
theorem slhdsa_suf_cma_final_linear_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSufG Q ≤ qLinRealSufG Q := by
  rw [← qLinIdealSuf_eq_general, ← qLinRealSuf_eq_general]
  exact slhdsa_suf_cma_final_linear_quantum_all hS Q

/-- **EUF-CMA of SLH-DSA (external pure interface, typed) against every quantum forger, advantages in the
general quantum games.** -/
theorem slhdsa_pure_euf_cma_final_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemoG (qToInternal Q) := by
  rw [← qBetaEufMemo_eq_general]
  exact slhdsa_pure_euf_cma_final_quantum_all hS Q

/-- **EUF-CMA of SLH-DSA (external pure interface, typed) against every quantum forger, linear form, general
quantum games.** -/
theorem slhdsa_pure_euf_cma_final_linear_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEufG (qToInternal Q) ≤ qLinRealEufG (qToInternal Q) := by
  rw [← qLinIdealEuf_eq_general, ← qLinRealEuf_eq_general]
  exact slhdsa_pure_euf_cma_final_linear_quantum_all hS Q

/-- **SUF-CMA of SLH-DSA (external pure interface, typed) against every quantum forger, advantages in the
general quantum games.** -/
theorem slhdsa_pure_suf_cma_final_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemoG (qToInternal Q) := by
  rw [← qBetaSufMemo_eq_general]
  exact slhdsa_pure_suf_cma_final_quantum_all hS Q

/-- **SUF-CMA of SLH-DSA (external pure interface, typed) against every quantum forger, linear form, general
quantum games.** -/
theorem slhdsa_pure_suf_cma_final_linear_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (externalAlg vp prims optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSufG (qToInternal Q) ≤ qLinRealSufG (qToInternal Q) := by
  rw [← qLinIdealSuf_eq_general, ← qLinRealSuf_eq_general]
  exact slhdsa_pure_suf_cma_final_linear_quantum_all hS Q

/-- **EUF-CMA of SLH-DSA (internal algorithms on byte strings) against every quantum forger, advantages in the
general quantum games.** -/
theorem slhdsa_bytes_euf_cma_final_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemoG (qBytesToTyped Q) := by
  rw [← qBetaEufMemo_eq_general]
  exact slhdsa_bytes_euf_cma_final_quantum_all hS Q

/-- **EUF-CMA of SLH-DSA (internal algorithms on byte strings) against every quantum forger, linear form, general
quantum games.** -/
theorem slhdsa_bytes_euf_cma_final_linear_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEufG (qBytesToTyped Q) ≤ qLinRealEufG (qBytesToTyped Q) := by
  rw [← qLinIdealEuf_eq_general, ← qLinRealEuf_eq_general]
  exact slhdsa_bytes_euf_cma_final_linear_quantum_all hS Q

/-- **SUF-CMA of SLH-DSA (internal algorithms on byte strings) against every quantum forger, advantages in the
general quantum games.** -/
theorem slhdsa_bytes_suf_cma_final_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemoG (qBytesToTyped Q) := by
  rw [← qBetaSufMemo_eq_general]
  exact slhdsa_bytes_suf_cma_final_quantum_all hS Q

/-- **SUF-CMA of SLH-DSA (internal algorithms on byte strings) against every quantum forger, linear form, general
quantum games.** -/
theorem slhdsa_bytes_suf_cma_final_linear_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (bytesAlg vp prims codec optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSufG (qBytesToTyped Q) ≤ qLinRealSufG (qBytesToTyped Q) := by
  rw [← qLinIdealSuf_eq_general, ← qLinRealSuf_eq_general]
  exact slhdsa_bytes_suf_cma_final_linear_quantum_all hS Q

/-- **EUF-CMA of SLH-DSA (external pure interface on byte strings) against every quantum forger, advantages in the
general quantum games.** -/
theorem slhdsa_pure_bytes_euf_cma_final_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ qBetaEufMemoG (qPureBytesToInternal Q) := by
  rw [← qBetaEufMemo_eq_general]
  exact slhdsa_pure_bytes_euf_cma_final_quantum_all hS Q

/-- **EUF-CMA of SLH-DSA (external pure interface on byte strings) against every quantum forger, linear form, general
quantum games.** -/
theorem slhdsa_pure_bytes_euf_cma_final_linear_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qUnforgeableAdvantage Q + qLinIdealEufG (qPureBytesToInternal Q) ≤ qLinRealEufG (qPureBytesToInternal Q) := by
  rw [← qLinIdealEuf_eq_general, ← qLinRealEuf_eq_general]
  exact slhdsa_pure_bytes_euf_cma_final_linear_quantum_all hS Q

/-- **SUF-CMA of SLH-DSA (external pure interface on byte strings) against every quantum forger, advantages in the
general quantum games.** -/
theorem slhdsa_pure_bytes_suf_cma_final_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q ≤ qBetaSufMemoG (qPureBytesToInternal Q) := by
  rw [← qBetaSufMemo_eq_general]
  exact slhdsa_pure_bytes_suf_cma_final_quantum_all hS Q

/-- **SUF-CMA of SLH-DSA (external pure interface on byte strings) against every quantum forger, linear form, general
quantum games.** -/
theorem slhdsa_pure_bytes_suf_cma_final_linear_quantum_all_general (hS : Structural vp prims)
    (Q : QForger W (pureBytesAlg vp prims codec optRand pkSeedDist)) :
    qStrongUnforgeableAdvantage Q + qLinIdealSufG (qPureBytesToInternal Q) ≤ qLinRealSufG (qPureBytesToInternal Q) := by
  rw [← qLinIdealSuf_eq_general, ← qLinRealSuf_eq_general]
  exact slhdsa_pure_bytes_suf_cma_final_linear_quantum_all hS Q

end Reduction

#print axioms Reduction.qBoundMemo_eq_general
#print axioms Reduction.slhdsa_euf_cma_final_quantum_all_general
#print axioms Reduction.slhdsa_euf_cma_final_linear_quantum_all_general
#print axioms Reduction.slhdsa_suf_cma_final_quantum_all_general
#print axioms Reduction.slhdsa_suf_cma_final_linear_quantum_all_general
#print axioms Reduction.slhdsa_pure_euf_cma_final_quantum_all_general
#print axioms Reduction.slhdsa_pure_euf_cma_final_linear_quantum_all_general
#print axioms Reduction.slhdsa_pure_suf_cma_final_quantum_all_general
#print axioms Reduction.slhdsa_pure_suf_cma_final_linear_quantum_all_general
#print axioms Reduction.slhdsa_bytes_euf_cma_final_quantum_all_general
#print axioms Reduction.slhdsa_bytes_euf_cma_final_linear_quantum_all_general
#print axioms Reduction.slhdsa_bytes_suf_cma_final_quantum_all_general
#print axioms Reduction.slhdsa_bytes_suf_cma_final_linear_quantum_all_general
#print axioms Reduction.slhdsa_pure_bytes_euf_cma_final_quantum_all_general
#print axioms Reduction.slhdsa_pure_bytes_euf_cma_final_linear_quantum_all_general
#print axioms Reduction.slhdsa_pure_bytes_suf_cma_final_quantum_all_general
#print axioms Reduction.slhdsa_pure_bytes_suf_cma_final_linear_quantum_all_general
