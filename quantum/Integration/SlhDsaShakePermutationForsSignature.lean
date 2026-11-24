import Integration.SlhDsaShakePermutationForsMachine
import Integration.SlhDsaShakePermutationSparseFors
import Integration.SlhDsaShakePermutationSparseCap
import Integration.SlhDsaShakePermutationSparseNumbers

namespace Reduction.ShakePermutation.SparsePort.Fors
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal TweakableHash SetOracle
open ShakeApi (extend)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] openPreTargets
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "T₀" => (fun _ : ShakeApi.Input N => (default : Bytes S.vp.params.m))
local notation "P₀" => ShakeApi.primitives S (extend T₀)
local notation "pr" => fun π : Permutation => ShakeApi.primitives S (extend (SkCost.table S N (oracle π)))
local notation "B" => fun π : Permutation => qPureBytesToInternal (SkCost.capped S rand seeds F N π)

noncomputable def selection : QTcrFV_Adversary (Work (E := E)) (Base S seeds) where
  State := Open.ForsP1State S.vp P₀
  choose := Open.forsPhase1 S.vp P₀
  forge := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

local notation "A" => selection S seeds F
local notation "M" => fun H st pk => ForsMach.forsTcrMach S N rand F T₀ st pk H

theorem actual (π : Permutation) : qTcrFV_Advantage (qToTcr (B π)) =
    qTcrFV_Advantage (player S seeds A M (oracle π) (fun p t m => (primitives (lanes π) S.vp.params).Thash p t [m])) := by
  let f := fun p t m => (pr π).Thash p t [m]
  have ch : (qToTcr (B π)).choose = (A).choose := by
    refine (Open.toTcr_choose_eq (B π).toClassical).trans ?_
    qm_kernel_rfl
  have fg : M (oracle π) = (qToTcr (B π)).forge := funext fun st => funext fun pk =>
    ForsMach.forsTcrMach_oracle S N rand seeds F T₀ st pk _
  let v := fun g => qTcrFV_Advantage (player S seeds A M (oracle π) g)
  have eq : qToTcr (B π) = player S seeds A M (oracle π) f := by
    kexact congrArg₂ (fun c g => (⟨Open.ForsP1State S.vp P₀,c,g,F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
      QTcrFV_Adversary (Work (E := E)) (fvWithEval (Base S seeds) f))) ch fg.symm
  exact (congrArg qTcrFV_Advantage eq).trans (congrArg v (funext fun p => funext fun t => funext fun m =>
    Memo.short S π p t [m] (by change 1 ≤ 67; decide)))

theorem signature_tcr
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    uniformMean (fun π => qTcrFV_Advantage (qToTcr (B π))) ≤ ((2:ℝ≥0∞)^38)⁻¹ := by
  let q := 2^40 + 483*forsMHashes S.vp 1
  have hq' : q ≤ 2^41 := by cases S <;> decide +kernel
  have w : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q :=
    fun st pk => ForsMach.pue_forsTcrMach S N rand F T₀ le_rfl st pk _ _ hq hs
  have h := bound S seeds A M q w
  simp_rw [actual S rand seeds F]
  exact h.trans ((show loss S q ≤ ArityGame.loss S 1 q 0 by simp only [loss,ArityGame.loss,Nat.cast_zero,zero_mul,add_zero,le_refl]).trans
    (ArityGame.benchmark_loss S 1 (by decide) q 0 hq' (by decide)))

end Reduction.ShakePermutation.SparsePort.Fors
#print axioms Reduction.ShakePermutation.SparsePort.Fors.signature_tcr
