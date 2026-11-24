import Integration.SlhDsaShakePermutationForsMachine
import Integration.SlhDsaShakePermutationSparseDspr
import Integration.SlhDsaShakePermutationSparseCap
import Integration.SlhDsaShakePermutationSparseNumbers

namespace Reduction.ShakePermutation.SparsePort.ForsDecision
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

noncomputable def selection : QDsprFV_Adversary (Fors.Work (E := E)) (DBase S seeds) where
  State := Open.ForsP1State S.vp P₀
  choose := Open.forsPhase1 S.vp P₀
  guess := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

local notation "A" => selection S seeds F
local notation "M" => fun H st pk => ForsMach.forsDsprMach S N rand F T₀ st pk H

theorem actual_eq (π : Permutation) :
    let f := fun p t m => (pr π).Thash p t [m]
    qToDspr (B π) = player S seeds A M (oracle π) f := by
  let f := fun p t m => (pr π).Thash p t [m]
  have ch : (qToDspr (B π)).choose = (A).choose := by
    refine (Open.toDspr_choose_eq (B π).toClassical).trans ?_
    qm_kernel_rfl
  have fg : M (oracle π) = (qToDspr (B π)).guess := funext fun st => funext fun pk =>
    ForsMach.forsDsprMach_oracle S N rand seeds F T₀ st pk _
  kexact congrArg₂ (fun c g => (⟨Open.ForsP1State S.vp P₀,c,g,F.ρ₀,F.posSemidef,F.trace_eq_one⟩ :
    QDsprFV_Adversary (Fors.Work (E := E)) (game S seeds f))) ch fg.symm

theorem signature_dspr
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    uniformMean (fun π => qDsprFV_Success (qToDspr (B π))) ≤
    uniformMean (fun π => qDsprFV_SPProbability (qToDspr (B π))) + ((2:ℝ≥0∞)^31)⁻¹ := by
  let q := 2^40 + 483*forsMHashes S.vp 1
  have hq' : q ≤ 2^41 := by cases S <;> decide +kernel
  have w : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q :=
    fun st pk => ForsMach.pue_forsDsprMach S N rand F T₀ le_rfl st pk _ _ hq hs
  let f := fun (π : Permutation) p t m => (pr π).Thash p t [m]
  let g := fun (π : Permutation) p t m => (primitives (lanes π) S.vp.params).Thash p t [m]
  have eq (π : Permutation) : f π = g π := funext fun p => funext fun t => funext fun m =>
    Memo.short S π p t [m] (by change 1 ≤ 67; decide)
  have succ (π : Permutation) : qDsprFV_Success (qToDspr (B π)) = qDsprFV_Success (player S seeds A M (oracle π) (g π)) :=
    (congrArg qDsprFV_Success (actual_eq S rand seeds F π)).trans (congrArg (fun z => qDsprFV_Success (player S seeds A M (oracle π) z)) (eq π))
  have sp (π : Permutation) : qDsprFV_SPProbability (qToDspr (B π)) = qDsprFV_SPProbability (player S seeds A M (oracle π) (g π)) :=
    (congrArg qDsprFV_SPProbability (actual_eq S rand seeds F π)).trans (congrArg (fun z => qDsprFV_SPProbability (player S seeds A M (oracle π) z)) (eq π))
  simp_rw [succ,sp]
  exact (bound S seeds A M q w).trans (add_le_add le_rfl (benchmark_loss S q hq'))

end Reduction.ShakePermutation.SparsePort.ForsDecision
#print axioms Reduction.ShakePermutation.SparsePort.ForsDecision.signature_dspr
