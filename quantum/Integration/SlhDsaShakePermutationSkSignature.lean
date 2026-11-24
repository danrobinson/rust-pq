import Integration.SlhDsaShakePermutationSkBudget
import Integration.SlhDsaShakePermutationHonestGame

/-! Select the bounded ancillary SHAKE roles inside the reduction of the
actual shared-permutation byte signature experiment. The bounded-domain
machine and original forger induce identical closed quantum computations. -/
namespace Reduction.ShakePermutation.SkCost
open Classical MLink SLHDSA SLHDSA.Security Quantum OracleComp OracleSpec PQ.Interactive QMsg ENNReal
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
noncomputable abbrev capped (N : ℕ) (π : Permutation) :=
  ShakeApi.forgerAt S rand seeds F (ShakeApi.extend (table S N (oracle π))) (oracle π)

private theorem restrict_extend (N : ℕ) (g : ShakeApi.RawTable S N) :
    ShakeApi.restrict S N (ShakeApi.extend g) = g := by
  funext x
  change ShakeApi.extend g (List.ofFn x.2) = g x
  have h : (List.ofFn x.2).length ≤ N := by simpa only [List.length_ofFn] using Nat.le_of_lt_succ x.1.isLt
  rw [ShakeApi.extend_apply g _ h,BList.ofList_ofFn]

theorem actual_game (N : ℕ) (c : Caps) (cap : ShakeApi.rawCap S 67 c.ml ≤ N)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (fresh : QueryLog (Honest.ByteMessage →ₒ Honest.ByteSig) → Honest.ByteMessage → Honest.ByteSig → Bool) (π : Permutation) :
    qSigExperiment fresh (experiment S rand seeds F π) =
      qSigExperiment (sigAlg := ShakeApi.scheme S rand seeds (ShakeApi.extend (table S N (oracle π)))) fresh (capped S rand seeds F N π) := by
  let fixed : ShakeApi.Xof S := fun _ => default
  have real := Honest.runJoint_permutation S N fixed rand seeds fresh F c cap hc π
  have finite := Honest.runJoint_full S N fixed (ShakeApi.extend (table S N (oracle π))) rand seeds F fresh c cap hc (oracle π)
  rw [restrict_extend] at finite
  exact real.symm.trans finite

theorem linear_reduction (N : ℕ) (c : Caps) (cap : ShakeApi.rawCap S 67 c.ml ≤ N)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) (π : Permutation) :
    let B := qPureBytesToInternal (capped S rand seeds F N π)
    qStrongUnforgeableAdvantage (experiment S rand seeds F π) + qLinIdealSuf B ≤ qLinRealSuf B := by
  intro B
  have eq : qStrongUnforgeableAdvantage (experiment S rand seeds F π) =
      qStrongUnforgeableAdvantage (capped S rand seeds F N π) := by
    unfold qStrongUnforgeableAdvantage qStrongUnforgeableExperiment
    rw [actual_game S rand seeds F N c cap hc]
    rfl
  rw [eq]
  exact slhdsa_pure_bytes_suf_cma_final_linear_quantum_all (ShakeApi.structural S _) _

end Reduction.ShakePermutation.SkCost
#print axioms Reduction.ShakePermutation.SkCost.linear_reduction
