import Integration.SlhDsaShakePermutationWotsPreSelect
import Ideal.Realize.WotsCount1
import Reduction.Gen.Forger

namespace Reduction.ShakePermutation.SparsePort.Wots
open Classical MLink SLHDSA SLHDSA.Security Ideal.Realize Ideal.Realize.Wots Open TweakableHash OracleComp OracleSpec PQ.Interactive Quantum
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] prePhase1 udPhase1 wotsTcrPhase1 simPhase1 wotsInsts wotsChainTargets wotsStepTargetsT wotsStepTargets
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
variable (S : Sha2Set) (ω : ShakeApi.Xof S) (seeds : ProbComp S.Node)
local notation "P₀" => ShakeApi.primitives S ω

private theorem length_budget (v : ValidatedParams) :
    483*((wotsInsts v).length*(v.params.len*1) + (wotsQc v+(wotsInsts v).length*(v.params.len*(v.params.w-1)))) ≤
      483*(2^v.params.h*(v.params.k*2^(v.params.a+1)+1) +
        (wotsInstanceCount v.params+1)*2^(v.params.hp+1) +
        wotsInstanceCount v.params*(v.params.len + v.params.len*(v.params.w-1))) := by
  have f := forsC_eq v
  have t := treeC_eq v
  have qc := wotsQc_closed v
  have fi := Nat.mul_le_mul_left (2^v.params.h) (show forsC v ≤ v.params.k*2^(v.params.a+1)+1 by omega)
  have ti := Nat.mul_le_mul_left ((wotsInsts v).length+1) (show treeC v ≤ 2^(v.params.hp+1) by omega)
  rw [Resources.wotsInsts_length] at qc ti ⊢
  apply Nat.mul_le_mul_left
  rw [Nat.mul_add (wotsInstanceCount v.params), Nat.mul_one]
  omega

theorem calls_budget :
    483*((wotsInsts S.vp).length*(S.vp.params.len*1) +
      (wotsQc S.vp+(wotsInsts S.vp).length*(S.vp.params.len*(S.vp.params.w-1)))) ≤ 2^100 := by
  exact (length_budget S.vp).trans (by cases S <;> decide +kernel)

theorem pre_choice_cost :
    IsQueryBoundP (prePhase1 (vp:=S.vp) (prims:=P₀) seeds) (fun i => i.isRight = true)
      ((wotsInsts S.vp).length*(S.vp.params.len*1) +
        (wotsQc S.vp+(wotsInsts S.vp).length*(S.vp.params.len*(S.vp.params.w-1)))) := by
  let f : HashFns P₀ := ⟨(P₀).Thash,(P₀).Hmsg,(P₀).PRF,(P₀).PRFmsg⟩
  let b := Gen.dummyForger (vp:=S.vp) (prims:=withHash P₀ f) (optRand:=fun _ => pure default) (pkSeedDist:=seeds)
  have eq := wotsPre_phase1_q1_zero (vp:=S.vp) (prims:=P₀) (pkSeedDist:=seeds) f b
  have a := rPre_choose_chal (vp:=S.vp) (prims:=withHash P₀ f) (optRand:=fun _ => pure default) seeds b
  have c := rPre_choose_coll (vp:=S.vp) (prims:=withHash P₀ f) (optRand:=fun _ => pure default) seeds b
  rw [eq] at a c
  have h := IsQueryBoundP.of_imp (p':=fun i => isChalI i ∨ Open.isColl i) (fun i (v : i.isRight = true) => by
    rcases i with n|d|t
    · cases v
    · exact Or.inl trivial
    · exact Or.inr trivial) (a.or c)
  kexact h

theorem ud_choice_cost :
    IsQueryBoundP (udPhase1 (vp:=S.vp) (prims:=P₀) seeds) (fun i => i.isRight = true)
      ((wotsInsts S.vp).length*(S.vp.params.len*1) +
        (wotsQc S.vp+(wotsInsts S.vp).length*(S.vp.params.len*(S.vp.params.w-1)))) := by
  let f : HashFns P₀ := ⟨(P₀).Thash,(P₀).Hmsg,(P₀).PRF,(P₀).PRFmsg⟩
  let b := Gen.dummyForger (vp:=S.vp) (prims:=withHash P₀ f) (optRand:=fun _ => pure default) (pkSeedDist:=seeds)
  have eq := wotsUd_phase1_q1_zero (vp:=S.vp) (prims:=P₀) (pkSeedDist:=seeds) f b
  have a := rUd_pick_chal (vp:=S.vp) (prims:=withHash P₀ f) (optRand:=fun _ => pure default) seeds b
  have c := rUd_pick_coll (vp:=S.vp) (prims:=withHash P₀ f) (optRand:=fun _ => pure default) seeds b
  rw [eq] at a c
  have h := IsQueryBoundP.of_imp (p':=fun i => isChalI i ∨ Open.isColl i) (fun i (v : i.isRight = true) => by
    rcases i with n|d|t
    · cases v
    · exact Or.inl trivial
    · exact Or.inr trivial) (a.or c)
  kexact h

theorem chain_choice_cost :
    IsQueryBoundP (wotsTcrPhase1 (vp:=S.vp) (prims:=P₀) seeds) (fun i => i.isRight = true)
      ((wotsInsts S.vp).length*(S.vp.params.len*1) +
        (wotsQc S.vp+(wotsInsts S.vp).length*(S.vp.params.len*(S.vp.params.w-1)))) := by
  let f : HashFns P₀ := ⟨(P₀).Thash,(P₀).Hmsg,(P₀).PRF,(P₀).PRFmsg⟩
  let b := Gen.dummyForger (vp:=S.vp) (prims:=withHash P₀ f) (optRand:=fun _ => pure default) (pkSeedDist:=seeds)
  have eq := wotsTcrT_phase1_q1_zero (vp:=S.vp) (prims:=P₀) (pkSeedDist:=seeds) f b
  have a := rTcrT_choose_chal (vp:=S.vp) (prims:=withHash P₀ f) (optRand:=fun _ => pure default) seeds b
  have c := rTcrT_choose_coll (vp:=S.vp) (prims:=withHash P₀ f) (optRand:=fun _ => pure default) seeds b
  rw [eq] at a c
  have h := IsQueryBoundP.of_imp (p':=fun i => isChalI i ∨ Open.isColl i) (fun i (v : i.isRight = true) => by
    rcases i with n|d|t
    · cases v
    · exact Or.inl trivial
    · exact Or.inr trivial) (a.or c)
  exact h.mono (by omega)
end Reduction.ShakePermutation.SparsePort.Wots
#print axioms Reduction.ShakePermutation.SparsePort.Wots.calls_budget
#print axioms Reduction.ShakePermutation.SparsePort.Wots.pre_choice_cost
