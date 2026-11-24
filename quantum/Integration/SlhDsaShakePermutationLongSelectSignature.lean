import Integration.SlhDsaShakePermutationLongSelectGame

/-! The native long-arity signature terms reduced to bounded search on a clean posterior permutation. -/
namespace Reduction.ShakePermutation.Long.SelectTrace
open Classical Classic SparsePort OracleSpec OracleComp SLHDSA SLHDSA.Security MLink TweakableHash PQ.Interactive Quantum SetOracle ENNReal PermutationConditioning
open scoped ComplexOrder
noncomputable section
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] arityTargets tcrTargets Select.choice Phase.erase Select.prog
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
attribute [local instance] extFT
variable (S : Sha2Set) (ar : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "T₀" => (fun _ : ShakeApi.Input N => (default : Bytes S.vp.params.m))
local notation "B" => fun π : Permutation => qPureBytesToInternal (SkCost.capped S rand seeds F N π)
local notation "A" => Memo.selection S ar seeds F
local notation "M" => fun H st pk => Memo.machine S N rand F T₀ ar st pk H

def ResidualBudget (q Q : ℕ) (b : ℝ≥0∞) : Prop := ∀ (t : Trace) (_ : Nonempty (Extensions t))
    (dest : List Rate → Option S.Node) (p : (ℕ × Arity.Msg S ar) → List Rate)
    (m : (Port → Words) → Closed (ArityGame.Work E) (ℕ × Arity.Msg S ar))
    (ρ : Matrix (ArityGame.Work E) (ArityGame.Work E) ℂ), ρ.PosSemidef → ρ.trace=1 →
    PUE (spec:=unifSpec) cnt0 m q → t.length ≤ Q → ¬bad (SkFormat.split S) dest t →
    (∀ jm, (p jm).length ≤ 17) → uniformMean (fun π : Extensions t =>
      qWeight (fun jm => hits S dest π.val (p jm)) (m (oracle π.val)) ρ) ≤ b

theorem signature (h : ar ≤ 67) (b : ℝ≥0∞)
    (residual : ResidualBudget (E:=E) S ar (2^41) (2^100) b)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    uniformMean (fun π => qSM_DT_TCR_Advantage (qbTcrArM ar (B π))) ≤
      b+((17*tcrTargets S.vp : ℕ):ℝ≥0∞)*forestPenalty Rate Words (17*tcrTargets S.vp) := by
  let q := 2^40 + 483 * tcrMHashes S.vp 1
  let Q := 17*tcrTargets S.vp
  simp_rw [Memo.cap_advantage S ar rand seeds F _ h]
  apply total S ar seeds A M h Q b
  · intro pk; kexact Select.native_cost S ar pk (ShakeApi.extend T₀)
  · intro pk t comp dest ps st sz clean lim
    have hm : PUE (spec:=unifSpec) cnt0 (fun H => Memo.machine S N rand F T₀ ar st pk H) q := by
      kexact Memo.machine_cost S N rand F T₀ (le_refl N) ar st pk (2^40) 1 hq hs
    exact residual t comp dest ps _ (A).ρ₀ (A).posSemidef (A).trace_eq_one (hm.mono (ArityGame.memo_queries S))
      (sz.trans (Select.benchmark_calls S)) clean lim
end
end Reduction.ShakePermutation.Long.SelectTrace
#print axioms Reduction.ShakePermutation.Long.SelectTrace.signature
