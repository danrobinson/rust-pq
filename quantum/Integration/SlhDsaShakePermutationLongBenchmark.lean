import Integration.SlhDsaShakePermutationLongSignature
import Integration.SlhDsaShakePermutationLongBankInner

/-! Strong and existential forgery bounds for all six pure SHAKE parameter
sets with a shared two-way ideal permutation and one classical signing query. -/
namespace Reduction.ShakePermutation.Long
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal SetOracle SparsePort
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] arityTargets tcrTargets Select.choice Phase.erase Select.prog
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "T₀" => (fun _ : ShakeApi.Input N => (default : Bytes S.vp.params.m))

theorem signature_arity (ar : ℕ) (ha : ar ≤ 67)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1) :
    arityTerm S rand seeds F ar ≤ ((2:ℝ≥0∞)^27)⁻¹ := by
  apply arity_of_inner S rand seeds F ar ha
  intro pk π hp he
  apply BankRun.salted_inner S ar seeds (Memo.selection S ar seeds F)
    (fun H st pk => Memo.machine S N rand F T₀ ar st pk H) pk π hp he ha
    (17*tcrTargets S.vp) (Select.benchmark_calls S)
  · kexact Select.native_cost S ar pk (ShakeApi.extend T₀)
  · intro st
    exact (Memo.machine_cost S N rand F T₀ (le_refl N) ar st pk (2^40) 1 hq hs).mono (ArityGame.memo_queries S)

theorem signature_benchmark (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let bound := ((2:ℝ≥0∞)^18)⁻¹ + ((2:ℝ≥0∞)^25)⁻¹
    strongAdvantage S rand seeds F ≤ bound ∧ advantage S rand seeds F ≤ bound :=
  compose S rand seeds F c msg hq hs hc (fun ar ha => signature_arity S rand seeds F ar ha hq hs)

end Reduction.ShakePermutation.Long
#print axioms Reduction.ShakePermutation.Long.signature_arity
#print axioms Reduction.ShakePermutation.Long.signature_benchmark
