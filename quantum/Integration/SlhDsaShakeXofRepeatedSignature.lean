import Integration.SlhDsaShakeCoverSubset
import Integration.SlhDsaShakeXofRepeated
namespace Reduction.ShakeSingle
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum QMsg QItsr KeyedHash
open scoped ComplexOrder
open Classical

variable (S : Sha2Set) (N : ℕ) {E : Type} [Fintype E] [DecidableEq E]
  (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
local notation "Q" => fun H => qPureBytesToInternal (ShakeApi.rawForger S N r seeds F H)
local notation "P" => fun H => ShakeApi.primitives S (ShakeApi.extend H)

theorem signature_itsr_subset (c : Caps) (raw : 3*S.vp.params.n+c.ml ≤ N) (q s d : ℕ) (many : s*d < S.vp.params.k)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun H => qItsrAdvantage (itsrProblem S.vp (P H)) (qbItsrL (Q H)) F.ρ₀) ≤
      subsetLoss S (q+itsrHashes S.vp s) s d := by
  apply signature_of_search S N r seeds F c raw q s hq hs hc
  exact fun M cost scope => subset_search S N s d many M _ cost scope F.ρ₀ F.posSemidef F.trace_eq_one

end Reduction.ShakeSingle

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal

theorem repeated_queries (S : Sha2Set) (N : ℕ)
    (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
    (q s d : ℕ) (many : s*d < S.vp.params.k) (c : Caps) (raw : 3*S.vp.params.n+c.ml ≤ N)
    (fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let bound := repeatedLoss S q s (ShakeSingle.subsetLoss S (q+itsrHashes S.vp s) s d)
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤ bound ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤ bound := by
  obtain ⟨strong,ordinary⟩ := signature_repeated S N r seeds F q s c (by omega) fit hq hs hc
  have cover := ShakeSingle.signature_itsr_subset S N r seeds F c raw q s d many hq hs hc
  apply And.intro (strong.trans ?_) (ordinary.trans ?_) <;> dsimp only [repeatedLoss] <;> gcongr <;> exact cover
end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.repeated_queries
