import Integration.SlhDsaShakeXofCompose
import Integration.SlhDsaShakeXofHashBenchmark
import Integration.SlhDsaShakeApiPrfBenchmark

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)
variable (S : Sha2Set) (N : ℕ) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)

/-- Strong and existential unforgeability of all six pure SHAKE byte APIs in
the shared ideal XOF model. The public port returns the full digest-width
prefix for any input up to N bytes. Shorter honest outputs read its prefix. -/
theorem signature_queries {q Q : ℕ} (room : q+2^22 ≤ Q) (c : Caps) (msg : c.ml = 65536)
    (cap : 65536 + 3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤ singleLoss S Q ∧
    uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤ singleLoss S Q := by
  have short : 2*S.vp.params.n+32 ≤ N := by omega
  have fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N := by
    intro k hk
    apply le_trans _ cap
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> cases S <;> decide +kernel
  obtain ⟨ds,fv,ar,ud,pre,chain⟩ := hash_games S N r seeds F room fit hq hs
  have honest : ShakeApi.Sk.budget S 0 1 ≤ 2^22 ∧ ShakeApi.Msg.budget S 0 1 ≤ 2^22 := by cases S <;> decide +kernel
  have sk : ShakeApi.Sk.budget S q 1 ≤ Q := by
    obtain ⟨h,_⟩ := honest
    unfold ShakeApi.Sk.budget at h ⊢
    omega
  have msgCost : ShakeApi.Msg.budget S q 1 ≤ Q := by
    obtain ⟨_,h⟩ := honest
    unfold ShakeApi.Msg.budget at h ⊢
    omega
  apply compose_queries S N r seeds F room c (by omega) hq hs hc _ _ ds fv ar ud pre chain
  · apply (ShakeApi.Sk.real_le_ideal S N r seeds F short _ _ hq hs).trans
    apply add_le_add le_rfl
    apply ENNReal.ofReal_le_ofReal
    gcongr
  · apply (ShakeApi.Msg.real_le_ideal S N r seeds F c (by omega) _ _ hq hs hc).trans
    apply add_le_add le_rfl
    apply ENNReal.ofReal_le_ofReal
    gcongr

/-- Strong and existential unforgeability of all six pure SHAKE byte APIs in
the shared ideal XOF model. The public port returns the full digest-width
prefix for any input up to N bytes. Shorter honest outputs read its prefix. -/
theorem signature_benchmark (c : Caps) (msg : c.ml = 65536)
    (cap : 65536 + 3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤ ((2:ℝ≥0∞)^36)⁻¹ ∧
    uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤ ((2:ℝ≥0∞)^36)⁻¹ := by
  obtain ⟨s,e⟩ := signature_queries (Q := 2^41) S N r seeds F (by decide) c msg cap hq hs hc
  exact ⟨s.trans (singleLoss_benchmark S),e.trans (singleLoss_benchmark S)⟩

/-- Security of the same signing API at a query budget enlarged for the public
permutation simulator. Each constituent reduction stays below 2^56 calls. -/
theorem signature_simulation (c : Caps) (msg : c.ml = 65536)
    (cap : 65536 + 3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^55))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤ ((2:ℝ≥0∞)^7)⁻¹ ∧
    uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤ ((2:ℝ≥0∞)^7)⁻¹ := by
  obtain ⟨s,e⟩ := signature_queries (Q := 2^56) S N r seeds F (by decide) c msg cap hq hs hc
  exact ⟨s.trans (singleLoss_simulation S),e.trans (singleLoss_simulation S)⟩

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.signature_benchmark
#print axioms Reduction.ShakeXof.signature_simulation
