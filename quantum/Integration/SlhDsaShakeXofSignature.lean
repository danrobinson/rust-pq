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
theorem signature_benchmark (c : Caps) (msg : c.ml = 65536)
    (cap : 65536 + 3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤ ((2:ℝ≥0∞)^36)⁻¹ ∧
    uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤ ((2:ℝ≥0∞)^36)⁻¹ := by
  have short : 2*S.vp.params.n+32 ≤ N := by omega
  have fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N := by
    intro k hk
    apply le_trans _ cap
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> cases S <;> decide +kernel
  obtain ⟨ds,fv,ar,ud,pre,chain⟩ := benchmark_hash_games S N r seeds F fit hq hs
  exact compose_benchmark S N r seeds F c (by omega) hq hs hc
    (by simpa only [ShakeApi.prfLoss,Nat.cast_pow,Nat.cast_ofNat] using ShakeApi.secret_prf_benchmark S N r seeds F short hq hs)
    (by simpa only [ShakeApi.prfLoss,Nat.cast_pow,Nat.cast_ofNat] using ShakeApi.message_prf_benchmark S N r seeds F c (by omega) hq hs hc)
    ds fv ar ud pre chain

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.signature_benchmark
