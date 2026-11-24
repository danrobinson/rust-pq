import Integration.SlhDsaShakeXofRepeatedSignature

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
set_option exponentiation.threshold 2048
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

def twoSignatureBits : Sha2Set → ℕ
  | .s128s => 10 | .s128f => 12 | .s192s => 49
  | .s192f => 46 | .s256s => 73 | .s256f => 72

private abbrev coordinates (S : Sha2Set) := (S.vp.params.k-1)/2

theorem twoSignatureLoss (S : Sha2Set) :
    repeatedLoss S (2^40) 2 (ShakeSingle.subsetLoss S (2^40+itsrHashes S.vp 2) 2 (coordinates S)) ≤
      ((2:ℝ≥0∞)^(twoSignatureBits S))⁻¹ := by
  unfold repeatedLoss repeatedLossWithPrfs epsTcr SetOracle.epsPreSet SetOracle.epsUdSet ShakeSingle.subsetLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add,ENNReal.toReal_div,ENNReal.toReal_mul,
    ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal,ENNReal.toReal_one,
    ENNReal.toReal_natCast]
  field_simp
  norm_cast
  cases S <;> decide +kernel

theorem two_signature_benchmark (S : Sha2Set) (N : ℕ)
    (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
    (c : Caps) (msg : c.ml = 65536) (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 2)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤
      ((2:ℝ≥0∞)^(twoSignatureBits S))⁻¹ ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N r seeds F H)) ≤
      ((2:ℝ≥0∞)^(twoSignatureBits S))⁻¹ := by
  have fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N := by
    intro k hk
    apply le_trans _ cap
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> cases S <;> decide +kernel
  obtain ⟨a,b⟩ := repeated_queries S N r seeds F (2^40) 2 (coordinates S) (by cases S <;> decide +kernel)
    c (by omega) fit hq hs hc
  exact ⟨a.trans (twoSignatureLoss S),b.trans (twoSignatureLoss S)⟩
/-- At the FIPS lifetime signing budget this particular subset estimate is
already vacuous even with zero public queries. It is a limitation of the
reduction's accounting, not a lower bound on forgery probability. -/
theorem lifetime_subset_vacuous (S : Sha2Set) (d : ℕ) (many : 2^64*d < S.vp.params.k) :
    1 ≤ ShakeSingle.subsetLoss S (itsrHashes S.vp (2^64)) (2^64) d := by
  have k : S.vp.params.k ≤ 35 := by cases S <;> decide +kernel
  have zero : d = 0 := by omega
  subst d
  unfold ShakeSingle.subsetLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := positivity) only [ENNReal.toReal_one,ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal]
  field_simp
  norm_cast
  cases S <;> decide +kernel

/-- Even a perfect covering bound would leave the secret-key PRF estimate
vacuous for 128-bit sets if the honest signing work is charged at the public
quantum query rate throughout a full key lifetime. -/
theorem lifetime_secret_prf_cost (S : Sha2Set) (width : S.vp.params.n = 16) :
    1 ≤ ENNReal.ofReal (8*(ShakeApi.Sk.budget S 0 (2^64):ℝ)^2 / 2^(8*S.vp.params.n)) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := positivity) only [ENNReal.toReal_ofReal,ENNReal.toReal_one]
  field_simp
  norm_cast
  cases S <;> revert width <;> decide +kernel

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.two_signature_benchmark
#print axioms Reduction.ShakeXof.lifetime_subset_vacuous
#print axioms Reduction.ShakeXof.lifetime_secret_prf_cost
