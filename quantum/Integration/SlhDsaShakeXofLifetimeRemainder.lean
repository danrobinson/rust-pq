import Integration.SlhDsaShakeXofRepeated

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

/-- Exponents for the terms other than digest covering at the full signing
budget. The remainder theorem applies to the four sets with at least 24-byte nodes. -/
def lifetimeRemainderBits : Sha2Set → ℕ
  | .s128s | .s128f => 0
  | .s192s => 13 | .s192f => 21
  | .s256s => 77 | .s256f => 83

theorem lifetime_remainder (S : Sha2Set) (width : 24 ≤ S.vp.params.n) (risk : ℝ≥0∞) :
    repeatedLoss S (2^40) (2^64) risk ≤ risk + ((2:ℝ≥0∞)^lifetimeRemainderBits S)⁻¹ := by
  have numeric : repeatedLoss S (2^40) (2^64) 0 ≤ ((2:ℝ≥0∞)^lifetimeRemainderBits S)⁻¹ := by
    unfold repeatedLoss repeatedLossWithPrfs epsTcr SetOracle.epsPreSet SetOracle.epsUdSet
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add, ENNReal.toReal_div,
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal, ENNReal.toReal_one, ENNReal.toReal_zero, ENNReal.toReal_natCast]
    field_simp
    norm_cast
    cases S <;> revert width <;> decide +kernel
  calc
    _ = risk + repeatedLoss S (2^40) (2^64) 0 := by unfold repeatedLoss repeatedLossWithPrfs; simp only [add_zero]; ac_rfl
    _ ≤ _ := add_le_add_right numeric risk

/-- Both byte-level forgery probabilities are at most the actual adaptive
digest-covering probability plus the set-specific remainder. The random
table is shared by all public hash queries and all signing requests. -/
theorem signature_lifetime_remainder (S : Sha2Set) (width : 24 ≤ S.vp.params.n) (N : ℕ)
    (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
    (c : Caps) (msg : c.ml = 65536) (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) (2^64))
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let A := ShakeApi.rawForger S N r seeds F
    let risk := SetOracle.uniformMean (fun H => qItsrAdvantage
      (itsrProblem S.vp (ShakeApi.primitives S (ShakeApi.extend H))) (qbItsrL (qPureBytesToInternal (A H))) F.ρ₀)
    let bound := risk + ((2:ℝ≥0∞)^lifetimeRemainderBits S)⁻¹
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (A H)) ≤ bound ∧
      SetOracle.uniformMean (fun H => qUnforgeableAdvantage (A H)) ≤ bound := by
  have fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N := by
    intro k hk
    apply le_trans _ cap
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> cases S <;> decide +kernel
  obtain ⟨strong,ordinary⟩ := signature_repeated S N r seeds F (2^40) (2^64) c (by omega) fit hq hs hc
  exact ⟨strong.trans (lifetime_remainder S width _), ordinary.trans (lifetime_remainder S width _)⟩

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.signature_lifetime_remainder
