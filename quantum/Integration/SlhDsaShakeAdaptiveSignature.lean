import Integration.SlhDsaShakeAdaptiveItsr
import Integration.SlhDsaShakeLifetimeCertificate
import Integration.SlhDsaSetLifetime

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

variable (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)

/-- Adaptive byte-signature security in one shared ideal XOF, with an integer
certificate for arbitrary public and signing budgets through the key lifetime. -/
theorem adaptive_signature_bound (q s l : ℕ) (c : Caps) (msg : c.ml = 65536)
    (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (life : s ≤ 2^64) (signings : s ≤ 2^(2*l)) :
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ ((adaptiveNumerator S q s l : ℝ≥0∞) / 2^(8*S.vp.params.n)) ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ ((adaptiveNumerator S q s l : ℝ≥0∞) / 2^(8*S.vp.params.n)) := by
  have fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N := by
    intro k hk
    apply le_trans _ cap
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> cases S <;> decide +kernel
  obtain ⟨strong,ordinary⟩ := signature_repeated S N rand seeds F q s c (by omega) fit hq hs hc
  have digest := ShakeAdaptive.signature_itsr S N rand seeds F q s c (by omega) hq hs hc
  have risk := digest.trans (ForsLifetime.digest_numerator S _ s l life signings)
  constructor <;> first | apply strong.trans | apply ordinary.trans
  all_goals
    rw [repeatedLoss_split]
    exact (add_le_add risk le_rfl).trans_eq (by rw [← ENNReal.add_div,← Nat.cast_add]; rfl)

theorem adaptive_signature (q s l divisor : ℕ) (c : Caps) (msg : c.ml = 65536)
    (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (life : s ≤ 2^64) (signings : s ≤ 2^(2*l))
    (cert : adaptiveNumerator S q s l * divisor ≤ 2^(8*S.vp.params.n)) :
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ (divisor:ℝ≥0∞)⁻¹ ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ (divisor:ℝ≥0∞)⁻¹ := by
  obtain ⟨strong,ordinary⟩ := adaptive_signature_bound S N rand seeds F q s l c msg cap hq hs hc life signings
  have limit := ForsLifetime.fraction_certificate (adaptiveNumerator S q s l) divisor (8*S.vp.params.n) cert
  exact ⟨strong.trans limit,ordinary.trans limit⟩

theorem signature_signing_checkpoint (c : Caps) (msg : c.ml = 65536) (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) (2^(SetOracle.signingCheckpoint S).1))
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    let bound := ((2:ℝ≥0∞)^(SetOracle.signingCheckpoint S).2)⁻¹
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ bound ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ bound := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using adaptive_signature S N rand seeds F _ _
    (((SetOracle.signingCheckpoint S).1+1)/2) (2^(SetOracle.signingCheckpoint S).2)
    c msg cap hq hs hc (by cases S <;> decide +kernel) (by cases S <;> decide +kernel)
    (by cases S <;> decide +kernel)

/-- Retain a constant-success query lower bound after up to 2^20
signatures, or use the tighter one-signature bound. -/
theorem signature_work_checkpoints (many : Bool) (c : Caps) (msg : c.ml = 65536)
    (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^(4*S.vp.params.n-(if many then 12 else 5))))
    (hs : ∀ pk, CountBound isSign (F.main pk) (if many then 2^20 else 1))
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) < 1/2 ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) < 1/2 := by
  let q := 2^(4*S.vp.params.n-(if many then 12 else 5))
  let s := if many then 2^20 else 1
  let l := if many then 10 else 0
  -- Use the integer numerator itself to retain the strict inequality at 1/2.
  let numerator := adaptiveNumerator S q s l
  have small : numerator * 2 < 2^(8*S.vp.params.n) := by cases S <;> cases many <;> decide +kernel
  have life : s ≤ 2^64 := by cases many <;> decide +kernel
  have signings : s ≤ 2^(2*l) := by cases many <;> decide +kernel
  obtain ⟨strong,ordinary⟩ := adaptive_signature_bound S N rand seeds F q s l c msg cap hq hs hc life signings
  have bound : (numerator:ℝ≥0∞)/2^(8*S.vp.params.n) < 1/2 := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by norm_num)).mp
    simp only [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
    rw [div_lt_div_iff₀ (by positivity) (by positivity),one_mul]
    exact_mod_cast small
  exact ⟨strong.trans_lt bound,ordinary.trans_lt bound⟩

/-- A full key lifetime for both SHAKE-256 sets, with enough public quantum
queries to test a constant-success work threshold. -/
theorem wide_lifetime_signature (wide : S.vp.params.n = 32) (c : Caps) (msg : c.ml = 65536)
    (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^94)) (hs : ∀ pk, CountBound isSign (F.main pk) (2^64))
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ (3:ℝ≥0∞)⁻¹ ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ (3:ℝ≥0∞)⁻¹ :=
  adaptive_signature S N rand seeds F _ _ 32 3 c msg cap hq hs hc le_rfl le_rfl
    (by cases S <;> first | contradiction | decide +kernel)

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.signature_signing_checkpoint
#print axioms Reduction.ShakeXof.wide_lifetime_signature
#print axioms Reduction.ShakeXof.signature_work_checkpoints
