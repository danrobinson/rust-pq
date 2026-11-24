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
def rootNumerator (S : Sha2Set) (q s root : ℕ) : ℕ :=
  let t := q + itsrHashes S.vp s
  (2*(2*t+1) + 2*t*root)^2 + hashNumerator S q s

theorem adaptive_signature_root_bound (q s root : ℕ) (c : Caps) (msg : c.ml = 65536)
    (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (life : s ≤ 2^64) (signings : s ≤ root^2) :
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ ((rootNumerator S q s root : ℝ≥0∞) / 2^(8*S.vp.params.n)) ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ ((rootNumerator S q s root : ℝ≥0∞) / 2^(8*S.vp.params.n)) := by
  have fit : ∀ k ∈ [1,2,S.vp.params.len,S.vp.params.k], S.vp.params.n+32+S.vp.params.n*k ≤ N := by
    intro k hk
    apply le_trans _ cap
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl <;> cases S <;> decide +kernel
  obtain ⟨strong,ordinary⟩ := signature_repeated S N rand seeds F q s c (by omega) fit hq hs hc
  have digest := ShakeAdaptive.signature_itsr S N rand seeds F q s c (by omega) hq hs hc
  have risk := (digest.trans (ForsLifetime.adaptive_digest_loss S _ s life)).trans
    (ForsLifetime.search_programming_numerator_root S _ _ s root _ le_rfl signings)
  constructor <;> first | apply strong.trans | apply ordinary.trans
  all_goals
    rw [repeatedLoss_split]
    exact (add_le_add risk le_rfl).trans_eq (by rw [← ENNReal.add_div,← Nat.cast_add]; rfl)

theorem adaptive_signature_bound (q s l : ℕ) (c : Caps) (msg : c.ml = 65536)
    (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (life : s ≤ 2^64) (signings : s ≤ 2^(2*l)) :
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ ((adaptiveNumerator S q s l : ℝ≥0∞) / 2^(8*S.vp.params.n)) ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) ≤ ((adaptiveNumerator S q s l : ℝ≥0∞) / 2^(8*S.vp.params.n)) :=
  adaptive_signature_root_bound S N rand seeds F q s (2^l) c msg cap hq hs hc life
    (by simpa only [← pow_mul,Nat.mul_comm l 2] using signings)

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


/-- Largest public query budget at the published signing checkpoint for which
the integer-square-root numerator proves success strictly below one half. -/
def halfQueryLimit : Sha2Set → ℕ
  | .s128s => 293388967768505
  | .s128f => 82147135819652
  | .s192s => 737457372386111934837
  | .s192f => 209505175649276092849
  | .s256s => 27959888141640534890193014032
  | .s256f => 28005348482203225446220823890

theorem halfQueryLimit_iff (q : ℕ) :
    let k := (SetOracle.signingCheckpoint S).1
    2 * rootNumerator S q (2^k) (1+Nat.sqrt (2^k-1)) < 2^(8*S.vp.params.n) ↔ q ≤ halfQueryLimit S := by
  dsimp only
  let k := (SetOracle.signingCheckpoint S).1
  let f := fun x => 2 * rootNumerator S x (2^k) (1+Nat.sqrt (2^k-1))
  have mono : Monotone f := by
    intro x y h
    dsimp [f,rootNumerator,hashNumerator,ShakeApi.Sk.budget,ShakeApi.Msg.budget]
    gcongr
  have below : f (halfQueryLimit S) < 2^(8*S.vp.params.n) := by cases S <;> decide +kernel
  have above : 2^(8*S.vp.params.n) ≤ f (halfQueryLimit S + 1) := by cases S <;> decide +kernel
  constructor
  · intro h
    by_contra! larger
    exact (not_lt_of_ge (above.trans (mono larger))) h
  · exact fun h => (mono h).trans_lt below

theorem signature_halfQueryLimit (c : Caps) (msg : c.ml = 65536)
    (cap : 65536+3*S.vp.params.n ≤ N)
    (hq : ∀ pk, CountBound isPort (F.main pk) (halfQueryLimit S))
    (hs : ∀ pk, CountBound isSign (F.main pk) (2^(SetOracle.signingCheckpoint S).1))
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun H => qStrongUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) < 1/2 ∧
    SetOracle.uniformMean (fun H => qUnforgeableAdvantage (ShakeApi.rawForger S N rand seeds F H)) < 1/2 := by
  let k := (SetOracle.signingCheckpoint S).1
  obtain ⟨strong,ordinary⟩ := adaptive_signature_root_bound S N rand seeds F (halfQueryLimit S) (2^k) (1+Nat.sqrt (2^k-1))
    c msg cap hq hs hc (by cases S <;> decide +kernel) (by cases S <;> decide +kernel)
  apply And.intro (strong.trans_lt ?_) (ordinary.trans_lt ?_)
  all_goals
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by norm_num)).mp
    simp only [ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
    rw [div_lt_div_iff₀ (by positivity) (by positivity),one_mul,mul_comm]
    exact_mod_cast (halfQueryLimit_iff S (halfQueryLimit S)).2 le_rfl

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.signature_signing_checkpoint
#print axioms Reduction.ShakeXof.wide_lifetime_signature
#print axioms Reduction.ShakeXof.signature_work_checkpoints
#print axioms Reduction.ShakeXof.halfQueryLimit_iff
#print axioms Reduction.ShakeXof.signature_halfQueryLimit
