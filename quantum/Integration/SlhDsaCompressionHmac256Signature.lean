import Integration.SlhDsaCompressionHmac256Search
import Integration.SlhDsaCompressionHmac256Budget

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)
open scoped ComplexOrder Kronecker

/-- The evidence machine uses three continuations' worth of work to monitor the
message queries and read back the two colliding paths. -/
noncomputable def loss (q : ℕ) : ℝ≥0∞ :=
  let B := q+(q+q)
  (2*(B:ℝ≥0∞)+1)^2/2^256 + 16*((B:ℝ≥0∞)+1)^3/2^256 +
    ENNReal.ofReal (8*(q:ℝ)^2/2^256) + ENNReal.ofReal (8*(q:ℝ)^2/2^128)

private theorem collect {a b c d e f : ℝ≥0∞} (h : a ≤ b+c+d+e) (hc : c ≤ f) : a ≤ b+(f+d+e) := by
  refine h.trans ?_
  rw [← add_assoc,← add_assoc]
  exact add_le_add (add_le_add (add_le_add le_rfl hc) le_rfl) le_rfl

variable {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

theorem message_bound (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec (Bytes 16 × List Byte) (Bytes 16)) Bool)
    (ρ : Matrix Work Work ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (q : ℕ) (hq : PUE messageCharge A q) :
    uniformMean (fun g => qPrfRealPr (msgPrf Sha2Set.s128s.vp (randPrims (functions Sha2Set.s128s g))) (A (oracle g)) ρ) -
      uniformMean (fun g => qPrfIdealPr (A (oracle g)) ρ) ≤ loss q := by
  classical
  obtain ⟨σ,hσ⟩ := exists_subState (A := (Input × Output) × E) ρ hp ht
  have h := hmac_collision A q hq σ
  dsimp only at h
  rw [← hσ] at h
  exact tsub_le_iff_left.mpr (collect h (inner_search A ρ hp ht q hq))

/-- Numerical message-PRF hop for the actual byte-level signing reduction of
both 128-bit parameter sets with coherent access to both compression tables. -/
theorem signature_bound (S : Sha2Set) (hn : S.vp.params.n = 16)
    (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)
    (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qPrfRealPr (msgPrf S.vp (randPrims (functions S g)))
      (qbPrfMsgWL sufCheck (reduced S rand seeds F g)) F.ρ₀) -
    uniformMean (fun g => qPrfIdealPr (qbPrfMsgWL sufCheck (reduced S rand seeds F g)) F.ρ₀) ≤
      loss (2*HmacKey.budget S c.ml q qs) := by
  have budget := signature_cost S rand seeds F c q qs hq hs hc
  simp only [← HmacKey.machine_oracle S rand seeds F]
  cases S <;> try contradiction
  case s128s =>
    have e : charge .s128s = messageCharge := by funext t; rcases t with n|⟨r,m⟩ <;> rfl
    rw [e] at budget
    exact message_bound _ F.ρ₀ F.posSemidef F.trace_eq_one _ budget
  case s128f =>
    have e : charge .s128f = messageCharge := by funext t; rcases t with n|⟨r,m⟩ <;> rfl
    rw [e] at budget
    exact message_bound _ F.ρ₀ F.posSemidef F.trace_eq_one _ budget

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.message_bound
#print axioms Reduction.Compression.Hmac256.signature_bound
