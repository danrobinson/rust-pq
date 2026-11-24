import Integration.SlhDsaLifetimeNumerator
import Integration.SlhDsaSetNumeric
import Integration.SlhDsaSetEuf

namespace Reduction.SetOracle
open MLink PQ.Interactive ENNReal
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-- Includes honest hash evaluations in the digest, FORS and WOTS+ reductions. -/
def lifetimeNumerator (S : Sha2Set) (q s l : ℕ) : ℕ :=
  let t := q + (componentCounts S.vp s).itsr
  (2*(2*t+1) + 2*t*2^l)^2 + otherNumerator S q s

/-- An integer certificate for the complete four-independent-component
signature game. Here 2^(2*l) upper bounds the number of signing requests. -/
theorem lifetime_certificate (S : Sha2Set) (q s l divisor : ℕ) (limit : s ≤ 2^64)
    (signings : s ≤ 2^(2*l))
    (cert : lifetimeNumerator S q s l * divisor ≤ 2^(8*S.vp.params.n)) :
    componentForgeryBound S q s ≤ (divisor : ℝ≥0∞)⁻¹ := by
  rw [componentForgeryBound_split]
  apply (add_le_add (ForsLifetime.digest_numerator S _ s l limit signings) le_rfl).trans
  rw [← ENNReal.add_div, ← Nat.cast_add]
  exact ForsLifetime.fraction_certificate _ _ _ cert

/-- Each pair gives (log₂ signing budget, forgery probability exponent) for
2^40 public quantum queries in the independent-component model. -/
def signingCheckpoint : Sha2Set → ℕ × ℕ
  | .s128s => (27,2) | .s128f => (30,2)
  | .s192s => (48,2) | .s192f => (51,1)
  | .s256s => (64,19) | .s256f => (64,25)

section Signature
variable (S : Sha2Set) (c : Caps) (rand : S.Node → S.Node → ProbComp S.Node)
    (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
    (F : PortForger (Input S c) (Output S) E)

theorem signature_of_lifetime_certificate (q s l divisor : ℕ) (limit : s ≤ 2^64)
    (signings : s ≤ 2^(2*l))
    (cert : lifetimeNumerator S q s l * divisor ≤ 2^(8*S.vp.params.n))
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) s)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (ht : max 2 (max S.vp.params.len S.vp.params.k) ≤ c.tl) :
    avg S c (fun g => qStrongUnforgeableAdvantage (forgerAt S c rand seeds F g)) ≤ (divisor : ℝ≥0∞)⁻¹ ∧
    avg S c (fun g => qUnforgeableAdvantage (forgerAt S c rand seeds F g)) ≤ (divisor : ℝ≥0∞)⁻¹ := by
  have bound := lifetime_certificate S q s l divisor limit signings cert
  exact ⟨(suf_closed S c rand seeds F _ _ hq hs hc ht).trans bound,
    (euf_closed S c rand seeds F _ _ hq hs hc ht).trans bound⟩

theorem signature_signing_checkpoint
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40))
    (hs : ∀ pk, CountBound isSign (F.main pk) (2^(signingCheckpoint S).1))
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (ht : max 2 (max S.vp.params.len S.vp.params.k) ≤ c.tl) :
    let bound := ((2:ℝ≥0∞)^(signingCheckpoint S).2)⁻¹
    avg S c (fun g => qStrongUnforgeableAdvantage (forgerAt S c rand seeds F g)) ≤ bound ∧
    avg S c (fun g => qUnforgeableAdvantage (forgerAt S c rand seeds F g)) ≤ bound := by
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using signature_of_lifetime_certificate S c rand seeds F
    _ _ (((signingCheckpoint S).1+1)/2) (2^(signingCheckpoint S).2)
    (by cases S <;> decide +kernel) (by cases S <;> decide +kernel) (by cases S <;> decide +kernel) hq hs hc ht

theorem wide_lifetime_signature (wide : S.vp.params.n = 32)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^94)) (hs : ∀ pk, CountBound isSign (F.main pk) (2^64))
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (ht : max 2 (max S.vp.params.len S.vp.params.k) ≤ c.tl) :
    avg S c (fun g => qStrongUnforgeableAdvantage (forgerAt S c rand seeds F g)) ≤ (3:ℝ≥0∞)⁻¹ ∧
    avg S c (fun g => qUnforgeableAdvantage (forgerAt S c rand seeds F g)) ≤ (3:ℝ≥0∞)⁻¹ :=
  signature_of_lifetime_certificate S c rand seeds F _ _ 32 3 le_rfl le_rfl
    (by cases S <;> first | contradiction | decide +kernel) hq hs hc ht
end Signature

end Reduction.SetOracle
#print axioms Reduction.SetOracle.signature_signing_checkpoint
#print axioms Reduction.SetOracle.wide_lifetime_signature
