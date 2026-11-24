import Integration.SlhDsaCompressionHmac256Trunc
import Integration.SlhDsaCompressionDigestCollision

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker ComplexOrder

variable {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

/-- The monitor sees the same public table and the same classical message queries
as the ideal PRF experiment. A win carries two distinct queries with equal inner digest. -/
noncomputable def digestCollisionPr (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool)
    (M : Matrix Work Work ℂ) (g : CompressionTables) (i : St) : ℝ≥0∞ :=
  let h := innerDigest g i
  qWeight (fun v => DigestCollision.found h v = true)
    (DigestCollision.watch (W := Work) (α := Bool) (R := (Bytes 16)) h (A (oracle g)) (fun _ => none) ∅) M

/-- Quantum PRF bound for the actual SHA-256 HMAC implementation, with the remaining
loss expressed as an explicit inner-digest collision experiment. -/
theorem hmac_collision (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool)
    (q : ℕ) (hA : PUE (messageCharge) A q) (ρ : SubState ((Input × Output) × E)) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (msgPrf Sha2Set.s128s.vp (randPrims (functions Sha2Set.s128s g))) (A (oracle g)) M) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g)) M) +
      (∑ g : CompressionTables, unifW _ g * ∑ i : St, unifW _ i * digestCollisionPr A M g i) +
      ENNReal.ofReal (8*(q:ℝ)^2 / 2^256) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^128) := by
  intro M
  have hm : M.PosSemidef := (ρ.prod (SubState.basis ())).posSemidef
  have per (g : CompressionTables) (i : St) := DigestCollision.eager_le_ideal_add_collision (R := (Bytes 16))
    (innerDigest g i) (A (oracle g)) M hm
  have sum (g : CompressionTables) :
      ((Fintype.card St : ℝ≥0∞)⁻¹ * ∑ i : St,
        (Fintype.card (St → (Bytes 16)) : ℝ≥0∞)⁻¹ * ∑ f : St → (Bytes 16),
         qWeight (· = true) (ansRun (fun d => f (innerDigest g i d)) (A (oracle g))) M) ≤
      qPrfIdealPr (A (oracle g)) M + ∑ i : St, unifW _ i * digestCollisionPr A M g i := by
    rw [Finset.mul_sum]
    have h := Finset.sum_le_sum (s := Finset.univ) fun i _ => mul_le_mul' (a := unifW _ i) le_rfl (per g i)
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_unifW, one_mul] at h
    kexact h
  have hh := Finset.sum_le_sum (s := Finset.univ) fun g _ => mul_le_mul' (a := unifW _ g) le_rfl (sum g)
  simp only [mul_add, Finset.sum_add_distrib] at hh
  exact (hmac_digest_game A q hA ρ).trans (add_le_add_left (add_le_add_left hh _) _)

end Reduction.Compression.Hmac256


#print axioms Reduction.Compression.Hmac256.hmac_collision
