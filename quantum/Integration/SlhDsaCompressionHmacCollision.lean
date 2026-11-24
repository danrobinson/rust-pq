import Integration.SlhDsaCompressionDigestCollision

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Reduction.Compression.HmacKey
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker ComplexOrder

variable (S : Sha2Set) {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

/-- The monitor sees the same public table and the same classical message queries
as the ideal PRF experiment. A win carries two distinct queries with equal inner digest. -/
noncomputable def digestCollisionPr (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool)
    (M : Matrix Work Work ℂ) (g : CompressionTables) (i : Chain512) : ℝ≥0∞ :=
  let h := innerDigest S g i
  qWeight (fun v => DigestCollision.found h v = true)
    (DigestCollision.watch (W := Work) (α := Bool) (R := S.Node) h (A (oracle g)) (fun _ => none) ∅) M

/-- Quantum PRF bound for the actual SHA-512 HMAC implementation, with the remaining
loss expressed as an explicit inner-digest collision experiment. -/
theorem wide_hmac_collision (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec (S.Node × List Byte) S.Node) Bool) (hw : S.vp.params.n ≠ 16)
    (q : ℕ) (hA : PUE (messageCharge S) A q) (ρ : SubState ((Input × Output) × E)) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (msgPrf S.vp (randPrims (functions S g))) (A (oracle g)) M) ≤
    (∑ g : CompressionTables, unifW _ g * qPrfIdealPr (A (oracle g)) M) +
      (∑ g : CompressionTables, unifW _ g * ∑ i : Chain512, unifW _ i * digestCollisionPr S A M g i) +
      ENNReal.ofReal (8*(q:ℝ)^2 / 2^512) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  intro M
  have hm : M.PosSemidef := (ρ.prod (SubState.basis ())).posSemidef
  have per (g : CompressionTables) (i : Chain512) := DigestCollision.eager_le_ideal_add_collision (R := S.Node)
    (innerDigest S g i) (A (oracle g)) M hm
  have sum (g : CompressionTables) :
      ((Fintype.card Chain512 : ℝ≥0∞)⁻¹ * ∑ i : Chain512,
        (Fintype.card (Chain512 → S.Node) : ℝ≥0∞)⁻¹ * ∑ f : Chain512 → S.Node,
         qWeight (· = true) (ansRun (fun d => f (innerDigest S g i d)) (A (oracle g))) M) ≤
      qPrfIdealPr (A (oracle g)) M + ∑ i : Chain512, unifW _ i * digestCollisionPr S A M g i := by
    rw [Finset.mul_sum]
    have h := Finset.sum_le_sum (s := Finset.univ) fun i _ => mul_le_mul' (a := unifW _ i) le_rfl (per g i)
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_unifW, one_mul] at h
    kexact h
  have hh := Finset.sum_le_sum (s := Finset.univ) fun g _ => mul_le_mul' (a := unifW _ g) le_rfl (sum g)
  simp only [mul_add, Finset.sum_add_distrib] at hh
  exact (wide_hmac_digest_game S hw A q hA ρ).trans (add_le_add_left (add_le_add_left hh _) _)

end Reduction.Compression.HmacKey


#print axioms Reduction.Compression.HmacKey.wide_hmac_collision
