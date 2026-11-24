import Integration.SlhDsaCompressionHmac256Outer

namespace Reduction.Compression.Hmac256
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open scoped Kronecker

open HmacKey (mean mean_sum mean_comm mean_bound bool_mean)
variable {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Input Output E

/-- Reduce the real wide-set message PRF to a private random function evaluated on
the inner digest. Repeated digests receive the same answer. Both shared compression
tables remain public throughout the two game hops. -/
theorem hmac_to_inner
    (A : (Input → Output) → QOC Work (PRFScheme.PRFOracleSpec ((Bytes 16) × List Byte) (Bytes 16)) Bool)
    (q : ℕ) (hA : PUE (messageCharge) A q) (ρ : SubState ((Input × Output) × E)) :
    let M := ρ.matrix ⊗ₖ (SubState.basis ()).matrix
    (∑ g : CompressionTables, unifW _ g * qPrfRealPr (msgPrf Sha2Set.s128s.vp (randPrims (functions Sha2Set.s128s g))) (A (oracle g)) M) ≤
    (∑ g : CompressionTables, unifW _ g *
      ((Fintype.card St : ℝ≥0∞)⁻¹ * ∑ i : St,
       (Fintype.card (St → St) : ℝ≥0∞)⁻¹ * ∑ f : St → St,
         qWeight (· = true) (ansRun (fun d => truncate (f (innerDigest g i d))) (A (oracle g))) M)) +
    ENNReal.ofReal (8*(q:ℝ)^2 / 2^256) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^128) := by
  intro M
  let work := fun g st => qWeight (· = true) (messageRun A st (oracle g)) M
  let rest := fun g i => mean fun (f : St → St) => qWeight (· = true)
    (ansRun (fun d => truncate (f (innerDigest g i d))) (A (oracle g))) M
  have h := message_hop A q hA ρ
  have first : mean (fun g => mean (work g)) =
      mean (fun i => mean (fun g => mean (fun o => work g (fun b => if b then o else i)))) := by
    simp_rw [bool_mean (work _)]
    exact mean_comm _
  have second (i) : mean (fun g => mean (fun o => work g (fun b => if b then o else i))) ≤
      mean (fun g => rest g i) + ENNReal.ofReal (8*(q:ℝ)^2 / 2^256) := by
    rw [mean_sum (fun g => mean _), mean_sum (fun g => rest g i)]
    exact outer_message_hop A i q hA ρ
  have last := mean_bound second
  rw [← first, ← mean_comm rest, mean_sum (fun g => mean (work g)), mean_sum (fun g => mean (rest g))] at last
  exact h.trans (add_le_add_left last _)

end Reduction.Compression.Hmac256
#print axioms Reduction.Compression.Hmac256.hmac_to_inner
