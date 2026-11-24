import Integration.SlhDsaForsLifetime

namespace Reduction.ForsLifetime
open MLink SLHDSA PQ.QROM Quantum ENNReal Num

/-- A full-lifetime bound for the adaptive digest game. Here q counts every
quantum query made by the digest-game machine, including any introduced by a
reduction from another game. The target queries consume a separate budget s. -/
theorem digest_bound_at_lifetime (S : Sha2Set) (q s b : ℕ)
    (limit : s ≤ 2^64) (qcap : 2*q+1 ≤ 2^b) (enough : b+1 ≤ 4*S.vp.params.n-32) :
    itsrBound S.vp.params q s ≤ ((2:ℝ≥0∞)^(2*(4*S.vp.params.n-32-b-1)))⁻¹ := by
  let m := 4*S.vp.params.n-32
  let u : ℝ≥0∞ := ((2:ℝ≥0∞)^(m-b))⁻¹
  have hb : b+1 ≤ m := enough
  have hq : 2*(q:ℝ≥0∞)+1 ≤ 2^b := by exact_mod_cast qcap
  have hs : (s:ℝ≥0∞) ≤ 2^64 := by exact_mod_cast limit
  have hC : 2*m ≤ coverageBits S := by cases S <;> decide
  have hN : 64 ≤ 8*S.vp.params.n := by cases S <;> decide
  have hM : 8*S.vp.params.n-64 = m*2 := by cases S <;> decide
  have cover : ((2:ℝ≥0∞)^coverageBits S)⁻¹ ≤ (((2:ℝ≥0∞)^m)⁻¹)^2 := by
    rw [inv_two_pow_pow]
    apply inv_two_pow_le
    omega
  have target : (s:ℝ≥0∞)*((2:ℝ≥0∞)^(8*S.vp.params.n))⁻¹ ≤ (((2:ℝ≥0∞)^m)⁻¹)^2 := by
    apply (mul_le_mul' hs le_rfl).trans_eq
    rw [two_pow_mul_inv 64 _ hN,inv_two_pow_pow,hM]
  have hu : (2:ℝ≥0∞)^b*((2:ℝ≥0∞)^m)⁻¹ = u := two_pow_mul_inv _ _ (by omega)
  apply (adaptive_digest_loss S q s limit).trans
  calc _ ≤ (u+u)^2 := by
          apply pow_le_pow_left₀ zero_le _ 2
          apply add_le_add
          · apply (ENNReal.rpow_le_rpow (mul_le_mul' (pow_le_pow_left₀ zero_le hq 2) cover)
              (by norm_num : 0 ≤ (2⁻¹:ℝ))).trans_eq
            rw [← mul_pow,sq_rpow_half,hu]
          · apply (mul_le_mul' (le_self_add.trans hq)
              (ENNReal.rpow_le_rpow target (by norm_num : 0 ≤ (2⁻¹:ℝ)))).trans_eq
            rw [sq_rpow_half,hu]
       _ = _ := by
         rw [← two_mul]
         have twice : (2:ℝ≥0∞)*((2:ℝ≥0∞)^(m-b))⁻¹ = ((2:ℝ≥0∞)^(m-b-1))⁻¹ := by
           simpa using two_pow_mul_inv 1 (m-b) (by omega)
         rw [show u = ((2:ℝ≥0∞)^(m-b))⁻¹ from rfl,twice,inv_two_pow_pow,Nat.mul_comm (m-b-1)]

/-- The numeric resource bound applies to adaptive quantum machines that
choose target messages in response to previous randomizers. -/
theorem adaptive_digest_game_at_lifetime (S : Sha2Set)
    {Xm : Type} [Fintype Xm] [DecidableEq Xm]
    {L : LocalSig.{1, 0}} {A : QReg} (I : L.Interp) (ρ : SubState A) (q s b : ℕ)
    (x : IAdv L (qromSpec (S.Node × Xm) (Bytes S.vp.params.m)) Xm S.Node
      (fun _ ↦ S.Node × Xm) s A) (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (limit : s ≤ 2^64) (qcap : 2*q+1 ≤ 2^b) (enough : b+1 ≤ 4*S.vp.params.n-32) :
    itsrAdaptiveExp I ρ s x (QItsr.SetDigest.idxCov S.vp) ≤
      ((2:ℝ≥0∞)^(2*(4*S.vp.params.n-32-b-1)))⁻¹ :=
  (itsr_digest_game_le S I ρ q s x hx).trans (digest_bound_at_lifetime S q s b limit qcap enough)

end Reduction.ForsLifetime
#print axioms Reduction.ForsLifetime.adaptive_digest_game_at_lifetime
