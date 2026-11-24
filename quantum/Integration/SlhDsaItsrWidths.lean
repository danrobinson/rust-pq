import Integration.SlhDsaSetCounts

namespace Reduction

open SLHDSA MLink ENNReal PQ.QROM Quantum

/-- ITSR term for the FIPS digest split, with the randomizer width in bytes. -/
noncomputable def itsrBound (p : Params) (q s : ℕ) : ℝ≥0∞ :=
  (((2 * (q : ℝ≥0∞) + 1) ^ 2 *
    (∑ γ ∈ Finset.range (s + 1), (s.choose γ : ℝ≥0∞) *
      (((2 : ℝ≥0∞) ^ p.h)⁻¹) ^ γ * (1 - ((2 : ℝ≥0∞) ^ p.h)⁻¹) ^ (s - γ) *
      (1 - (1 - ((2 : ℝ≥0∞) ^ p.a)⁻¹) ^ γ) ^ p.k)) ^ (2⁻¹ : ℝ) +
    2 * q * ((s : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (8 * p.n))⁻¹) ^ (2⁻¹ : ℝ)) ^ 2

theorem itsrBound_128s (q s : ℕ) : itsrBound Link.vp.params q s = epsItsr Link.vp.params q s :=
  rfl

/-- A bound on an exact adaptive ITSR game. Linking a signature forger to this
game requires the digest parsing and oracle simulation proofs for its set. -/
theorem itsr_game_le (S : Sha2Set)
    {Xm Ix Lx : Type} [Fintype Xm] [DecidableEq Xm] [Fintype Ix] [DecidableEq Ix]
    [AddCommGroup Ix] [Fintype Lx] [DecidableEq Lx] [AddCommGroup Lx]
    {L : LocalSig.{1, 0}} {A : QReg} (I : L.Interp) (ρ : SubState A) (q s : ℕ)
    (x : IAdv L (qromSpec (S.Node × Xm) (Ix × (Fin S.vp.params.k → Lx))) Xm S.Node
      (fun _ ↦ S.Node × Xm) s A)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hi : Fintype.card Ix = 2 ^ S.vp.params.h) (hl : Fintype.card Lx = 2 ^ S.vp.params.a) :
    itsrAdaptiveExp I ρ s x (forsCov (I := Ix) (L := Lx) (k := S.vp.params.k)) ≤
      itsrBound S.vp.params q s := by
  have h := itsr4_adaptive_fors_le I ρ s x q hx
  have hk : Fintype.card S.Node = 2 ^ (8 * S.vp.params.n) := by
    rw [card_bytes', pow_mul]
    rfl
  simpa only [itsrBound, hi, hl, hk, Nat.cast_pow, Nat.cast_ofNat] using h

/-- The same bound with the actual FIPS byte digest and index extraction. -/
theorem itsr_digest_game_le (S : Sha2Set)
    {Xm : Type} [Fintype Xm] [DecidableEq Xm]
    {L : LocalSig.{1, 0}} {A : QReg} (I : L.Interp) (ρ : SubState A) (q s : ℕ)
    (x : IAdv L (qromSpec (S.Node × Xm) (Bytes S.vp.params.m)) Xm S.Node
      (fun _ ↦ S.Node × Xm) s A)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    itsrAdaptiveExp I ρ s x (QItsr.SetDigest.idxCov S.vp) ≤ itsrBound S.vp.params q s := by
  apply (itsr4_adaptive_le (I := I) (ρ := ρ) (Cov := QItsr.SetDigest.idxCov S.vp) ?_ hx).trans
  · have hc := QItsr.SetDigest.coverProb_idxCov_le S.vp s
    rw [coverProb_fors] at hc
    simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hc
    have hk : Fintype.card S.Node = 2 ^ (8 * S.vp.params.n) := by
      rw [card_bytes', pow_mul]
      rfl
    rw [hk, Nat.cast_pow, Nat.cast_ofNat]
    unfold itsrBound
    gcongr
  · intro a b u hab ha i hi
    obtain ⟨d, hd, hdi⟩ := ha i hi
    exact ⟨d, hab hd, hdi⟩

/-- Exponent bounding twice the total ITSR query count plus one at the benchmark. -/
def itsrQueryBits (S : Sha2Set) : ℕ :=
  Nat.log2 (2 * (2^40 + (componentCounts S.vp (2^20)).itsr) + 1) + 1

open Num in
/-- The ITSR term at 2^40 adversary queries and 2^20 signatures, including
the set-dependent key generation and signing cost of the ITSR reduction. -/
theorem itsrBound_sets_num (S : Sha2Set) :
    itsrBound S.vp.params (2^40 + (componentCounts S.vp (2^20)).itsr) (2^20) ≤
      ((2 : ℝ≥0∞)^(8 * S.vp.params.n - 2 * itsrQueryBits S - 22))⁻¹ := by
  let p := S.vp.params
  let q := 2^40 + (componentCounts S.vp (2^20)).itsr
  let b := itsrQueryBits S
  let e := 4 * p.n - 10 - b
  let u : ℝ≥0∞ := ((2 : ℝ≥0∞)^e)⁻¹
  have hq : 2 * q + 1 ≤ 2^b := by cases S <;> decide +kernel
  have h1 : 2 * (q : ℝ≥0∞) + 1 ≤ 2^b := by exact_mod_cast hq
  have h2 : 2 * (q : ℝ≥0∞) ≤ 2^b := le_self_add.trans h1
  have hcover : 20 + p.k + 1 ≤ p.h := by cases S <;> decide
  have hc := cover_sum_le (2^20) p.k (((2 : ℝ≥0∞)^p.h)⁻¹) (((2 : ℝ≥0∞)^p.a)⁻¹)
    (ENNReal.inv_le_one.2 (one_le_pow₀ one_le_two)) (by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [mul_right_comm, ← pow_add, two_pow_mul_inv _ _ (by omega)]
      simpa using inv_two_pow_le 1 (p.h - (20 + p.k)) (by omega))
  have hgeo : b * 2 + 1 + 2 * e ≤ p.a * p.k := by cases S <;> decide
  have hA : ((2 : ℝ≥0∞)^b)^2 * (2 * (((2 : ℝ≥0∞)^p.a)⁻¹)^p.k) ≤ u^2 := by
    rw [inv_two_pow_pow, ← mul_assoc, ← pow_mul, ← pow_succ, two_pow_mul_inv _ _ (by omega)]
    unfold u
    rw [inv_two_pow_pow]
    exact inv_two_pow_le _ _ (by omega)
  have hn : 8 * p.n - 20 = (4 * p.n - 10) * 2 := by cases S <;> decide
  have hs : (2 : ℝ≥0∞)^20 * ((2 : ℝ≥0∞)^(8 * p.n))⁻¹ =
      (((2 : ℝ≥0∞)^(4 * p.n - 10))⁻¹)^2 := by
    rw [two_pow_mul_inv _ _ (by cases S <;> decide), inv_two_pow_pow, hn]
  change itsrBound p q (2^20) ≤ _
  unfold itsrBound
  simp only [Nat.cast_pow, Nat.cast_ofNat, hs, sq_rpow_half]
  calc _ ≤ (u + u)^2 := by
          apply pow_le_pow_left₀ zero_le _ 2
          apply add_le_add
          · apply (ENNReal.rpow_le_rpow _ (by norm_num : 0 ≤ (2⁻¹ : ℝ))).trans
              (le_of_eq (sq_rpow_half u))
            exact (mul_le_mul' (pow_le_pow_left₀ zero_le h1 2) hc).trans hA
          · apply (mul_le_mul' h2 le_rfl).trans
            rw [two_pow_mul_inv _ _ (by cases S <;> decide)]
       _ = _ := by
          rw [← two_mul]
          have h : (2 : ℝ≥0∞) * (2^e)⁻¹ = (2^(e-1))⁻¹ := by
            simpa using two_pow_mul_inv 1 e (by cases S <;> decide)
          unfold u
          rw [h, inv_two_pow_pow]
          congr 2
          cases S <;> decide

/-- The numeric bound applies to the exact game on encoded digests at every set. -/
theorem itsr_digest_num (S : Sha2Set)
    {Xm : Type} [Fintype Xm] [DecidableEq Xm]
    {L : LocalSig.{1, 0}} {A : QReg} (I : L.Interp) (ρ : SubState A)
    (x : IAdv L (qromSpec (S.Node × Xm) (Bytes S.vp.params.m)) Xm S.Node
      (fun _ ↦ S.Node × Xm) (2^20) A)
    (hx : IAdv.IsQueryBound (2^20) x (fun _ ↦ 2^40 + (componentCounts S.vp (2^20)).itsr)) :
    itsrAdaptiveExp I ρ (2^20) x (QItsr.SetDigest.idxCov S.vp) ≤
      ((2 : ℝ≥0∞)^(8 * S.vp.params.n - 2 * itsrQueryBits S - 22))⁻¹ :=
  (itsr_digest_game_le S I ρ _ _ x hx).trans (itsrBound_sets_num S)

theorem itsrBound_192f_num :
    itsrBound Sha2Set.s192f.vp.params
      (2^40 + (componentCounts Sha2Set.s192f.vp (2^20)).itsr) (2^20) ≤ ((2 : ℝ≥0∞)^86)⁻¹ :=
  (itsrBound_sets_num .s192f).trans (Num.inv_two_pow_le _ _ (by decide +kernel))

/-- Exact-game success probability at the 192f resource point. -/
theorem itsr_game_192f_num
    {Xm Ix Lx : Type} [Fintype Xm] [DecidableEq Xm] [Fintype Ix] [DecidableEq Ix]
    [AddCommGroup Ix] [Fintype Lx] [DecidableEq Lx] [AddCommGroup Lx]
    {L : LocalSig.{1, 0}} {A : QReg} (I : L.Interp) (ρ : SubState A)
    (x : IAdv L (qromSpec (Sha2Set.s192f.Node × Xm) (Ix × (Fin 33 → Lx))) Xm
      Sha2Set.s192f.Node (fun _ ↦ Sha2Set.s192f.Node × Xm) (2^20) A)
    (hx : IAdv.IsQueryBound (2^20) x
      (fun _ ↦ 2^40 + (componentCounts Sha2Set.s192f.vp (2^20)).itsr))
    (hi : Fintype.card Ix = 2^66) (hl : Fintype.card Lx = 2^8) :
    itsrAdaptiveExp I ρ (2^20) x (forsCov (I := Ix) (L := Lx) (k := 33)) ≤
      ((2 : ℝ≥0∞)^86)⁻¹ :=
  (itsr_game_le .s192f I ρ _ _ x hx hi hl).trans itsrBound_192f_num

end Reduction

#print axioms Reduction.itsr_digest_game_le
#print axioms Reduction.itsr_game_le
#print axioms Reduction.itsrBound_192f_num

#print axioms Reduction.itsr_game_192f_num
#print axioms Reduction.itsrBound_sets_num
#print axioms Reduction.itsr_digest_num
