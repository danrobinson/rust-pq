import PQ.QROM.ExactItsr2

/-!
# Adaptive ITSR in the QROM: the randomizer-collision term

## Why the collision term is not dropped

`itsr_adaptive_le` contains `s²/|K|`, the probability that two of the `s` pre-sampled
randomizers coincide (`avg_not_injective_le`).  It was suggested to drop it on the grounds that
repeated randomizers cannot help ("the digests of distinct target points are independent
uniform, hence the covering probability is dominated by `coverProb` for `s` independent
digests").  In the ADAPTIVE game this domination is false for a fixed non-injective tuple of
randomizers, and the term cannot be removed by that argument:

* If `R_j = R_i` for some `i < j`, the row of `R_j` is already visible to the adversary (it was
  issued at request `i`) when the adversary chooses the `j`-th target input `x_j`.  The digest
  `H (R_j, x_j)` is then not a fresh uniform value: the adversary may choose `x_j` among inputs
  whose digests in the row of `R_i` it has already computed.  (It does not know that `R_j` will
  equal `R_i`, but it loses nothing by preparing for it.)
* Example (fixed tuple `Rs ≡ R`, `s = 2`, `Cov S u := u ∈ S`, which is monotone): after the
  first request the adversary searches the row of `R` for a collision `x ≠ x'`,
  `H (R, x) = H (R, x')` (Brassard–Høyer–Tapp, success `Θ(q³/|D|)`), requests `x` and outputs
  `(R, x')`.  It wins with probability `Θ(q³/|D|)`, whereas
  `(2q+1)² · coverProb (Fin 2) Cov ≈ 8 q²/|D|` is smaller for large `q`.
  So `∀ Rs, hybrid(Rs) ≤ (2q+1)² · coverProb` does not hold, and on average over `Rs` the
  winning probability can be of order `Pr[collision] · (gain given a collision)`.

What IS true and proved here: only the EVENT that two randomizers coincide is charged, with its
exact union bound over unordered pairs, `C(s,2)/|K|` instead of `s²/|K|`
(`avg_not_injective_le_choose`).  At `s = 2^64`, `|K| = 2^128` this is `< 1/2` (the birthday
probability of a repeated 128-bit randomizer among `2^64` signatures, which is a real event),
so the bounds below are no longer vacuous there, but they are not small either.  Bounding the
adversary's gain GIVEN a collision (a collision-type search problem inside the visible rows,
not a hidden-set search) would need a quantum collision bound, which the hybrid engine of
`PQ/QROM` does not provide; it is not attempted.

## Results (collision term `C(s,2)/|K|`)

* `itsr_hyb_le_choose`, `itsr_adaptive_choose_le`, `itsr_adaptive_weighted_choose_le`,
  `itsr_adaptive_noloss_choose_le`, `itsr_adaptive_fors_choose_le`,
  `itsr_adaptive_fors_noloss_choose_le`.

## Not proved: the byte-level digest

`security/Reduction/Basic.lean`'s `itsrProblem` uses digests `Bytes m` and the index map
`forsIndices ∘ splitDigest`.  For `forsCov` on pre-split digests `I × (Fin k → L)` to be the
same game, the push-forward of the uniform distribution on `Bytes m` under `splitDigest` must
be uniform on `I × (Fin k → L)`.  At the 128s sizes (`m = 30` bytes: 21 bytes = `k·a = 168`
bits of FORS indices, 7 bytes masked to `h − h/d = 54` bits of tree index, 2 bytes masked to
`h/d = 9` bits of leaf index) the three fields read disjoint bytes and the masks drop whole
bits, so the push-forward is exactly uniform with `|I| = 2^63`, `|L| = 2^12`, `k = 14`; this is
an arithmetic observation about FIPS 205, NOT a machine-checked statement here (it needs
`security/`'s `splitDigest`, which `PQ/` does not import).
-/

open MeasureTheory ENNReal Quantum Matrix Finset
open scoped Kronecker ComplexOrder

universe u v w

namespace PQ.QROM

/-- The probability that a uniform `s`-tuple of randomizers is not injective is at most
`C(s,2) / |K|` (union bound over unordered pairs). -/
theorem avg_not_injective_le_choose {K : Type} [Fintype K] [DecidableEq K] (s : ℕ) :
    avg (fun Rs : Fin s → K ↦ if Function.Injective Rs then (0 : ℝ≥0∞) else 1) ≤
      (s.choose 2 : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) := by
  classical
  let g : (Fin s → K) → Finset (Fin s) → ℝ≥0∞ := fun Rs T ↦
    if ∃ i ∈ T, ∃ j ∈ T, i ≠ j ∧ Rs i = Rs j then 1 else 0
  have hle : ∀ Rs : Fin s → K, (if Function.Injective Rs then (0 : ℝ≥0∞) else 1) ≤
      ∑ T ∈ Finset.powersetCard 2 (univ : Finset (Fin s)), g Rs T := by
    intro Rs
    split_ifs with hinj
    · exact zero_le
    · obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.1 hinj
      have hT : ({i, j} : Finset (Fin s)) ∈ Finset.powersetCard 2 (univ : Finset (Fin s)) :=
        Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, Finset.card_pair hne⟩
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun _ _ ↦ zero_le) hT)
      have : ∃ a ∈ ({i, j} : Finset (Fin s)), ∃ b ∈ ({i, j} : Finset (Fin s)),
          a ≠ b ∧ Rs a = Rs b := ⟨i, by simp, j, by simp, hne, heq⟩
      simp only [g, this, ↓reduceIte]
  have hT : ∀ T ∈ Finset.powersetCard 2 (univ : Finset (Fin s)),
      (avg fun Rs : Fin s → K ↦ g Rs T) ≤ (Fintype.card K : ℝ≥0∞)⁻¹ := by
    intro T hT
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (Finset.mem_powersetCard.1 hT).2
    have hg : ∀ Rs : Fin s → K, g Rs {a, b} ≤ if Rs a = Rs b then (1 : ℝ≥0∞) else 0 := by
      intro Rs
      by_cases h : Rs a = Rs b
      · simp only [h, ↓reduceIte]
        simp only [g]
        split_ifs <;> simp
      · have : ¬ ∃ i ∈ ({a, b} : Finset (Fin s)), ∃ j ∈ ({a, b} : Finset (Fin s)),
            i ≠ j ∧ Rs i = Rs j := by
          rintro ⟨i, hi, j, hj, hij, he⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
          rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
          · exact hij rfl
          · exact h he
          · exact h he.symm
          · exact hij rfl
        simp only [g, this, ↓reduceIte, h, le_refl]
    refine (avg_mono hg).trans ?_
    unfold avg
    rw [← Finset.mul_sum, sum_collide a b hab, mul_left_comm]
    exact (mul_le_mul' le_rfl (by
      rw [mul_comm]; exact natCast_mul_inv_le_one _)).trans (mul_one _).le
  refine (avg_mono hle).trans ?_
  rw [avg_finset_sum]
  refine (Finset.sum_le_sum hT).trans ?_
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, div_eq_mul_inv]

section Game

variable {K Xm D : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm] [DecidableEq Xm]
  [Fintype D] [DecidableEq D] [AddCommGroup D]
  {L : LocalSig.{u, v}} {A : QReg}
  {I : L.Interp} {ρ : SubState A} {s : ℕ}
  {x : IAdv L (qromSpec (K × Xm) D) Xm K (fun _ ↦ K × Xm) s A}
  {Cov : Finset D → D → Prop} [∀ S, DecidablePred (Cov S)] {q Wt : ℕ}

/-- The hybrid experiment, with the collision term `C(s,2)/|K|`. -/
theorem itsr_hyb_le_choose [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    mpHybExp I ρ s x (itsrAWin Cov) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
        (s.choose 2 : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) := by
  classical
  have hB : ∀ Rs : Fin s → K,
      (avg fun Φ : (K × Xm) × Bool → D ↦ avg fun d : Fin s → D ↦
        leafProb (nRuntime (itsrBFn Rs d Φ)) I (mpComp s x Rs) (joint ρ)
          (fun p ↦ itsrAWin Cov Rs (mpFn Rs (owTgt Rs p.2.2 d Φ) s) p)) ≤
        (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov := by
    intro Rs
    rw [avg_comm]
    refine (avg_mono fun d ↦ itsrB_le hmono hx Rs d).trans ?_
    rw [avg_mul_left]
    rfl
  have hRs : ∀ Rs : Fin s → K,
      (avg fun Φ : (K × Xm) × Bool → D ↦
        leafProb (nRuntime fun t : List Xm ↦ mpFn Rs Φ t.length) I (mpComp s x Rs) (joint ρ)
          (itsrAWin Cov Rs (mpFn Rs Φ s))) ≤
        (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
          (if Function.Injective Rs then (0 : ℝ≥0∞) else 1) := by
    intro Rs
    by_cases hinj : Function.Injective Rs
    · rw [itsrA_eq_B hinj]
      simp only [hinj, ↓reduceIte, add_zero]
      exact hB Rs
    · simp only [hinj, ↓reduceIte]
      refine le_trans ?_ le_add_self
      exact avg_le fun Φ ↦
        (leafProb_le _ (joint_posSemidef ρ) _).trans (ofReal_trace_joint_le_one ρ)
  unfold mpHybExp
  refine (avg_mono hRs).trans ?_
  rw [avg_add, avg_const]
  exact add_le_add le_rfl (avg_not_injective_le_choose s)

/-- **Adaptive ITSR, phase-weighted, collision term `C(s,2)/|K|`.** -/
theorem itsr_adaptive_weighted_choose_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) Wt) :
    itsrAdaptiveExp I ρ s x Cov ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
          (s.choose 2 : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ)) ^ 2 :=
  calc itsrAdaptiveExp I ρ s x Cov = (itsrAdaptiveExp I ρ s x Cov ^ (2⁻¹ : ℝ)) ^ 2 :=
        (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' ((mp_reprogram_weighted hx hW).trans
        (add_le_add (sqrt_le_sqrt (itsr_hyb_le_choose hmono hx)) le_rfl)) 2

/-- **Adaptive ITSR, collision term `C(s,2)/|K|`.**
`Pr[win] ≤ (√((2q+1)² · coverProb (Fin s) Cov + C(s,2)/|K|) + 2 q √(s/|K|))²`. -/
theorem itsr_adaptive_choose_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    itsrAdaptiveExp I ρ s x Cov ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
          (s.choose 2 : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 :=
  calc itsrAdaptiveExp I ρ s x Cov = (itsrAdaptiveExp I ρ s x Cov ^ (2⁻¹ : ℝ)) ^ 2 :=
        (sq_sqrt _).symm
    _ ≤ _ := pow_le_pow_left' ((mp_reprogram hx).trans
        (add_le_add (sqrt_le_sqrt (itsr_hyb_le_choose hmono hx)) le_rfl)) 2

/-- **Adaptive ITSR without reprogramming loss, collision term `C(s,2)/|K|`**: all quantum
queries after the `s`-th target request. -/
theorem itsr_adaptive_noloss_choose_le [Nonempty D]
    (hmono : ∀ (S S' : Finset D) (u : D), S ⊆ S' → Cov S u → Cov S' u)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) 0) :
    itsrAdaptiveExp I ρ s x Cov ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 * coverProb (Fin s) Cov +
        (s.choose 2 : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) :=
  (mp_reprogram_zero hx hW).trans (itsr_hyb_le_choose hmono hx)

end Game

section Fors

variable {K Xm Ix Lx : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Xm]
  [DecidableEq Xm] [Fintype Ix] [DecidableEq Ix] [AddCommGroup Ix] [Fintype Lx] [DecidableEq Lx]
  [AddCommGroup Lx] {k : ℕ}
  {L : LocalSig.{u, v}} {A : QReg}

/-- **Adaptive ITSR, FORS relation, collision term `C(s,2)/|K|`.** -/
theorem itsr_adaptive_fors_choose_le (I : L.Interp) (ρ : SubState A) (s : ℕ)
    (x : IAdv L (qromSpec (K × Xm) (Ix × (Fin k → Lx))) Xm K (fun _ ↦ K × Xm) s A) (q : ℕ)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) :
    itsrAdaptiveExp I ρ s x (forsCov (I := Ix) (L := Lx) (k := k)) ≤
      (((2 * (q : ℝ≥0∞) + 1) ^ 2 *
          (∑ γ ∈ range (s + 1),
            (s.choose γ : ℝ≥0∞) * ((Fintype.card Ix : ℝ≥0∞)⁻¹) ^ γ *
              (1 - (Fintype.card Ix : ℝ≥0∞)⁻¹) ^ (s - γ) *
              (1 - (1 - (Fintype.card Lx : ℝ≥0∞)⁻¹) ^ γ) ^ k) +
          (s.choose 2 : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q * ((s : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := itsr_adaptive_choose_le (I := I) (ρ := ρ)
    (Cov := forsCov (I := Ix) (L := Lx) (k := k)) forsCov_mono hx
  rw [coverProb_fors] at h
  simpa only [Fintype.card_fin] using h

/-- **Adaptive ITSR, FORS relation, no reprogramming loss, collision term `C(s,2)/|K|`.** -/
theorem itsr_adaptive_fors_noloss_choose_le (I : L.Interp) (ρ : SubState A) (s : ℕ)
    (x : IAdv L (qromSpec (K × Xm) (Ix × (Fin k → Lx))) Xm K (fun _ ↦ K × Xm) s A) (q : ℕ)
    (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Xm ↦ s - t.length) 0) :
    itsrAdaptiveExp I ρ s x (forsCov (I := Ix) (L := Lx) (k := k)) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
          (∑ γ ∈ range (s + 1),
            (s.choose γ : ℝ≥0∞) * ((Fintype.card Ix : ℝ≥0∞)⁻¹) ^ γ *
              (1 - (Fintype.card Ix : ℝ≥0∞)⁻¹) ^ (s - γ) *
              (1 - (1 - (Fintype.card Lx : ℝ≥0∞)⁻¹) ^ γ) ^ k) +
        (s.choose 2 : ℝ≥0∞) / (Fintype.card K : ℝ≥0∞) := by
  have h := itsr_adaptive_noloss_choose_le (I := I) (ρ := ρ)
    (Cov := forsCov (I := Ix) (L := Lx) (k := k)) forsCov_mono hx hW
  rw [coverProb_fors] at h
  simpa only [Fintype.card_fin] using h

end Fors

end PQ.QROM

#print axioms PQ.QROM.avg_not_injective_le_choose
#print axioms PQ.QROM.itsr_adaptive_choose_le
#print axioms PQ.QROM.itsr_adaptive_weighted_choose_le
#print axioms PQ.QROM.itsr_adaptive_noloss_choose_le
#print axioms PQ.QROM.itsr_adaptive_fors_choose_le
#print axioms PQ.QROM.itsr_adaptive_fors_noloss_choose_le
