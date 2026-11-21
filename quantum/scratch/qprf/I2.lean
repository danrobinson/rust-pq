import PQ.QROM.ExactItsr4

open ENNReal Finset

namespace PQ.QROM

set_option linter.unusedSectionVars false

variable {ι D D' : Type} [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D] [Fintype D']
  [DecidableEq D']

theorem card_fun_fiber (π : D → D') (N : ℕ) (hfib : ∀ z, (univ.filter fun d ↦ π d = z).card = N)
    (b : ι → D') : (univ.filter fun a : ι → D ↦ π ∘ a = b).card = N ^ Fintype.card ι := by
  classical
  have e : {a : ι → D // π ∘ a = b} ≃ ((i : ι) → {u : D // π u = b i}) :=
    (Equiv.subtypeEquivRight (q := fun a : ι → D ↦ ∀ i, π (a i) = b i) fun a ↦ funext_iff).trans
      (Equiv.subtypePiEquivPi (p := fun i u ↦ π u = b i))
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_pi]
  simp only [Fintype.card_subtype, hfib, prod_const, card_univ]

theorem sum_comp_fiber (π : D → D') (N : ℕ) (hN : 0 < N)
    (hfib : ∀ z, (univ.filter fun d ↦ π d = z).card = N) (g : (ι → D') → ℝ≥0∞) :
    ∑ a : ι → D, g (π ∘ a) = ∑ b : ι → D', (N ^ Fintype.card ι : ℕ) * g b := by
  classical
  rw [Finset.sum_comp (s := univ) (g := fun a : ι → D ↦ π ∘ a)]
  have himg : (univ.image fun a : ι → D ↦ π ∘ a) = univ := by
    refine eq_univ_of_forall fun b ↦ ?_
    have h := card_fun_fiber π N hfib b
    have hpos : 0 < (univ.filter fun a : ι → D ↦ π ∘ a = b).card := by
      rw [h]; exact pow_pos hN _
    obtain ⟨a, ha⟩ := card_pos.1 hpos
    exact mem_image.2 ⟨a, mem_univ _, (mem_filter.1 ha).2⟩
  rw [himg]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [card_fun_fiber π N hfib b, nsmul_eq_mul]

theorem avg_comp_fiber (π : D → D') (N : ℕ) (hN : 0 < N)
    (hfib : ∀ z, (univ.filter fun d ↦ π d = z).card = N) (g : (ι → D') → ℝ≥0∞) :
    ∑ a : ι → D, (Fintype.card (ι → D) : ℝ≥0∞)⁻¹ * g (π ∘ a) =
      ∑ b : ι → D', (Fintype.card (ι → D') : ℝ≥0∞)⁻¹ * g b := by
  have hc : (Fintype.card (ι → D) : ℝ≥0∞) =
      (N ^ Fintype.card ι : ℕ) * (Fintype.card (ι → D') : ℝ≥0∞) := by
    have h := sum_comp_fiber (ι := ι) π N hN hfib (fun _ ↦ 1)
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h
    rw [h, mul_comm]
  rw [← mul_sum, ← mul_sum, sum_comp_fiber π N hN hfib, ← mul_sum, hc,
    ENNReal.mul_inv (Or.inr (natCast_ne_top _)) (Or.inl (natCast_ne_top _))]
  have hN' : ((N ^ Fintype.card ι : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (pow_pos hN _).ne'
  calc ((N ^ Fintype.card ι : ℕ) : ℝ≥0∞)⁻¹ * (Fintype.card (ι → D') : ℝ≥0∞)⁻¹ *
        (((N ^ Fintype.card ι : ℕ) : ℝ≥0∞) * ∑ b, g b)
      = (((N ^ Fintype.card ι : ℕ) : ℝ≥0∞)⁻¹ * ((N ^ Fintype.card ι : ℕ) : ℝ≥0∞)) *
          ((Fintype.card (ι → D') : ℝ≥0∞)⁻¹ * ∑ b, g b) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hN' (natCast_ne_top _), one_mul]

variable [Nonempty D']

theorem coverProb_le_of_fiber (π : D → D') (N : ℕ) (hN : 0 < N)
    (hfib : ∀ z, (univ.filter fun d ↦ π d = z).card = N)
    (Cov : Finset D → D → Prop) [∀ S, DecidablePred (Cov S)]
    (Cov' : Finset D' → D' → Prop) [∀ S, DecidablePred (Cov' S)]
    (hcov : ∀ S u, Cov S u → Cov' (S.image π) (π u)) :
    coverProb ι Cov ≤ coverProb ι Cov' := by
  classical
  have hD : (Fintype.card D : ℝ≥0∞) = N * Fintype.card D' := by
    have h := Fintype.card_congr (Equiv.sigmaFiberEquiv π).symm
    rw [Fintype.card_sigma] at h
    simp only [Fintype.card_subtype, hfib, sum_const, card_univ, smul_eq_mul] at h
    rw [h]; push_cast; ring
  have hpt : ∀ d : ι → D, ((covered Cov (univ.image d)).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹ ≤
      ((covered Cov' (univ.image (π ∘ d))).card : ℝ≥0∞) * (Fintype.card D' : ℝ≥0∞)⁻¹ := by
    intro d
    have hsub : covered Cov (univ.image d) ⊆
        univ.filter fun u ↦ π u ∈ covered Cov' (univ.image (π ∘ d)) := by
      intro u hu
      simp only [covered, mem_filter, mem_univ, true_and] at hu ⊢
      have := hcov _ u hu
      rwa [image_image] at this
    have hcard : (univ.filter fun u ↦ π u ∈ covered Cov' (univ.image (π ∘ d))).card =
        N * (covered Cov' (univ.image (π ∘ d))).card := by
      rw [card_eq_sum_card_fiberwise (s := univ.filter fun u ↦ π u ∈ covered Cov' (univ.image (π ∘ d)))
        (f := π) (t := covered Cov' (univ.image (π ∘ d))) (fun u hu ↦ (mem_filter.1 hu).2)]
      have : ∀ z ∈ covered Cov' (univ.image (π ∘ d)),
          ((univ.filter fun u ↦ π u ∈ covered Cov' (univ.image (π ∘ d))).filter
            fun u ↦ π u = z).card = N := by
        intro z hz
        rw [← hfib z]
        congr 1
        ext u
        simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
        rintro rfl; exact hz
      rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_comm]
    calc ((covered Cov (univ.image d)).card : ℝ≥0∞) * (Fintype.card D : ℝ≥0∞)⁻¹
        ≤ (N * (covered Cov' (univ.image (π ∘ d))).card : ℕ) * (Fintype.card D : ℝ≥0∞)⁻¹ := by
          gcongr
          rw [← hcard]; exact_mod_cast card_le_card hsub
      _ = _ := by
          rw [hD]; push_cast
          rw [ENNReal.mul_inv (Or.inr (natCast_ne_top _)) (Or.inl (natCast_ne_top _)),
            mul_comm (N : ℝ≥0∞), mul_assoc, ← mul_assoc (N : ℝ≥0∞),
            ENNReal.mul_inv_cancel (by exact_mod_cast hN.ne') (natCast_ne_top _), one_mul]
  unfold coverProb
  calc _ ≤ ∑ d : ι → D, (Fintype.card (ι → D) : ℝ≥0∞)⁻¹ *
        (((covered Cov' (univ.image (π ∘ d))).card : ℝ≥0∞) * (Fintype.card D' : ℝ≥0∞)⁻¹) :=
        sum_le_sum fun d _ ↦ mul_le_mul' le_rfl (hpt d)
    _ = _ := avg_comp_fiber π N hN hfib
        (fun b ↦ ((covered Cov' (univ.image b)).card : ℝ≥0∞) * (Fintype.card D' : ℝ≥0∞)⁻¹)

end PQ.QROM
