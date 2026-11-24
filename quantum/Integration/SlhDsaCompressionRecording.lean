import PQ.QROM.PurifyTight
import MIdeal.MsgPrf512

/-! Local recording-oracle estimate for a compression cell with a finite output alphabet.
A cell register has an extra empty basis state. A vector-valued amplitude at each
basis value includes all response and workspace registers. -/
namespace Reduction.Compression.Recording

variable {Y V : Type} [Fintype Y] [Nonempty Y] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def coeff (Y : Type) [Fintype Y] : ℝ := (Real.sqrt (Fintype.card Y))⁻¹

private lemma coeff_sq : coeff Y ^ 2 * Fintype.card Y = 1 := by
  have h : (0:ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  rw [coeff, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

def energy (ψ : Option Y → V) : ℝ := ‖ψ none‖^2 + ∑ y : Y, ‖ψ (some y)‖^2

noncomputable def mean (ψ : Option Y → V) : V := coeff Y • ∑ y, ψ (some y)

noncomputable def swap (ψ : Option Y → V) : Option Y → V
  | none => mean ψ
  | some y => ψ (some y) + coeff Y • (ψ none - mean ψ)

private lemma mean_swap (ψ : Option Y → V) : mean (swap ψ) = ψ none := by
  have hc := coeff_sq (Y := Y)
  change coeff Y • (∑ y : Y, (ψ (some y) + coeff Y • (ψ none - mean ψ))) = ψ none
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_add, smul_smul, smul_smul]
  rw [show coeff Y * (Fintype.card Y : ℝ) * coeff Y = 1 by nlinarith [hc]]
  change mean ψ + (1:ℝ) • (ψ none - mean ψ) = _
  simp

theorem swap_involutive (ψ : Option Y → V) : swap (swap ψ) = ψ := by
  funext t
  cases t with
  | none => exact mean_swap ψ
  | some y =>
    change ψ (some y) + coeff Y • (ψ none - mean ψ) +
      coeff Y • (mean ψ - mean (swap ψ)) = ψ (some y)
    rw [mean_swap, add_assoc, ← smul_add]
    simp

private lemma coeff_nonneg : 0 ≤ coeff Y := by unfold coeff; positivity

theorem swap_energy (ψ : Option Y → V) : energy (swap ψ) = energy ψ := by
  let a := coeff Y
  let d := ψ none - mean ψ
  have hs : (∑ y : Y, 2 * inner ℝ (ψ (some y)) (a • d)) = 2 * inner ℝ (mean ψ) d := by
    simp only [real_inner_smul_right, ← Finset.mul_sum, ← sum_inner, mean, real_inner_smul_left]
    ring
  have hsq : (Fintype.card Y : ℝ) * ‖a • d‖^2 = ‖d‖^2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (coeff_nonneg (Y := Y))]
    have hc := coeff_sq (Y := Y)
    rw [← mul_assoc, mul_comm (Fintype.card Y : ℝ), hc, one_mul]
  change ‖mean ψ‖^2 + ∑ y : Y, ‖ψ (some y) + a • d‖^2 = _
  simp only [norm_add_sq_real, Finset.sum_add_distrib, hs, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hsq, energy]
  dsimp only [d]
  rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real, real_inner_comm (mean ψ)]
  ring

private theorem mean_sq_le (ψ : Option Y → V) : ‖mean ψ‖^2 ≤ ∑ y : Y, ‖ψ (some y)‖^2 := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Y) (fun _ => (1:ℝ))
    (fun y => ‖ψ (some y)‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at cs
  have hn := norm_sum_le (Finset.univ : Finset Y) (fun y => ψ (some y))
  have h := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr hn |>.trans cs)
    (sq_nonneg (coeff Y))
  rw [← mul_assoc, coeff_sq, one_mul] at h
  simpa only [mean, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (coeff_nonneg (Y := Y))] using h

/-- Decompress, query with a response/workspace isometry controlled by the
undecompressed option value, and compress again. The empty branch may use the identity. -/
noncomputable def query (O : Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Option Y → V) :
    Option Y → V := swap (fun t => O t (swap ψ t))

theorem query_energy (O : Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Option Y → V) :
    energy (query O ψ) = energy ψ := by
  unfold query
  rw [swap_energy, ← swap_energy ψ]
  simp [energy]

private theorem diff_le (ψ : Option Y → V) :
    ‖ψ none - mean ψ‖ ≤ 2 * Real.sqrt (energy ψ) := by
  have hs : 0 ≤ ∑ y : Y, ‖ψ (some y)‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have he : 0 ≤ energy ψ := add_nonneg (sq_nonneg _) hs
  have h₁ : ‖ψ none‖ ≤ Real.sqrt (energy ψ) := (Real.le_sqrt (norm_nonneg _) he).mpr
    (le_add_of_nonneg_right hs)
  have h₂ : ‖mean ψ‖ ≤ Real.sqrt (energy ψ) := (Real.le_sqrt (norm_nonneg _) he).mpr
    ((mean_sq_le ψ).trans (le_add_of_nonneg_left (sq_nonneg _)))
  exact (norm_sub_le _ _).trans (by linarith)

/-- A single recording query starting with no amplitude on the marked outputs.
The marked set can be the union of all prefix fibres already recorded elsewhere. -/
theorem query_marked_energy (O : Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Option Y → V)
    (B : Finset Y) (clean : ∀ y ∈ B, ψ (some y) = 0) :
    (∑ y ∈ B, ‖query O ψ (some y)‖^2) ≤
      16 * ((B.card : ℝ) / Fintype.card Y) * energy ψ := by
  let φ := fun t => O t (swap ψ t)
  have same : energy φ = energy ψ := by
    calc energy φ = energy (swap ψ) := by simp [energy, φ]
         _ = energy ψ := swap_energy ψ
  have he : 0 ≤ energy ψ := add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have one (y : Y) (hy : y ∈ B) :
      ‖query O ψ (some y)‖ ≤ 4 * coeff Y * Real.sqrt (energy ψ) := by
    change ‖O (some y) (ψ (some y) + coeff Y • (ψ none - mean ψ)) +
      coeff Y • (φ none - mean φ)‖ ≤ _
    rw [clean y hy,zero_add]
    apply (norm_add_le _ _).trans
    simp only [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (coeff_nonneg (Y := Y))]
    have a := mul_le_mul_of_nonneg_left (diff_le ψ) (coeff_nonneg (Y := Y))
    have b := mul_le_mul_of_nonneg_left (diff_le φ) (coeff_nonneg (Y := Y))
    rw [same] at b
    linarith
  calc _ ≤ ∑ _y ∈ B, (4 * coeff Y * Real.sqrt (energy ψ))^2 := by
         apply Finset.sum_le_sum
         intro y hy
         exact (sq_le_sq₀ (norm_nonneg _) (by positivity [coeff_nonneg (Y := Y)])).mpr (one y hy)
       _ = _ := by
         simp only [Finset.sum_const, nsmul_eq_mul, mul_pow, Real.sq_sqrt he, coeff, inv_pow,
           Real.sq_sqrt (Nat.cast_nonneg _)]
         ring

section Sha512
set_option maxRecDepth 6000
open MLink Ideal MIdeal.Sha512

def prefixCells (S : Sha2Set) (B : Finset S.Node) : Finset Chain512 :=
  Finset.univ.filter (fun y => trunc S y ∈ B)

theorem mem_prefixCells (S : Sha2Set) (B : Finset S.Node) (y : Chain512) :
    y ∈ prefixCells S B ↔ trunc S y ∈ B := by
  simp only [prefixCells, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Each recorded n-byte prefix marks exactly a 2^(-8n) fraction of the full
512-bit output alphabet. The query still returns all 512 bits. -/
theorem prefixCells_fraction (S : Sha2Set) (B : Finset S.Node) :
    ((prefixCells S B).card : ℝ) / Fintype.card Chain512 =
      (B.card : ℝ) / 2^(8*S.vp.params.n) := by
  classical
  have h := trunc_uniform S (fun y => y ∈ B)
  simp only [SampleableType.prEvent_uniformSample] at h
  have e := congrArg ENNReal.toReal h
  have node : (Fintype.card S.Node : ℝ) = 2^(8*S.vp.params.n) := by
    rw [card_bytes, Nat.cast_pow, pow_mul]
    norm_num
  rw [← node]
  simpa only [prefixCells, ENNReal.toReal_div, ENNReal.toReal_natCast,
    Finset.filter_mem_eq_inter, Finset.univ_inter] using e

/-- Fibres split by the queried address and the unchanged part of the database
are orthogonal. If every fibre starts collision-free and the other cells supply
at most t marked prefixes, sum their actual transition energies. -/
theorem query_prefix_energy (S : Sha2Set) {I : Type} [Fintype I] (t : ℕ)
    (O : I → Option Chain512 → V ≃ₗᵢ[ℝ] V) (ψ : I → Option Chain512 → V)
    (B : I → Finset S.Node) (count : ∀ i, (B i).card ≤ t)
    (clean : ∀ i (y : Chain512), y ∈ prefixCells S (B i) → ψ i (some y) = 0) :
    (∑ i, ∑ y ∈ prefixCells S (B i), ‖query (O i) (ψ i) (some y)‖^2) ≤
      16 * ((t : ℝ) / 2^(8*S.vp.params.n)) * ∑ i, energy (ψ i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := query_marked_energy (Y := Chain512) (V := V) (O i) (ψ i) (prefixCells S (B i)) (clean i)
  rw [prefixCells_fraction] at h
  apply h.trans
  have hn : 0 ≤ energy (ψ i) :=
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  gcongr
  exact_mod_cast count i

end Sha512

end Reduction.Compression.Recording
#print axioms Reduction.Compression.Recording.swap_energy
#print axioms Reduction.Compression.Recording.query_marked_energy
#print axioms Reduction.Compression.Recording.query_prefix_energy
