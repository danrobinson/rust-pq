import Integration.SlhDsaShakePermutationHidden
import Mathlib.Algebra.Order.Chebyshev

namespace Reduction.ShakePermutation.Hidden
open Classical Quantum
set_option maxRecDepth 8192
set_option exponentiation.threshold 1024
variable {E : Type} [Fintype E]
abbrev Vec (E : Type) [Fintype E] := EuclideanSpace ℂ ((Port × Words) × E)

noncomputable def call (π : Permutation) : Vec E ≃ₗᵢ[ℂ] Vec E :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ ((oracleEquiv (oracle π)).prodCongr (Equiv.refl E))

private theorem norm_expand (x : Vec E) :
    ‖x‖^2 = ∑ p : Port, ∑ w : Words × E, ‖x ((p,w.1),w.2)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type,Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)
    (f:=fun y : Words => fun i : E => ‖x ((_,y),i)‖^2)]

theorem call_sum (π : Permutation) (ki ko : Mask) (h : RateMask) (g : Capacity → RateMask)
    (outside : ∀ c z, z ≠ c → g c z = h z) (x : Vec E) :
    ∑ c, ‖call (salted ki ko (g c) π) x - call (salted ki ko h π) x‖^2 ≤ 4*‖x‖^2 := by
  simp only [norm_expand,PiLp.sub_apply]
  exact all_rows π ki ko h g outside (fun p w => x ((p,w.1),w.2))

/-- A fixed sequence of arbitrary coherent inter-query operations, with
ancillas included in E. The incoming vector and operations are independent
of the location of the hidden programmed row. -/
noncomputable def interact (π : Permutation) (op : ℕ → Vec E ≃ₗᵢ[ℂ] Vec E) (x : Vec E) :
    ℕ → Vec E
  | 0 => x
  | t+1 => op t (call π (interact π op x t))

private theorem interact_norm (π : Permutation) (op : ℕ → Vec E ≃ₗᵢ[ℂ] Vec E) (x : Vec E) (t : ℕ) :
    ‖interact π op x t‖ = ‖x‖ := by induction t <;> simp [interact, *]

private theorem telescope (π τ : Permutation) (op : ℕ → Vec E ≃ₗᵢ[ℂ] Vec E) (x : Vec E) (t : ℕ) :
    ‖interact τ op x t - interact π op x t‖ ≤ ∑ j ∈ Finset.range t,
      ‖call τ (interact π op x j) - call π (interact π op x j)‖ := by
  induction t with
  | zero => simp [interact]
  | succ t ih =>
    rw [interact,interact,← map_sub,(op t).norm_map,Finset.sum_range_succ]
    have tri := norm_sub_le_norm_sub_add_norm_sub (call τ (interact τ op x t)) (call τ (interact π op x t)) (call π (interact π op x t))
    rw [← map_sub,(call τ).norm_map] at tri
    exact tri.trans (add_le_add ih le_rfl)

theorem hidden_queries (π : Permutation) (ki ko : Mask) (h : RateMask) (g : Capacity → RateMask)
    (outside : ∀ c z, z ≠ c → g c z = h z)
    (op : ℕ → Vec E ≃ₗᵢ[ℂ] Vec E) (x : Vec E) (q : ℕ) :
    ∑ c, ‖interact (salted ki ko (g c) π) op x q - interact (salted ki ko h π) op x q‖^2 ≤
      4*(q:ℝ)^2*‖x‖^2 := by
  let base := salted ki ko h π
  let err (c : Capacity) (j : ℕ) := ‖call (salted ki ko (g c) π) (interact base op x j) -
    call base (interact base op x j)‖
  calc
    _ ≤ ∑ c, (q:ℝ) * ∑ j ∈ Finset.range q, (err c j)^2 := by
      apply Finset.sum_le_sum
      intro c _
      have b := telescope base (salted ki ko (g c) π) op x q
      apply le_trans (pow_le_pow_left₀ (norm_nonneg _) b 2)
      simpa only [Finset.card_range] using sq_sum_le_card_mul_sum_sq (s:=Finset.range q) (f:=err c)
    _ = (q:ℝ) * ∑ j ∈ Finset.range q, ∑ c, (err c j)^2 := by rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ (q:ℝ) * ∑ _j ∈ Finset.range q, (4*‖x‖^2) := by
      gcongr with j
      simpa only [err,base,interact_norm] using call_sum π ki ko h g outside (interact base op x j)
    _ = _ := by simp; ring

/-- At 2^40 two-way queries, the mean squared state distance caused
by programming one uniformly hidden capacity is at most 2^-430. -/
theorem hidden_benchmark (π : Permutation) (ki ko : Mask) (h : RateMask)
    (g : Capacity → RateMask) (outside : ∀ c z, z ≠ c → g c z = h z)
    (op : ℕ → Vec E ≃ₗᵢ[ℂ] Vec E) (x : Vec E) (unit : ‖x‖ = 1) :
    (∑ c, ‖interact (salted ki ko (g c) π) op x (2^40) -
      interact (salted ki ko h π) op x (2^40)‖^2) / Fintype.card Capacity ≤ (2^430 : ℝ)⁻¹ := by
  have hc : Fintype.card Capacity = 2^512 := by
    change Fintype.card (Fin 8 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  have b := hidden_queries π ki ko h g outside op x (2^40)
  rw [unit] at b
  refine (div_le_div_of_nonneg_right b (Nat.cast_nonneg _)).trans ?_
  rw [hc]
  norm_num

end Reduction.ShakePermutation.Hidden
#print axioms Reduction.ShakePermutation.Hidden.hidden_queries
#print axioms Reduction.ShakePermutation.Hidden.hidden_benchmark
