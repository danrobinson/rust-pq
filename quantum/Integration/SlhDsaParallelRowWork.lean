import Integration.SlhDsaParallelRowSearch
import PQ.QROM.MultiPhase2

/-! Variable-width parallel queries to one table. The selected port is a mask
of active lanes and can depend on preceding measurement outcomes. A port
call accesses the shared table once in every active lane and acts as the
identity on all inactive response registers. -/

namespace Reduction.ParallelRowSearch

open Quantum PQ.QROM Finset ENNReal
open scoped Kronecker ComplexOrder
universe u v w
set_option maxHeartbeats 1200000

variable {K X Y : Type} [Fintype K] [DecidableEq K]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
    {L : LocalSig.{u,v}} {W : QReg → Type w} {A : QReg} {cap : ℕ}

/-- A port for each mask on a finite pool of lanes. -/
abbrev maskSpec (cap : ℕ) (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :=
  qromNSpec (Finset (Fin cap)) (Fin cap → X) (Fin cap → Y)

def maskedTable (H : X → Y) (mask : Finset (Fin cap)) (x : Fin cap → X) : Fin cap → Y :=
  fun j => if j ∈ mask then H (x j) else 0

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- On a computational basis state, an inactive lane is left alone and an
active lane executes the ordinary additive oracle query. -/
theorem masked_lane (H : X → Y) (mask : Finset (Fin cap)) (x : Fin cap → X)
    (y : Fin cap → Y) (j : Fin cap) :
    ((oracleEquiv (maskedTable H mask) (x,y)).1 j, (oracleEquiv (maskedTable H mask) (x,y)).2 j) =
      if j ∈ mask then oracleEquiv H (x j,y j) else (x j,y j) := by
  by_cases h : j ∈ mask <;> simp [maskedTable, h]

private theorem mean_mask_mass (I : L.Interp) (G : X → Y) (row : X → K)
    (H : K → X → Y) (outside : ∀ k x, row x ≠ k → H k x = G x)
    (x : QuantumComp L (maskSpec cap X Y) W A) (ρ : SubState A) (work : ℕ)
    (budget : IsWeightedBound x Finset.card work) :
    (avg fun k => diffMass I (maskedTable (H k)) (maskedTable G) x (joint ρ)) ≤
      (Fintype.card K : ℝ≥0∞)⁻¹ * work := by
  classical
  let mass := massN I (maskedTable G) x (joint ρ)
  unfold diffMass
  rw [avg_tsum]
  have lim := (tsum_weighted_massN_le I (maskedTable G) (joint_posSemidef ρ) _ budget).trans
    ((mul_le_mul' le_rfl (ofReal_trace_joint_le_one ρ)).trans_eq (mul_one _))
  apply le_trans _ (mul_le_mul' (le_refl (Fintype.card K : ℝ≥0∞)⁻¹) lim)
  rw [← ENNReal.tsum_mul_left]
  apply tsum_le_tsum
  intro c
  let touched := c.1.image (fun j => row (c.2 j))
  have unchanged (k : K) (hk : k ∉ touched) : maskedTable (H k) c.1 c.2 = maskedTable G c.1 c.2 := by
    funext j
    by_cases on : j ∈ c.1
    · have ne : row (c.2 j) ≠ k := fun eq => hk (Finset.mem_image.mpr ⟨j,on,eq⟩)
      simp [maskedTable,on,outside k _ ne]
    · simp [maskedTable,on]
  calc
    _ ≤ avg (fun k => if k ∈ touched then mass c else 0) := by
      apply avg_mono
      intro k
      by_cases hk : k ∈ touched
      · simp only [hk, ite_true]
        split_ifs <;> simp [mass]
      · simp [hk, unchanged k hk]
    _ = (Fintype.card K : ℝ≥0∞)⁻¹ * ((touched.card:ℝ≥0∞) * mass c) := by
      simp [avg, nsmul_eq_mul, mul_left_comm]
    _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' (Nat.cast_le.mpr Finset.card_image_le) le_rfl)

/-- Adaptive masked batches with at most `depth` calls and `work` total active
lanes on every execution path. The winning predicate may depend on the hidden
row. Both probabilities average over a uniform choice of that row. -/
theorem work_depth_sqrt (I : L.Interp) (G : X → Y) (row : X → K)
    (H : K → X → Y) (outside : ∀ k x, row x ≠ k → H k x = G x)
    (x : QuantumComp L (maskSpec cap X Y) W A) (ρ : SubState A)
    (depth work : ℕ) (rounds : IsTotalBound x depth)
    (budget : IsWeightedBound x Finset.card work) (win : K → (Σ a, W a) → Prop) :
    let success := fun k h => leafProb (nRuntime (maskedTable h)) I x (joint ρ) (win k)
    (avg fun k => success k (H k)) ^ (2⁻¹ : ℝ) ≤
      (avg fun k => success k G) ^ (2⁻¹ : ℝ) +
        (4*(depth:ℝ≥0∞)*((Fintype.card K : ℝ≥0∞)⁻¹*work)) ^ (2⁻¹ : ℝ) := by
  dsimp only
  refine (sqrt_avg_le _ _ _ fun k =>
    (nRuntime_sqrt_le I (maskedTable (H k)) (maskedTable G)
      (joint_posSemidef ρ) rounds (win k)).1).trans (add_le_add le_rfl (sqrt_le_sqrt ?_))
  rw [avg_mul_left]
  exact mul_le_mul' le_rfl (mean_mask_mass I G row H outside x ρ work budget)

/-- Probability of correctly identifying a uniform hidden row. The charge
`work` is the sum of the active widths along each path, and the port masks
may be chosen adaptively between rounds. -/
theorem recover_row (I : L.Interp) (G : X → Y) (row : X → K)
    (H : K → X → Y) (outside : ∀ k x, row x ≠ k → H k x = G x)
    (x : QuantumComp L (maskSpec cap X Y) W A) (ρ : SubState A)
    (depth work : ℕ) (rounds : IsTotalBound x depth)
    (budget : IsWeightedBound x Finset.card work) (guess : (Σ a, W a) → K) :
    (avg fun k => leafProb (nRuntime (maskedTable (H k))) I x (joint ρ) (fun p => guess p = k)) ≤
      (1 + (4*(depth:ℝ≥0∞)*work)^(2⁻¹:ℝ))^2 / Fintype.card K := by
  let u := (Fintype.card K : ℝ≥0∞)⁻¹
  let b := 4*(depth:ℝ≥0∞)*work
  have base : (avg fun k => leafProb (nRuntime (maskedTable G)) I x (joint ρ)
      (fun p => guess p = k)) ≤ u := by
    unfold avg
    rw [← Finset.mul_sum]
    have h := (sum_leafProb_eq_le (R := nRuntime (maskedTable G)) (I := I) x
      (joint_posSemidef ρ) guess).trans (ofReal_trace_joint_le_one ρ)
    exact (mul_le_mul' (le_refl u) h).trans_eq (mul_one u)
  have h := work_depth_sqrt I G row H outside x ρ depth work rounds budget (fun k p => guess p = k)
  have fac : 4*(depth:ℝ≥0∞)*(u*work) = u*b := by dsimp only [b]; ring
  change _ ≤ _ + (4*(depth:ℝ≥0∞)*(u*work))^(2⁻¹:ℝ) at h
  rw [fac, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h
  have h' := h.trans (add_le_add (sqrt_le_sqrt base) le_rfl)
  rw [show u^(2⁻¹:ℝ) + u^(2⁻¹:ℝ)*b^(2⁻¹:ℝ) =
      u^(2⁻¹:ℝ)*(1+b^(2⁻¹:ℝ)) by ring] at h'
  have fin := pow_le_pow_left' h' 2
  simpa only [mul_pow, sq_sqrt, u, b, div_eq_mul_inv, mul_comm] using fin

end Reduction.ParallelRowSearch

#print axioms Reduction.ParallelRowSearch.masked_lane
#print axioms Reduction.ParallelRowSearch.work_depth_sqrt
#print axioms Reduction.ParallelRowSearch.recover_row
