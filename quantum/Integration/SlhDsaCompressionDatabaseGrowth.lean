import Integration.SlhDsaCompressionReindex

/-! A recording-query estimate for database predicates whose bad one-cell
extensions occupy at most a known fraction of fresh answers. -/
namespace Reduction.Compression.Recording.Database
open Classical
set_option linter.unusedSectionVars false
variable {X Y V : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Failure persists when the blank queried cell is filled, and from a clean
fibre a random answer creates failure with probability at most `δ`. -/
structure Growth (P : DB X Y → Prop) (q : ℕ) (δ : ℝ) : Prop where
  mono : ∀ x (r : Rest x Y) u, P (assemble x r none) → P (assemble x r u)
  fresh : ∀ x (r : Rest x Y), (occupied r).card ≤ q → ¬P (assemble x r none) →
    ((Finset.univ.filter fun y => P (assemble x r (some y))).card:ℝ)/Fintype.card Y ≤ δ

noncomputable def waveWeight (P : DB X Y → Prop) (ψ : Wave X Y V) : ℝ := by
  classical exact ∑ x, ∑ d, if P d then ‖ψ x d‖^2 else 0

private theorem fibre (P : DB X Y → Prop) (q : ℕ) (δ : ℝ) (hn : 0 ≤ δ) (growth : Growth P q δ)
    (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V) (sp : Sparse q ψ)
    (clean : ∀ x d, P d → ψ x d = 0) (x : X) (r : Rest x Y) :
    (∑ u : Option Y, if P (assemble x r u) then ‖call O ψ x (assemble x r u)‖^2 else 0) ≤
      16 * δ * (∑ u : Option Y, ‖ψ x (assemble x r u)‖^2) := by
  classical
  let φ := fun u => ψ x (assemble x r u)
  let M := Finset.univ.filter fun y => P (assemble x r (some y))
  by_cases live : (occupied r).card ≤ q ∧ ¬P (assemble x r none)
  · have fresh : ∀ y ∈ M, φ (some y) = 0 := fun y hy => clean x _ (Finset.mem_filter.mp hy).2
    have he : 0 ≤ energy φ := add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h := (query_marked_energy (O x) φ M fresh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (growth.fresh x r live.1 live.2) (by norm_num : (0:ℝ) ≤ 16)) he)
    simp only [Fintype.sum_option]
    simp only [live.2,ite_false,zero_add,call_at]
    rw [← Finset.sum_filter]
    exact h
  · have hz : ∀ u, φ u = 0 := fun u => by
      by_cases k : (occupied r).card ≤ q
      · exact clean x _ (growth.mono x r u (by tauto))
      · exact sp x _ (lt_of_lt_of_le (Nat.lt_of_not_ge k) (occupied_rest_le x r u))
    have zero (u) : call O ψ x (assemble x r u) = 0 := by
      rw [call_at]
      change query (O x) φ u = 0
      rw [show φ = fun _ => 0 from funext hz,query_zero]
    simp only [zero,norm_zero,zero_pow (by decide : 2 ≠ 0),ite_self,Finset.sum_const_zero]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem clean_le (P : DB X Y → Prop) (q : ℕ) (δ : ℝ) (hn : 0 ≤ δ) (growth : Growth P q δ)
    (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V) (sp : Sparse q ψ) (clean : ∀ x d, P d → ψ x d = 0) :
    waveWeight P (call O ψ) ≤ 16*δ*mass ψ := by
  classical
  unfold waveWeight mass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [sum_fibres x,sum_fibres x (fun d => ‖ψ x d‖^2),Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ => fibre P q δ hn growth O ψ sp clean x r

private theorem as_product (P : DB X Y → Prop) (ψ : Wave X Y V) :
    sumWeight (fun z : X × DB X Y => P z.2) (fun z => ψ z.1 z.2) = waveWeight P ψ := by
  classical simp only [sumWeight,waveWeight,Fintype.sum_prod_type]

private theorem wave_le (P : DB X Y → Prop) (ψ : Wave X Y V) : waveWeight P ψ ≤ mass ψ := by
  classical
  exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun d _ => by
    split <;> first | exact le_rfl | exact sq_nonneg _

theorem growth_call (P : DB X Y → Prop) (q : ℕ) (δ : ℝ) (hn : 0 ≤ δ) (growth : Growth P q δ)
    (O : X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : Wave X Y V) (sp : Sparse q ψ) :
    Real.sqrt (waveWeight P (call O ψ)) ≤ Real.sqrt (waveWeight P ψ) + 4*Real.sqrt δ*Real.sqrt (mass ψ) := by
  classical
  let f : Wave X Y V := fun x d => if P d then ψ x d else 0
  let g : Wave X Y V := fun x d => if P d then 0 else ψ x d
  have splitψ : ψ = fun x d => f x d + g x d := by funext x d; by_cases h : P d <;> simp [f,g,h]
  have part : call O ψ = fun x d => call O f x d + call O g x d := by
    conv_lhs => rw [splitψ]
    exact funext fun x => funext fun d => call_add O f g x d
  have prior : mass f = waveWeight P ψ := by
    simp only [mass,waveWeight,f,apply_ite (fun x : V => ‖x‖),norm_zero,ite_pow,zero_pow (by decide : 2 ≠ 0)]
  have bounded : mass g ≤ mass ψ := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun d _ => ?_
    by_cases h : P d <;> simp [g,h]
  have z := clean_le P q δ hn growth O g (fun x d h => by simp [g,sp x d h]) (fun x d h => by simp [g,h])
  have loss := Real.sqrt_le_sqrt (z.trans (mul_le_mul_of_nonneg_left bounded (by positivity : 0 ≤ 16*δ)))
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16),
    show Real.sqrt 16 = 4 by rw [show (16:ℝ) = 4^2 by norm_num, Real.sqrt_sq (by norm_num)]] at loss
  have triangle := sw_triangle (fun z : X × DB X Y => P z.2)
    (fun z => call O f z.1 z.2) (fun z => call O g z.1 z.2)
  rw [as_product P (fun x d => call O f x d + call O g x d),as_product,as_product] at triangle
  rw [part]
  exact triangle.trans (add_le_add (Real.sqrt_le_sqrt ((wave_le P _).trans_eq ((call_mass O f).trans prior))) loss)


variable {E W : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
private theorem split_weight (P : DB X Y → Prop) (L : V ≃ₗᵢ[ℝ] Work X E) (v : DB X Y → V) :
    waveWeight P (splitAtWork L v) = sumWeight P v := by
  classical
  unfold waveWeight sumWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : P d <;> simp [h,split_norm]

theorem growth_reindex (P : DB X Y → Prop) (q : ℕ) (δ : ℝ) (hn : 0 ≤ δ) (growth : Growth P q δ)
    (L : V ≃ₗᵢ[ℝ] Work X E) (R : W ≃ₗᵢ[ℝ] Work X E)
    (O : X → Option Y → E ≃ₗᵢ[ℝ] E) (v : DB X Y → V)
    (hv : ∀ d, q < (occupied d).card → v d = 0) :
    Real.sqrt (sumWeight P (reindexCall L R O v)) ≤
      Real.sqrt (sumWeight P v) + 4 * Real.sqrt δ * Real.sqrt (∑ d, ‖v d‖^2) := by
  have sp : Sparse q (splitAtWork L v) := fun x d h => by simp [splitAtWork,hv d h]
  rw [← split_weight P R,reindexCall,split_join,← split_weight P L,← split_mass L]
  exact growth_call P q δ hn growth O _ sp

end Reduction.Compression.Recording.Database
#print axioms Reduction.Compression.Recording.Database.growth_call
