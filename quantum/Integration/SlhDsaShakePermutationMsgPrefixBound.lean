import Integration.SlhDsaShakePermutationMsgPrefixSwitch

namespace Reduction.ShakePermutation.MsgEffect
open Classical Quantum OracleComp OracleSpec PQ.Interactive PQ.QROM ENNReal SetOracle Program
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
variable {I X Y E A : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype E] [DecidableEq E]
local notation "Work" => WS X Y E

theorem uniform_switch (g : I → X → Y) (G : X → Y) (owners : X → Finset I)
    (keep : ∀ i x, i ∉ owners x → g i x = G x) (r a : ℝ) (hr : 0 ≤ r) (ha : 0 < a)
    (risk : ∀ x, ((owners x).card:ℝ)/Fintype.card I ≤ r^2)
    (pre : (X → Y) → Closed Work A) (q : ℕ) (hp : PUE (spec:=unifSpec) cnt0 pre q)
    (post : I → A → Closed Work Bool) (M : Matrix Work Work ℂ) (hM : M.PosSemidef) :
    uniformMean (fun i => qWeight (· = true) (pre (g i) >>= post i) M) ≤
      uniformMean (fun i => qWeight (· = true) (pre G >>= post i) M) +
        ENNReal.ofReal ((q:ℝ)*fee r a*M.trace.re) := by
  classical
  let rows (i : I) := Finset.univ.filter fun x => i ∈ owners x
  let w (_ : I) := ((Fintype.card I : ℝ))⁻¹
  have norm : ∑ i, w i ≤ 1 := by simp [w,Fintype.card_ne_zero]
  have supp (i x) (ne : g i x ≠ G x) : x ∈ rows i := by
    by_contra miss; exact ne (keep i x (by simpa only [rows,Finset.mem_filter,Finset.mem_univ,true_and] using miss))
  have lim (x) : ∑ i with x ∈ rows i, w i ≤ r^2 := by
    have shape : Finset.univ.filter (fun i => x ∈ rows i) = owners x := by ext i; simp [rows]
    simpa only [shape,w,Finset.sum_const,nsmul_eq_mul,← div_eq_mul_inv] using (show ((owners x).card:ℝ)/Fintype.card I ≤ _ from risk x)
  have h := switch w (fun _ => by unfold w; positivity) norm g G rows supp r a hr ha lim hp post M hM
  have mean_finite (p : I → Closed Work Bool) : uniformMean (fun i => qWeight (· = true) (p i) M) ≠ ⊤ := by
    unfold uniformMean
    exact ENNReal.sum_ne_top.mpr fun i _ => mul_ne_top (by simp [unifW]) (finite_weight _ hM)
  have real_mean (p : I → Closed Work Bool) : (uniformMean (fun i => qWeight (· = true) (p i) M)).toReal =
        ∑ i, w i*mass (p i) M := by
    rw [uniformMean,ENNReal.toReal_sum (fun i _ => mul_ne_top (by simp [unifW]) (finite_weight _ hM))]
    simp only [w,mass,unifW,ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  apply (ENNReal.toReal_le_toReal (mean_finite _) (ENNReal.add_ne_top.mpr ⟨mean_finite _,ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add (mean_finite _) ofReal_ne_top,real_mean,real_mean,ENNReal.toReal_ofReal]
  · exact h
  · unfold fee cost; have := hM.trace_re_nonneg; positivity

theorem column_bound (width : ℕ) (π : Permutation) {J : Type} [Fintype J] (u t : (I × J) ↪ Words)
    (positive : 0 < width) (large : 2^(2*width) ≤ Fintype.card I)
    (pre : (Port → Words) → Closed (WS Port Words E) A)
    (hp : PUE (spec:=unifSpec) cnt0 pre (2^41)) (post : I → A → Closed (WS Port Words E) Bool)
    (M : Matrix (WS Port Words E) (WS Port Words E) ℂ) (hM : M.PosSemidef) (one : M.trace.re ≤ 1) :
    uniformMean (fun i => qWeight (· = true)
      (pre (oracle (swapInjections (Program.slice u i) (π,Program.slice t i)).1) >>= post i) M) ≤
      uniformMean (fun i => qWeight (· = true) (pre (oracle π) >>= post i) M) + ENNReal.ofReal (((2^41:ℕ):ℝ)*fee ((2^(width-1))⁻¹) ((2^(width-1))⁻¹)) := by
  let r : ℝ := (2^(width-1))⁻¹
  have ri : ∀ x, ((keyOwners π u t x).card:ℝ)/Fintype.card I ≤ r^2 := by
    intro x
    have d : ((keyOwners π u t x).card:ℝ) ≤ 2 := by exact_mod_cast keyOwners_card π u t x
    have c : (2^(2*width):ℝ) ≤ Fintype.card I := by exact_mod_cast large
    calc
      _ ≤ 2/2^(2*width) := div_le_div₀ (by norm_num) d (by norm_num) c
      _ ≤ _ := by
        obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
        simp only [r,Nat.succ_sub_one,Nat.mul_succ,pow_add,pow_mul]
        field_simp
        ring_nf
        rw [Nat.mul_comm v 2,pow_mul]
        norm_num
  have h := uniform_switch (fun i => oracle (swapInjections (Program.slice u i) (π,Program.slice t i)).1)
    (oracle π) (keyOwners π u t) (outside_column π u t) r r (by unfold r; positivity)
    (by unfold r; positivity) ri pre _ hp post M hM
  refine h.trans (add_le_add le_rfl ?_)
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left one (by unfold fee cost r; positivity)).trans_eq (mul_one _)

/-- At the minimum 128-bit key size, an arbitrary private-key-dependent
continuation costs at most 2⁻¹⁹ for up to 2⁴¹ prefix queries. -/
theorem benchmark_column (π : Permutation) {J : Type} [Fintype J] (u t : (I × J) ↪ Words)
    (large : 2^128 ≤ Fintype.card I)
    (pre : (Port → Words) → Closed (WS Port Words E) A)
    (hp : PUE (spec:=unifSpec) cnt0 pre (2^41)) (post : I → A → Closed (WS Port Words E) Bool)
    (M : Matrix (WS Port Words E) (WS Port Words E) ℂ) (hM : M.PosSemidef) (one : M.trace.re ≤ 1) :
    uniformMean (fun i => qWeight (· = true)
      (pre (oracle (swapInjections (Program.slice u i) (π,Program.slice t i)).1) >>= post i) M) ≤
      uniformMean (fun i => qWeight (· = true) (pre (oracle π) >>= post i) M) + ((2:ℝ≥0∞)^19)⁻¹ := by
  apply (column_bound 64 π u t (by decide) large pre hp post M hM one).trans
  apply add_le_add le_rfl
  rw [← ENNReal.ofReal_ofNat (n := 2),← ENNReal.ofReal_pow (by norm_num),← ENNReal.ofReal_inv_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  norm_num [fee,cost]

end
end Reduction.ShakePermutation.MsgEffect
#print axioms Reduction.ShakePermutation.MsgEffect.benchmark_column
