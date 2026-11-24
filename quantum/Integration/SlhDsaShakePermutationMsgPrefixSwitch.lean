import Integration.SlhDsaShakePermutationMsgPortStep

namespace Reduction.ShakePermutation.MsgEffect
open Classical Quantum OracleComp OracleSpec PQ.Interactive PQ.QROM Matrix
open scoped ComplexOrder
noncomputable section
variable {X Y E I A : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] [Fintype I]
local notation "Work" => WS X Y E

def fee (r a : ℝ) := cost r a + r^2

variable (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (total : ∑ i, w i ≤ 1) (g : I → X → Y) (G : X → Y)
    (rows : I → Finset X) (support : ∀ i x, g i x ≠ G x → x ∈ rows i)
    (r a : ℝ) (hr : 0 ≤ r) (ha : 0 < a) (risk : ∀ x, ∑ i with x ∈ rows i, w i ≤ r^2)

include hw total support hr ha risk in
/-- Switch the public oracle used by a measured quantum prefix. The
continuation may depend on the private index, on the measured outcome,
and on every unmeasured workspace qubit. Its operations are unrestricted. -/
theorem switch {p : (X → Y) → Closed Work A} {q : ℕ}
    (bound : PUE (spec:=unifSpec) cnt0 p q) (k : I → A → Closed Work Bool)
    (M : Matrix Work Work ℂ) (psd : M.PosSemidef) :
    ∑ i, w i * mass (p (g i) >>= k i) M ≤
      ∑ i, w i * mass (p G >>= k i) M + (q:ℝ)*fee r a*M.trace.re := by
  have fee_nonneg : 0 ≤ fee r a := by unfold fee cost; positivity
  induction bound generalizing M with
  | pure z q =>
    simp only [pure_bind]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) fee_nonneg) psd.trace_re_nonneg)
  | instr j p q h ih =>
    let u := framedIdx (X:=X) (Y:=Y) (E:=E) j
    have tr : ∑ n, (u.2.1.branch n M).trace.re = M.trace.re := by
      rw [← Complex.re_sum,u.2.2.sum_trace_eq (s:=Finset.univ) (by simp)]
    simp only [bind_assoc,mass_instr _ _ psd,Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => lhs; rw [Finset.sum_comm]
    rw [← tr,Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => ih j _ ((u.2.1.isCP_branch j).posSemidef psd)
  | port p q h ih =>
    let after (i : I) := p (g i) >>= k i
    let v (H : X → Y) (z : Closed Work Bool) :=
      liftM ((instrSpec Work + unifSpec).query (.inl (portIdx H))) >>= fun _ => z
    have value (H) (z : Closed Work Bool) : mass (v H z) M = mass z (applyPort H M) := by
      unfold v
      rw [mass_instr _ _ psd]
      change (∑ _i : Fin 1, _) = _
      rw [Fin.sum_univ_one]; rfl
    simp only [bind_assoc]
    change ∑ i, w i * mass (v (g i) (after i)) M ≤ ∑ i, w i * mass (v G (p G >>= k i)) M + _
    simp only [value]
    have query := port_step w hw total g G rows support r a hr ha risk after M psd
    have next := ih (applyPort G M) (port_positive G psd)
    rw [port_trace] at next
    dsimp only [after] at query
    have fee_more := mul_le_mul_of_nonneg_right
      (show cost r a ≤ fee r a by unfold fee; linarith [sq_nonneg r]) psd.trace_re_nonneg
    push_cast
    linarith
  | query n p q h ih =>
    simp only [bind_assoc,mass_coin _ _ psd,cnt0,Nat.add_zero]
    let c := ((n:ℝ)+1)⁻¹
    have comm (v : I → Fin (n+1) → ℝ) : ∑ i, w i*(c*∑ j, v i j) = c*∑ j, ∑ i, w i*v i j := by
      simp_rw [mul_left_comm (w _) c,Finset.mul_sum]
      exact Finset.sum_comm
    change ∑ i, w i*(c*∑ j, _) ≤ ∑ i, w i*(c*∑ j, _) + _
    rw [comm,comm]
    have avg := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) fun j _ => ih j M psd) (show 0 ≤ c by unfold c; positivity)
    have units : c*(n+1:ℝ) = 1 := by unfold c; exact inv_mul_cancel₀ (by positivity)
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_add,Nat.cast_one,mul_add,← mul_assoc,units,one_mul] at avg
    exact avg
  | eval x p q h ih =>
    let left (i : I) := mass (p (g i x) (g i) >>= k i) M
    let mid (i : I) := mass (p (G x) (g i) >>= k i) M
    have one (i) : w i * left i ≤ w i * mid i + if x ∈ rows i then w i*M.trace.re else 0 := by
      by_cases mem : x ∈ rows i
      · rw [ite_eq_left mem]
        have nonneg : 0 ≤ w i * mid i := mul_nonneg (hw i) ENNReal.toReal_nonneg
        exact (mul_le_mul_of_nonneg_left (mass_le _ psd) (hw i)).trans (le_add_of_nonneg_left nonneg)
      · rw [ite_eq_right mem,add_zero]
        have eq : g i x = G x := by by_contra h; exact mem (support i x h)
        simp only [left,mid,eq,le_rfl]
    have term := Finset.sum_le_sum (s:=Finset.univ) fun i _ => one i
    rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.sum_mul] at term
    have rest := ih (G x) M psd
    have lim := mul_le_mul_of_nonneg_right (risk x) psd.trace_re_nonneg
    have f : r^2 ≤ fee r a := le_add_of_nonneg_left (by unfold cost; positivity)
    have extra := mul_le_mul_of_nonneg_right f psd.trace_re_nonneg
    change ∑ i, w i * left i ≤ _
    dsimp only [mid] at term
    push_cast
    linarith

end
end Reduction.ShakePermutation.MsgEffect
#print axioms Reduction.ShakePermutation.MsgEffect.switch
