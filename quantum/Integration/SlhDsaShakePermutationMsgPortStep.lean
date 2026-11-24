import Integration.SlhDsaShakePermutationMsgEffect

namespace Reduction.ShakePermutation.MsgEffect
open Classical Quantum OracleComp OracleSpec PQ.Interactive PQ.QROM PQ.QROM.Purify PQ.QROM.Tight Matrix
open scoped ComplexOrder
noncomputable section
variable {X Y E I : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] [Fintype I]
local notation "Work" => WS X Y E
local notation "Vec" => EuclideanSpace ℂ Work
local notation "K" => fun v : Vec => ketBra v v

def applyPort (H : X → Y) (M : Matrix Work Work ℂ) := (portInstr H).branch 0 M

theorem port_positive (H : X → Y) {M : Matrix Work Work ℂ} (h : M.PosSemidef) :
    (applyPort H M).PosSemidef := ((portInstr H).isCP_branch 0).posSemidef h

theorem port_trace (H : X → Y) (M : Matrix Work Work ℂ) :
    (applyPort H M).trace = M.trace := by
  have h := (lossless_portInstr (E:=E) H).sum_trace_eq (s:=Finset.univ) (by simp) M
  change (∑ i : Fin 1, ((portInstr H).branch i M).trace) = M.trace at h
  simpa only [Fin.sum_univ_one,applyPort] using h

def cost (r a : ℝ) := a+(1+1/a)*(4*r^2)

variable (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (total : ∑ i, w i ≤ 1) (g : I → X → Y) (G : X → Y)
    (rows : I → Finset X) (support : ∀ i x, g i x ≠ G x → x ∈ rows i)
    (r a : ℝ) (hr : 0 ≤ r) (ha : 0 < a) (risk : ∀ x, ∑ i with x ∈ rows i, w i ≤ r^2)

include hw total support hr ha risk in
theorem pure_port (p : I → Closed Work Bool) (v : Vec) :
    ∑ i, w i * mass (p i) (applyPort (g i) (ketBra v v)) ≤
      ∑ i, w i * mass (p i) (applyPort G (ketBra v v)) + cost r a * ‖v‖^2 := by
  let V (H : X → Y) := qvec (idSplit X Y E) H v
  let diff (i : I) := V (g i)-V G
  have move (H) : applyPort H (ketBra v v) = ketBra (V H) (V H) :=
    queryStep_branch_ketBra (idSplit X Y E) H v
  have nd : ∑ i, w i * ‖diff i‖^2 ≤ (2*r*‖v‖)^2 := by
    let Iq := stdOracle X Y ((QReg.of E) × Unit)
    have h := sum_norm_D_sq_le w hw g G rows support r hr risk Iq ((splitIso (idSplit X Y E)) v)
    simpa only [diff,V,qvec,← map_sub,LinearIsometryEquiv.norm_map,OracleInterface.D,Iq] using h
  have nv : ‖V G‖ ≤ ‖v‖ := by
    unfold V qvec
    rw [LinearIsometryEquiv.norm_map]
    exact ((stdOracle X Y ((QReg.of E) × Unit)).O_le G _).trans_eq (LinearIsometryEquiv.norm_map ..)
  have step (i : I) : mass (p i) (applyPort (g i) (ketBra v v)) ≤
      mass (p i) (applyPort G (ketBra v v)) + a*‖v‖^2 + (1+1/a)*‖diff i‖^2 := by
    simp only [move]
    have id : V G + diff i = V (g i) := by simp [diff]
    have e := shift (p i) (V G) (diff i) a ha
    rw [id] at e
    exact e.trans (by nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) nv 2) ha.le])
  apply (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (step i) (hw i)).trans
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul]
  have sc : ∑ i, w i*((1+1/a)*‖diff i‖^2) = (1+1/a)*∑ i, w i*‖diff i‖^2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [sc]
  unfold cost
  nlinarith [mul_le_mul_of_nonneg_right total (show 0 ≤ a*‖v‖^2 by positivity),
    mul_le_mul_of_nonneg_left nd (show 0 ≤ 1+1/a by positivity)]

private theorem sum_mass {W B : Type} [Fintype W] [Fintype B] (p : Closed W Bool)
    (m : B → Matrix W W ℂ) (h : ∀ b, (m b).PosSemidef) :
    mass p (∑ b, m b) = ∑ b, mass p (m b) := by
  obtain ⟨L,hL⟩ := linear_test p
  rw [← hL _ (Matrix.posSemidef_sum _ (fun i _ => h i)),map_sum,Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => hL _ (h i)

include hw total support hr ha risk in
theorem port_step (p : I → Closed Work Bool) (M : Matrix Work Work ℂ) (h : M.PosSemidef) :
    ∑ i, w i * mass (p i) (applyPort (g i) M) ≤
      ∑ i, w i * mass (p i) (applyPort G M) + cost r a * M.trace.re := by
  obtain ⟨v,eq⟩ := exists_ketBra_sum h
  have split (B : Closed Work Bool) (H : X → Y) :
      mass B (applyPort H M) = ∑ t, mass B (applyPort H (ketBra (v t) (v t))) := by
    rw [eq,applyPort,map_sum]
    exact sum_mass _ _ (fun t => port_positive H (posSemidef_ketBra_self (v t)))
  have tr : M.trace.re = ∑ t, ‖v t‖^2 := by
    rw [eq,Matrix.trace_sum,Complex.re_sum]; simp only [trace_re_ketBra_self]
  simp only [split,Finset.mul_sum,tr]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => lhs; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun t _ => pure_port w hw total g G rows support r a hr ha risk p (v t)

end
end Reduction.ShakePermutation.MsgEffect
#print axioms Reduction.ShakePermutation.MsgEffect.port_step
