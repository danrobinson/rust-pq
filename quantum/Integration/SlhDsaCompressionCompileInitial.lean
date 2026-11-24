import Integration.SlhDsaCompressionCompileKraus

namespace Reduction.Compression.Recording.Compile
set_option linter.unusedSectionVars false
open MLink Ideal PQ.QROM Quantum Database Classical
universe u v w
variable {A : QReg} {L : LocalSig.{u,v}} {W : QReg → Type w}

private noncomputable def emptyOnly {X Y V : Type} [Zero V] (u : V) (d : DB X Y) : V := by
  classical
  exact if d = fun _ => none then u else 0

section Empty
variable {X Y V T : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem emptyOnly_mass (u : V) : ∑ d : DB X Y, ‖emptyOnly u d‖ ^ 2 = ‖u‖^2 := by
  classical
  simp [emptyOnly,apply_ite (fun v : V => ‖v‖),ite_pow]

private theorem emptyOnly_bad (p : Y → T) (u : V) :
    sumWeight (Collision (I := X) p) (emptyOnly u) = 0 := by
  classical
  unfold sumWeight
  apply Finset.sum_eq_zero
  intro d _
  by_cases h : d = fun _ => none
  · subst d
    exact ite_eq_right (by rintro ⟨i,j,a,b,hd,hi,_⟩; cases hi)
  · simp [emptyOnly,h]

private theorem emptyOnly_sparse (u : V) (d : DB X Y) (hd : 0 < (occupied d).card) : emptyOnly u d = 0 := by
  classical
  refine ite_eq_right fun h => ?_
  subst d
  simp [occupied] at hd

private theorem emptyOnly_tensor (h : X → Y) (u : V) :
    tensor (emptyOnly u) (fun i => some (h i)) = coeff Y ^ Fintype.card X • u := by
  classical
  simp [tensor, emptyOnly, smul_ite, coeffDB, entry]
end Empty

/-- Before the first query, all recording cells are empty. -/
noncomputable def initialState (u : Vec A) : State A := emptyOnly u

theorem initial_mass (u : Vec A) : ∑ d, ‖initialState u d‖ ^ 2 = ‖u‖^2 := emptyOnly_mass u

theorem initial_bad {T : Type} (p : Chain512 → T) (u : Vec A) :
    sumWeight (Collision p) (initialState u) = 0 := emptyOnly_bad p u

theorem initial_sparse (u : Vec A) : sparse 0 (initialState u) := emptyOnly_sparse u

theorem initial_tensor (h : Full) (u : Vec A) :
    tensor (initialState u) (fun i => some (h i)) = coeff Chain512 ^ Fintype.card Input • u :=
  emptyOnly_tensor h u

theorem pv_smul_real (I : L.Interp) (H : Input → Output) (x : QuantumComp L (qromSpec Input Output) W A)
    (ev : (Σ i, W i) → Prop) (r : ℝ) (u : Vec A) :
    Purify.pv I H x ev (r • u) = r^2 * Purify.pv I H x ev u := by
  have e : ketBra (r • u) (r • u) = ((r : ℂ)^2) • ketBra u u := by
    ext i j
    simp only [ketBra_apply,WithLp.ofLp_smul,Pi.smul_apply,Complex.real_smul,star_mul',
      Complex.star_def,Complex.conj_ofReal,Matrix.smul_apply,smul_eq_mul]
    ring
  unfold Purify.pv Purify.gv
  rw [e,map_smul]
  simp [smul_eq_mul, ← Complex.ofReal_pow]

theorem initial_pv (I : L.Interp) (a : CF St Blk) (h : Full) (x : QuantumComp L (qromSpec Input Output) W A)
    (ev : (Σ i, W i) → Prop) (u : Vec A) :
    Purify.pv I (project a h) x ev (tensor (initialState u) (fun i => some (h i))) =
      (Fintype.card Full : ℝ)⁻¹ * Purify.pv I (project a h) x ev u := by
  rw [initial_tensor,pv_smul_real,total_weight]

theorem initial_numeric (q : ℕ) (N : ℝ) (hN : 0 < N) (b : ℝ) (hb : 0 ≤ b) :
    (Real.sqrt 0 + (4 * (q:ℝ) * Real.sqrt ((q:ℝ)/N) + 2 * Real.sqrt (4/N)) * Real.sqrt b)^2 ≤
      16*((q:ℝ)+1)^3/N * b := by
  have hq : 0 ≤ (q:ℝ) := Nat.cast_nonneg _
  have e : 4 * (q:ℝ) * Real.sqrt ((q:ℝ)/N) = Real.sqrt (16 * (q:ℝ)^3/N) := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    ring
  rw [Real.sqrt_zero,zero_add,e,mul_pow,Real.sq_sqrt hb]
  exact mul_le_mul_of_nonneg_right (numeric q N hN) hb

end Reduction.Compression.Recording.Compile
#print axioms Reduction.Compression.Recording.Compile.initial_pv
#print axioms Reduction.Compression.Recording.Compile.initial_numeric
