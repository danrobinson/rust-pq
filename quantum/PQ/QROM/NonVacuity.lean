import PQ.QROM.Preimage
import PQ.QROM.Hybrid
import VCVio.Quantum.Oracle.Classical
import VCVio.Quantum.Oracle.Comb

/-!
# Non-vacuity of the QROM development

Machine-checked sanity checks for the objects quantified over in `PQ/QROM`:

1. **The preimage game can be lost** (`preimage_game_const`): the zero-query program that outputs
   a constant wins the uniform-target preimage game of `preimage_uniform_le` with probability
   exactly `1/|Y|`, which is `< 1` for `|Y| ≥ 2` and equal to the bound at `q = 0`
   (`preimage_bound_zero_tight`).
2. **The preimage game can be won** (`preimage_game_oneQuery`): on `X = Y = Fin 2` the one-query
   program "query `H 0`; output `0` if `H 0 = y`, else `1`" wins with probability exactly `3/4`,
   strictly more than the zero-query value `1/2`.

   NOTE: the programs of items 1 and 2 are CLASSICAL strategies (`constGuess`, `oneQueryGuess`:
   deterministic `OracleComp` algorithms), embedded in the quantum query model by
   `OracleComp.toQuantum` (each query: prepare `|t, 0⟩`, call the oracle unitary, measure).  They
   show that the experiment is neither trivially lost nor trivially won; they exhibit no quantum
   behaviour.  The only genuinely quantum programs are Deutsch's algorithm (item 3) and Grover's
   algorithm (`PQ/QROM/NonVacuity2.lean`).
3. **The adversary class contains genuinely quantum algorithms** (`qprob_deutsch`,
   `queryBounded_deutsch`): Deutsch's algorithm, a program with `QueryBounded _ 1`, outputs
   `H 0 + H 1` with `qprob = 1` for every `H : Fin 2 → Fin 2`; every deterministic classical
   one-query strategy succeeds for exactly half of the functions
   (`classical_oneQuery_parity_card`, `qprob_classical_oneQuery_parity`).  Every fixed-slot
   circuit `U_q O ⋯ O U_0` is a `q`-query program (`queryBounded_comb`).

All statements are about `qprob`, `QueryBounded` and `HybridModel.ofProgram`, the objects of the
bounds.
-/

open MeasureTheory ENNReal Quantum Matrix OracleSpec
open scoped Kronecker ComplexOrder

namespace PQ.QROM.NonVacuity

/-! ## `qprob` of fixed-register programs and of classical algorithms -/

section bridge

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- `qprob` of a fixed-register program is the weight its returned value puts on the event. -/
theorem qprob_eq_evalDist₂ {L : LocalSig} {A B : QReg} {α : Type} [MeasurableSpace α]
    (I : L.Interp) (H : X → Y) (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A)
    (E : α → Prop) (hE : MeasurableSet {a | E a}) :
    qprob I H x ρ (fun p ↦ E ((QuantumComp₂.leafEquiv B α).symm p)) =
      (additiveOracleRuntime H).evalDist₂ I x ρ {a | E a} := by
  classical
  have h1 := (additiveOracleRuntime H).evalDistMap_apply I
    (show QuantumComp L (qromSpec X Y) (QuantumComp₂.Leaf B α) A from x) ρ
    (fun p ↦ E ((QuantumComp₂.leafEquiv B α).symm p)) (MeasurableSet.singleton True)
  have h2 := (additiveOracleRuntime H).evalDistMap_apply I
    (show QuantumComp L (qromSpec X Y) (QuantumComp₂.Leaf B α) A from x) ρ
    (QuantumComp₂.leafEquiv B α).symm hE
  rw [QuantumRuntime.evalDist₂_eq_evalDistMap]
  refine h1.trans ((tsum_congr fun p ↦ congrArg _ ?_).trans h2.symm)
  by_cases h : E ((QuantumComp₂.leafEquiv B α).symm p) <;> simp [h]

/-- The program of a classical algorithm, run against the oracle unitary of `H`, ends in the
value of the algorithm on `H` with probability one. -/
theorem qprob_toQuantum {α : Type} (H : X → Y) (oa : OracleComp (X →ₒ Y) α) (E : α → Prop)
    [Decidable (E (evalWithAnswerFn (QueryImpl.ofFn H) oa))] :
    qprob .instruments H oa.toQuantum (SubState.basis ())
        (fun p ↦ E ((QuantumComp₂.leafEquiv (QReg.of Unit) α).symm p)) =
      if E (evalWithAnswerFn (QueryImpl.ofFn H) oa) then 1 else 0 := by
  let : MeasurableSpace α := ⊤
  rw [qprob_eq_evalDist₂ _ _ _ _ _ (MeasurableSpace.measurableSet_top),
    evalDist_additiveOracleRuntime_toQuantum, Measure.dirac_apply' _
      (MeasurableSpace.measurableSet_top)]
  by_cases h : E (evalWithAnswerFn (QueryImpl.ofFn H) oa) <;> simp [h]

/-- The `HybridModel` (the interface of `preimage_uniform_le`) of a classical `q`-query
algorithm, embedded as a quantum query program. -/
noncomputable def classicalModel {α : Type} (oa : OracleComp (X →ₒ Y) α) (q : ℕ)
    (hq : OracleComp.IsTotalQueryBound oa q) : HybridModel X Y α q :=
  HybridModel.ofProgram .instruments oa.toQuantum (SubState.basis ()) q
    (OracleComp.isQueryBound_toQuantum hq) (QuantumComp₂.leafEquiv (QReg.of Unit) α).symm

theorem classicalModel_prob {α : Type} (oa : OracleComp (X →ₒ Y) α) (q : ℕ)
    (hq : OracleComp.IsTotalQueryBound oa q) (H : X → Y) (E : α → Prop)
    [Decidable (E (evalWithAnswerFn (QueryImpl.ofFn H) oa))] :
    (classicalModel oa q hq).prob H E =
      if E (evalWithAnswerFn (QueryImpl.ofFn H) oa) then 1 else 0 :=
  qprob_toQuantum H oa E

end bridge

/-! ## 1. The preimage game can be lost -/

section lose

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The zero-query CLASSICAL algorithm with constant output `x₀` (embedded as a quantum program
by `OracleComp.toQuantum`). -/
def constGuess (x₀ : X) : OracleComp (X →ₒ Y) X := pure x₀

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
theorem isTotalQueryBound_constGuess (x₀ : X) :
    OracleComp.IsTotalQueryBound (constGuess (Y := Y) x₀) 0 :=
  trivial

/-- The program of `constGuess` makes no oracle call. -/
theorem queryBounded_constGuess (x₀ : X) :
    QueryBounded (constGuess (Y := Y) x₀).toQuantum 0 :=
  OracleComp.isQueryBound_toQuantum (isTotalQueryBound_constGuess x₀)

/-- Against a fixed `H`, the constant guess `x₀` is a preimage of `y` iff `H x₀ = y`: the
probability is `0` or `1`, not constantly `1`. -/
theorem qprob_constGuess (x₀ : X) (H : X → Y) (y : Y) :
    qprob .instruments H (constGuess (Y := Y) x₀).toQuantum (SubState.basis ())
        (fun p ↦ H ((QuantumComp₂.leafEquiv (QReg.of Unit) X).symm p) = y) =
      if H x₀ = y then 1 else 0 :=
  qprob_toQuantum H (constGuess x₀) fun a ↦ H a = y

/-- **The preimage game can be lost.**  The experiment of `preimage_uniform_le`, for the
zero-query program with constant output (a classical strategy, embedded via `toQuantum`), has
value exactly `1/|Y|`. -/
theorem preimage_game_const (x₀ : X) :
    ∑ H : X → Y, ∑ y : Y,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card Y : ℝ≥0∞)⁻¹) *
          (classicalModel (constGuess (Y := Y) x₀) 0 (isTotalQueryBound_constGuess x₀)).prob H
            (fun p ↦ H (id p) = y) =
      1 / (Fintype.card Y : ℝ≥0∞) := by
  have h : ∀ H : X → Y, ∑ y : Y,
      ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card Y : ℝ≥0∞)⁻¹) *
        (classicalModel (constGuess (Y := Y) x₀) 0 (isTotalQueryBound_constGuess x₀)).prob H
          (fun p ↦ H (id p) = y) =
      (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card Y : ℝ≥0∞)⁻¹ := fun H ↦ by
    simp only [classicalModel_prob]
    rw [Finset.sum_eq_single (H x₀) (fun y _ hy ↦ by simp [constGuess, Ne.symm hy])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    simp [constGuess]
  rw [Finset.sum_congr rfl fun H _ ↦ h H, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, natCast_mul_inv_cancel Fintype.card_ne_zero, one_mul, one_div]

/-- The value `1/|Y|` is strictly below one as soon as `Y` has two elements: the experiment is not
trivially won. -/
theorem preimage_game_const_lt_one (x₀ : X) (hY : 2 ≤ Fintype.card Y) :
    ∑ H : X → Y, ∑ y : Y,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card Y : ℝ≥0∞)⁻¹) *
          (classicalModel (constGuess (Y := Y) x₀) 0 (isTotalQueryBound_constGuess x₀)).prob H
            (fun p ↦ H (id p) = y) < 1 := by
  rw [preimage_game_const, one_div]
  exact ENNReal.inv_lt_one.2 (by exact_mod_cast hY)

omit [DecidableEq Y] [AddCommGroup Y] in
/-- At `q = 0` the bound of `preimage_uniform_le` is `1/|Y|`: it is attained by `constGuess`
(`preimage_game_const`), and is `< 1` for `|Y| ≥ 2`. -/
theorem preimage_bound_zero_tight :
    (2 * ((0 : ℕ) : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) = 1 / (Fintype.card Y : ℝ≥0∞) := by
  simp

end lose

/-! ## 2. The preimage game can be won on a toy instance -/

section win

/-- A sum over the four functions `Fin 2 → Fin 2`. -/
theorem sum_fun_fin_two {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Fin 2) → M) :
    ∑ H, f H = f ![0, 0] + f ![0, 1] + f ![1, 0] + f ![1, 1] := by
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp f]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc]

/-- The one-query CLASSICAL algorithm for target `y`: query `H 0`; output `0` if `H 0 = y`, else
`1`.  It is embedded as a quantum program by `OracleComp.toQuantum`; nothing quantum happens. -/
def oneQueryGuess (y : Fin 2) : OracleComp (Fin 2 →ₒ Fin 2) (Fin 2) := do
  let z ← liftM ((Fin 2 →ₒ Fin 2).query 0)
  pure (if z = y then 0 else 1)

theorem isTotalQueryBound_oneQueryGuess (y : Fin 2) :
    OracleComp.IsTotalQueryBound (oneQueryGuess y) 1 := by
  rw [oneQueryGuess, OracleComp.isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- The program of `oneQueryGuess` makes one oracle call. -/
theorem queryBounded_oneQueryGuess (y : Fin 2) : QueryBounded (oneQueryGuess y).toQuantum 1 :=
  OracleComp.isQueryBound_toQuantum (isTotalQueryBound_oneQueryGuess y)

theorem evalWithAnswerFn_oneQueryGuess (H : Fin 2 → Fin 2) (y : Fin 2) :
    evalWithAnswerFn (QueryImpl.ofFn H) (oneQueryGuess y) = if H 0 = y then 0 else 1 :=
  rfl

/-- Against a fixed `H`, the one-query program finds a preimage of `y` iff `H 0 = y` or
`H 1 = y`. -/
theorem qprob_oneQueryGuess (H : Fin 2 → Fin 2) (y : Fin 2) :
    qprob .instruments H (oneQueryGuess y).toQuantum (SubState.basis ())
        (fun p ↦ H ((QuantumComp₂.leafEquiv (QReg.of Unit) (Fin 2)).symm p) = y) =
      if H 0 = y ∨ H 1 = y then 1 else 0 := by
  rw [qprob_toQuantum H (oneQueryGuess y) fun a ↦ H a = y, evalWithAnswerFn_oneQueryGuess]
  by_cases h : H 0 = y <;> simp [h]

theorem inv_four_mul_inv_two_mul_six : ((4 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) * 6 = 3 / 4 := by
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

/-- **The preimage game can be won on a toy instance.**  The experiment of
`preimage_uniform_le` on `X = Y = Fin 2`, for the one-query program `oneQueryGuess` (a CLASSICAL
strategy, embedded via `toQuantum`; not a quantum speed-up), has value exactly `3/4`. -/
theorem preimage_game_oneQuery :
    ∑ H : Fin 2 → Fin 2, ∑ y : Fin 2,
        ((Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹ * (Fintype.card (Fin 2) : ℝ≥0∞)⁻¹) *
          (classicalModel (oneQueryGuess y) 1 (isTotalQueryBound_oneQueryGuess y)).prob H
            (fun p ↦ H (id p) = y) =
      3 / 4 := by
  have hc : (Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞) = 4 := by simp
  simp only [classicalModel_prob, evalWithAnswerFn_oneQueryGuess, hc]
  rw [← inv_four_mul_inv_two_mul_six, sum_fun_fin_two]
  simp only [Fin.sum_univ_two, Fintype.card_fin, Nat.cast_ofNat]
  simp
  ring_nf

/-- The zero-query value on the same instance is `1/2`. -/
theorem preimage_game_const_fin_two (x₀ : Fin 2) :
    ∑ H : Fin 2 → Fin 2, ∑ y : Fin 2,
        ((Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹ * (Fintype.card (Fin 2) : ℝ≥0∞)⁻¹) *
          (classicalModel (constGuess (Y := Fin 2) x₀) 0 (isTotalQueryBound_constGuess x₀)).prob H
            (fun p ↦ H (id p) = y) =
      1 / 2 := by
  rw [preimage_game_const]
  simp

theorem one_half_lt_three_quarters : (1 / 2 : ℝ≥0∞) < 3 / 4 := by
  rw [← ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- One query strictly helps: the (classical, embedded) one-query program beats the (classical,
embedded) zero-query constant guess. -/
theorem preimage_game_const_lt_oneQuery (x₀ : Fin 2) :
    ∑ H : Fin 2 → Fin 2, ∑ y : Fin 2,
        ((Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹ * (Fintype.card (Fin 2) : ℝ≥0∞)⁻¹) *
          (classicalModel (constGuess (Y := Fin 2) x₀) 0 (isTotalQueryBound_constGuess x₀)).prob H
            (fun p ↦ H (id p) = y) <
      ∑ H : Fin 2 → Fin 2, ∑ y : Fin 2,
        ((Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹ * (Fintype.card (Fin 2) : ℝ≥0∞)⁻¹) *
          (classicalModel (oneQueryGuess y) 1 (isTotalQueryBound_oneQueryGuess y)).prob H
            (fun p ↦ H (id p) = y) := by
  rw [preimage_game_const_fin_two, preimage_game_oneQuery]
  exact one_half_lt_three_quarters

/-- Consistency with `preimage_uniform_le` at `q = 1`, `|Y| = 2`: the exact value `3/4` is below
the bound `(2·1+1)²/2 = 9/2`. -/
example :
    (3 / 4 : ℝ≥0∞) ≤ (2 * ((1 : ℕ) : ℝ≥0∞) + 1) ^ 2 / (Fintype.card (Fin 2) : ℝ≥0∞) := by
  rw [← preimage_game_oneQuery]
  exact preimage_uniform_le
    (fun y ↦ classicalModel (oneQueryGuess y) 1 (isTotalQueryBound_oneQueryGuess y)) fun _ p ↦ p

end win

/-! ## 3. The adversary class contains genuinely quantum algorithms -/

section comb

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

omit [AddCommGroup Y] in
/-- **Every fixed-slot `q`-query circuit is a `q`-query program.**  A comb `U_q O ⋯ O U_0` on a
register `M` (arbitrary lossless local operations `U_i`, arbitrary lossless final instrument),
whose queries go to the factor `X × Y` of `M ≃ (X × Y) × E`, embeds as the program
`Quantum.QuantumComb.toComp`; the program satisfies `QueryBounded _ q`, and it runs as the comb
does (`Quantum.QuantumComb.run_toComp`).  So the class quantified over in the bounds of
`PQ/QROM` contains all `q`-query quantum circuits. -/
theorem queryBounded_comb {M : Type} [Fintype M] [DecidableEq M] {α : Type} {q : ℕ}
    (c : QuantumComb M α q) (E : QReg) (ℓ : M ≃ (X × Y) × E) (ℓ' : (X × Y) × E ≃ M) :
    QueryBounded (c.toComp (spec := qromSpec X Y) () E ℓ ℓ') q :=
  (c.isQueryBound_toComp (spec := qromSpec X Y) () E ℓ ℓ').mono fun _ ↦ by simp

/-- The program of a comb runs as the comb: the steps, framed by the oracle's (trivial) private
register, interleaved with the oracle call. -/
theorem run_comb {M : Type} [Fintype M] [DecidableEq M] {α : Type} {q : ℕ}
    (c : QuantumComb M α q) (H : X → Y) (E : QReg) (ℓ : M ≃ (X × Y) × E)
    (ℓ' : (X × Y) × E ≃ M) :
    (additiveOracleRuntime H).run₂ .instruments (c.toComp (spec := qromSpec X Y) () E ℓ ℓ') =
      (c.frame (additiveOracleRuntime H).D (additiveOracleRuntime H).init).run
        ((additiveOracleRuntime H).combQuery () E ℓ ℓ') :=
  QuantumComb.run_toComp ..

/-- The oracle call of a comb whose register is the query register `X × Y`: on the comb's
register it is the oracle unitary `ρ ↦ U_H ρ U_H†`. -/
theorem traceRight_post_combQuery (H : X → Y) (ρ : SubState (X × Y)) :
    (((additiveOracleRuntime H).combQuery () (QReg.of Unit) (Equiv.prodPUnit (X × Y)).symm
        (Equiv.prodPUnit (X × Y))).post (ρ.prod (SubState.basis ())) ()).traceRight =
      (oracleQuery H).post ρ () := by
  refine SubState.ext ?_
  rw [SubState.matrix_traceRight, DSubInstrument.matrix_post, DSubInstrument.matrix_post,
    QuantumRuntime.combQuery, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
    QuantumRuntime.queryStep_branch_apply]
  ext m m'
  simp only [MatrixMap.traceRight_apply, DSubInstrument.branch_frame_apply,
    SubInstrument.relabel_branch_apply, MatrixMap.amplify_apply, Matrix.submatrix_apply,
    additiveOracleRuntime_step]
  refine (Fintype.sum_unique (ι := Unit) _).trans ?_
  change (((oracleQuery H).branch ()).amplify Unit).amplify Unit
    ((ρ.matrix ⊗ₖ (SubState.basis ()).matrix).submatrix
      (QuantumRuntime.queryEquivIn (Equiv.prodPUnit (X × Y)).symm Unit).symm
      (QuantumRuntime.queryEquivIn (Equiv.prodPUnit (X × Y)).symm Unit).symm)
    ((QuantumRuntime.queryEquivOut (X × Y) Unit Unit).symm ((m, ()), ()))
    ((QuantumRuntime.queryEquivOut (X × Y) Unit Unit).symm ((m', ()), ())) = _
  simp only [MatrixMap.amplify_apply]
  have key : ∀ σ : Matrix (X × Y) (X × Y) ℂ, σ = ρ.matrix → ∀ a b, a = m → b = m' →
      (oracleQuery H).branch () σ a b = (oracleQuery H).branch () ρ.matrix m m' := by
    rintro _ rfl _ _ rfl rfl
    rfl
  refine key _ ?_ _ _ rfl rfl
  ext x y
  simp [SubState.matrix_basis, Matrix.kroneckerMap_apply, QuantumRuntime.queryEquivIn]

end comb

/-! ### Deutsch's algorithm

The definitions follow `VCVioTest/Quantum/Oracle.lean` (re-proved here; the test library is not a
dependency). -/

section deutsch

/-- The register of Deutsch's algorithm: one query qubit and one response qubit. -/
abbrev Reg : Type := Fin 2 × Fin 2

/-- The sign `(-1) ^ y` of a bit. -/
def sgn (y : Fin 2) : ℂ :=
  if y = 0 then 1 else -1

/-- The amplitudes of the state `|+⟩|-⟩`. -/
noncomputable def amp : Reg → ℂ :=
  fun m ↦ sgn m.2 / 2

/-- The projector onto `|+⟩` (for `b = 0`) or `|-⟩` (for `b = 1`) of the query qubit. -/
noncomputable def proj (b : Fin 2) : Matrix Reg Reg ℂ :=
  Matrix.of fun m m' ↦ if m.2 = m'.2 then sgn (b * (m.1 + m'.1)) / 2 else 0

theorem eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- The projectors onto `|+⟩` and `|-⟩` satisfy the completeness relation. -/
theorem sum_conjTranspose_proj_mul_proj : ∑ b, (proj b)ᴴ * proj b = 1 := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  rcases eq_zero_or_one x with rfl | rfl <;> rcases eq_zero_or_one y with rfl | rfl <;>
    rcases eq_zero_or_one x' with rfl | rfl <;> rcases eq_zero_or_one y' with rfl | rfl <;>
    norm_num [Fin.sum_univ_two, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, proj,
      sgn, map_ofNat]

/-- The state `|+⟩|-⟩`. -/
noncomputable def plusMinus : SubState Reg where
  matrix := vecMulVec amp (star amp)
  posSemidef := Matrix.posSemidef_vecMulVec_self_star amp
  trace_re_le_one := by
    norm_num [Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two, amp, sgn]

/-- Deutsch's algorithm as a one-query circuit: start in `|+⟩|-⟩`, query once, and measure the
query qubit in the `|±⟩` basis. -/
noncomputable def deutsch : QuantumComb Reg (Fin 2) 1 where
  init := plusMinus
  step _ := SubInstrument.pure ()
  lossless_step _ := DSubInstrument.lossless_ret (fun _ : Unit ↦ Reg) ()
  final := DSubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj
  lossless_final := DSubInstrument.lossless_ofKraus _ _

/-- The weight of a Kraus branch on a pure state is the squared norm of the image vector. -/
theorem trace_conj_vecMulVec {A B : Type} [Fintype A] [Fintype B] (K : Matrix B A ℂ)
    (v : A → ℂ) :
    (MatrixMap.conj K (vecMulVec v (star v))).trace = ∑ i, (K *ᵥ v) i * star ((K *ᵥ v) i) := by
  rw [MatrixMap.conj_apply, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec,
    Matrix.trace_vecMulVec]
  rfl

/-- After the query, the measurement reports `H 0 + H 1` with weight one. -/
theorem trace_conj_proj (H : Fin 2 → Fin 2) (b : Fin 2) :
    (MatrixMap.conj (proj b)
      (MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)))).trace =
      if b = H 0 + H 1 then 1 else 0 := by
  have h : MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)) =
      vecMulVec (fun m ↦ amp ((oracleEquiv H).symm m))
        (star fun m ↦ amp ((oracleEquiv H).symm m)) := by
    rw [oracleUnitary, conj_basisMatrix_equiv]
    rfl
  rw [h, trace_conj_vecMulVec]
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    rcases eq_zero_or_one b with rfl | rfl <;>
    norm_num [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, proj, amp, sgn,
      oracleEquiv_symm_apply, h0, h1]

/-- The final measurement on the state after the query reports `H 0 + H 1` with certainty. -/
theorem outcomeMeasure_final_deutsch (H : Fin 2 → Fin 2) :
    deutsch.final.outcomeMeasure ((oracleQuery H).post plusMinus ()) =
      Measure.dirac (H 0 + H 1) := by
  rw [DSubInstrument.outcomeMeasure_eq_sum_univ, Fin.sum_univ_two]
  have h : ∀ b, (deutsch.final.branch b ((oracleQuery H).post plusMinus ()).matrix).trace =
      if b = H 0 + H 1 then 1 else 0 := fun b ↦ by
    have h₁ : ((oracleQuery H).post plusMinus ()).matrix =
        MatrixMap.conj (oracleUnitary H) (vecMulVec amp (star amp)) := by
      simp [MatrixMap.conj_apply, plusMinus]
    rw [h₁]
    change ((DSubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj).branch b _).trace = _
    rw [DSubInstrument.branch_ofKraus_apply]
    exact trace_conj_proj H b
  rw [h, h]
  rcases eq_zero_or_one (H 0) with h0 | h0 <;> rcases eq_zero_or_one (H 1) with h1 | h1 <;>
    simp [h0, h1]

/-- Deutsch's algorithm as a query program in the model of `PQ/QROM`: the program of the comb
`deutsch`, whose call goes to the whole register `Fin 2 × Fin 2` (trivial remainder). -/
noncomputable def deutschComp :
    QComp (qromSpec (Fin 2) (Fin 2)) (QReg.of Reg) (QReg.of Reg) (Fin 2) :=
  deutsch.toComp () (QReg.of Unit) (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg)

/-- Deutsch's program makes ONE oracle call. -/
theorem queryBounded_deutsch : QueryBounded deutschComp 1 :=
  queryBounded_comb deutsch (QReg.of Unit) (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg)

/-- Deutsch's program is lossless. -/
theorem lossless_deutsch : deutschComp.Lossless .instruments :=
  deutsch.lossless_toComp (spec := qromSpec (Fin 2) (Fin 2)) () _ _ _

/-- Against the oracle unitary of `H`, Deutsch's program returns `H 0 + H 1` with certainty. -/
theorem evalDist₂_deutsch (H : Fin 2 → Fin 2) :
    (additiveOracleRuntime H).evalDist₂ .instruments deutschComp plusMinus =
      Measure.dirac (H 0 + H 1) := by
  have h := QuantumComb.evalDist_toComp deutsch (additiveOracleRuntime H) () (QReg.of Unit)
    (Equiv.prodPUnit Reg).symm (Equiv.prodPUnit Reg)
  rw [QuantumComb.outcomeMeasure_run, show Fin.last 1 = (0 : Fin 1).succ from rfl,
    QuantumComb.stateAfterStep_succ, show Fin.castSucc (0 : Fin 1) = 0 from rfl,
    QuantumComb.stateAfterStep_zero] at h
  have hp : ∀ σ : SubState (Reg × Unit),
      ((SubInstrument.pure () : SubInstrument Reg Reg Unit).frame Unit).post σ () = σ := fun σ ↦ by
    rw [SubInstrument.frame_pure]
    exact DSubInstrument.post_ret_self _ _
  have main : ∀ Q : SubInstrument (Reg × Unit) (Reg × Unit) Unit,
      (Q.post (plusMinus.prod (SubState.basis ())) ()).traceRight =
        (oracleQuery H).post plusMinus () →
      (deutsch.final.frame Unit).outcomeMeasure
        (((SubInstrument.pure () : SubInstrument Reg Reg Unit).frame Unit).post
          (Q.post (((SubInstrument.pure () : SubInstrument Reg Reg Unit).frame Unit).post
            (plusMinus.prod (SubState.basis ())) ()) ()) ()) = Measure.dirac (H 0 + H 1) := by
    intro Q hQ
    rw [hp, hp, DSubInstrument.outcomeMeasure_frame, hQ, outcomeMeasure_final_deutsch]
  exact h.trans (main _ (traceRight_post_combQuery H plusMinus))

/-- **A genuinely quantum one-query algorithm.**  For every `H : Fin 2 → Fin 2`, Deutsch's
program (one oracle call, `queryBounded_deutsch`), run from `|+⟩|-⟩` against the oracle unitary
of `H`, outputs the parity `H 0 + H 1` with probability one. -/
theorem qprob_deutsch (H : Fin 2 → Fin 2) :
    qprob .instruments H deutschComp plusMinus
        (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Reg) (Fin 2)).symm p = H 0 + H 1) = 1 := by
  rw [qprob_eq_evalDist₂ _ _ _ _ (fun a ↦ a = H 0 + H 1) (measurableSet_singleton _),
    evalDist₂_deutsch]
  simp

/-- The input state `|+⟩|-⟩` of Deutsch's algorithm is normalized. -/
theorem trace_plusMinus : plusMinus.matrix.trace = 1 := by
  norm_num [plusMinus, Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    amp, sgn]

end deutsch

/-! ### No classical one-query algorithm computes the parity -/

section classicalParity

/-- A deterministic classical one-query strategy: query the point `a`, output `g (H a)`. -/
def classicalOneQuery (a : Fin 2) (g : Fin 2 → Fin 2) : OracleComp (Fin 2 →ₒ Fin 2) (Fin 2) := do
  let z ← liftM ((Fin 2 →ₒ Fin 2).query a)
  pure (g z)

theorem isTotalQueryBound_classicalOneQuery (a : Fin 2) (g : Fin 2 → Fin 2) :
    OracleComp.IsTotalQueryBound (classicalOneQuery a g) 1 := by
  rw [classicalOneQuery, OracleComp.isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- Its program makes one oracle call. -/
theorem queryBounded_classicalOneQuery (a : Fin 2) (g : Fin 2 → Fin 2) :
    QueryBounded (classicalOneQuery a g).toQuantum 1 :=
  OracleComp.isQueryBound_toQuantum (isTotalQueryBound_classicalOneQuery a g)

/-- Every deterministic classical one-query strategy outputs the parity `H 0 + H 1` for exactly
two of the four functions `H : Fin 2 → Fin 2`. -/
theorem classical_oneQuery_parity_card (a : Fin 2) (g : Fin 2 → Fin 2) :
    (Finset.univ.filter fun H : Fin 2 → Fin 2 ↦ g (H a) = H 0 + H 1).card = 2 := by
  revert a g
  decide

/-- Against a fixed `H`, the program of a classical one-query strategy outputs the parity with
probability `1` or `0` according to whether `g (H a) = H 0 + H 1`. -/
theorem qprob_classicalOneQuery (a : Fin 2) (g : Fin 2 → Fin 2) (H : Fin 2 → Fin 2) :
    qprob .instruments H (classicalOneQuery a g).toQuantum (SubState.basis ())
        (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) (Fin 2)).symm p = H 0 + H 1) =
      if g (H a) = H 0 + H 1 then 1 else 0 :=
  qprob_toQuantum H (classicalOneQuery a g) fun b ↦ b = H 0 + H 1

/-- **Classical impossibility.**  For every deterministic classical one-query strategy, embedded
as a quantum program, the probability over a uniform `H : Fin 2 → Fin 2` of outputting the
parity `H 0 + H 1` is exactly `1/2`; Deutsch's program achieves `1` (`qprob_deutsch`).
Randomised classical one-query strategies (mixtures, and programs with private uniform coins)
are covered in `PQ/QROM/NonVacuity2.lean`. -/
theorem qprob_classical_oneQuery_parity (a : Fin 2) (g : Fin 2 → Fin 2) :
    ∑ H : Fin 2 → Fin 2, (Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹ *
        qprob .instruments H (classicalOneQuery a g).toQuantum (SubState.basis ())
          (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) (Fin 2)).symm p = H 0 + H 1) =
      1 / 2 := by
  have h : ∀ H : Fin 2 → Fin 2, (Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹ *
      qprob .instruments H (classicalOneQuery a g).toQuantum (SubState.basis ())
        (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) (Fin 2)).symm p = H 0 + H 1) =
      if g (H a) = H 0 + H 1 then (Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹ else 0 := fun H ↦ by
    refine (congrArg _ (qprob_classicalOneQuery a g H)).trans ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun H _ ↦ h H, ← Finset.sum_filter, Finset.sum_const,
    classical_oneQuery_parity_card]
  have hc : (Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞) = 4 := by simp
  rw [hc, nsmul_eq_mul, Nat.cast_ofNat,
    ← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-- The same average for Deutsch's program is `1`. -/
theorem qprob_deutsch_parity :
    ∑ H : Fin 2 → Fin 2, (Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹ *
        qprob .instruments H deutschComp plusMinus
          (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Reg) (Fin 2)).symm p = H 0 + H 1) = 1 := by
  rw [Finset.sum_congr rfl fun H _ ↦ congrArg _ (qprob_deutsch H)]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact natCast_mul_inv_cancel Fintype.card_ne_zero

end classicalParity

end PQ.QROM.NonVacuity

#print axioms PQ.QROM.NonVacuity.preimage_game_const
#print axioms PQ.QROM.NonVacuity.preimage_game_const_lt_one
#print axioms PQ.QROM.NonVacuity.preimage_game_oneQuery
#print axioms PQ.QROM.NonVacuity.preimage_game_const_lt_oneQuery
#print axioms PQ.QROM.NonVacuity.queryBounded_comb
#print axioms PQ.QROM.NonVacuity.run_comb
#print axioms PQ.QROM.NonVacuity.queryBounded_deutsch
#print axioms PQ.QROM.NonVacuity.qprob_deutsch
#print axioms PQ.QROM.NonVacuity.classical_oneQuery_parity_card
#print axioms PQ.QROM.NonVacuity.qprob_classical_oneQuery_parity
#print axioms PQ.QROM.NonVacuity.qprob_deutsch_parity
#print axioms PQ.QROM.NonVacuity.qprob_constGuess
#print axioms PQ.QROM.NonVacuity.qprob_oneQueryGuess
#print axioms PQ.QROM.NonVacuity.preimage_game_const_fin_two
#print axioms PQ.QROM.NonVacuity.lossless_deutsch
#print axioms PQ.QROM.NonVacuity.trace_plusMinus
#print axioms PQ.QROM.NonVacuity.qprob_classicalOneQuery
