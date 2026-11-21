import PQ.QROM.NonVacuity

/-!
# Non-vacuity of the QROM development, part 2: quantum speed-ups

* **Grover on four items** (`qprob_grover`, `queryBounded_grover`): for the search space
  `Fin 2 × Fin 2` with exactly one marked item `w` (oracle `mark w`, the indicator of `w`), a
  program with `QueryBounded _ 1` outputs `w` with `qprob = 1`, for every `w`.
* **Classical one-query search** (`classical_search_card_le`,
  `qprob_classical_search_le`, `qprob_classical_search_mixture_le`): every deterministic
  classical one-query strategy, embedded as a quantum program, finds the marked item for at most
  two of the four positions, i.e. with probability at most `1/2` over a uniform position; so does
  every mixture of such strategies.
* **Randomised classical strategies for the parity** (`classical_parity_mixture`,
  `qprob_coin_classical_parity`): every mixture of deterministic one-query strategies outputs
  `H 0 + H 1` with probability exactly `1/2` over a uniform `H : Fin 2 → Fin 2`; Deutsch's
  program achieves `1` (`PQ.QROM.NonVacuity.qprob_deutsch`).
-/

open MeasureTheory ENNReal Quantum Matrix OracleSpec
open scoped Kronecker ComplexOrder

namespace PQ.QROM.NonVacuity

/-! ## One-query circuits on the query register -/

section oneQuery

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- A one-query circuit on the register `X × Y` with trivial local steps (state preparation is
its initial state, everything else is its final instrument), run as a program against the oracle
unitary of `H`: the final instrument measures `U_H ρ U_H†`. -/
theorem evalDist₂_comb_one {α : Type} [MeasurableSpace α] (c : QuantumComb (X × Y) α 1)
    (hc : ∀ i, c.step i = SubInstrument.pure ()) (H : X → Y) :
    (additiveOracleRuntime H).evalDist₂ .instruments
        (c.toComp (spec := qromSpec X Y) () (QReg.of Unit) (Equiv.prodPUnit (X × Y)).symm
          (Equiv.prodPUnit (X × Y))) c.init =
      c.final.outcomeMeasure ((oracleQuery H).post c.init ()) := by
  have h := QuantumComb.evalDist_toComp c (additiveOracleRuntime H) () (QReg.of Unit)
    (Equiv.prodPUnit (X × Y)).symm (Equiv.prodPUnit (X × Y))
  rw [QuantumComb.outcomeMeasure_run, show Fin.last 1 = (0 : Fin 1).succ from rfl,
    QuantumComb.stateAfterStep_succ, show Fin.castSucc (0 : Fin 1) = 0 from rfl,
    QuantumComb.stateAfterStep_zero] at h
  have hp : ∀ σ : SubState ((X × Y) × Unit),
      ((SubInstrument.pure () : SubInstrument (X × Y) (X × Y) Unit).frame Unit).post σ () = σ :=
    fun σ ↦ by
      rw [SubInstrument.frame_pure]
      exact DSubInstrument.post_ret_self _ _
  have main : ∀ Q : SubInstrument ((X × Y) × Unit) ((X × Y) × Unit) Unit,
      (Q.post (c.init.prod (SubState.basis ())) ()).traceRight = (oracleQuery H).post c.init () →
      (c.final.frame Unit).outcomeMeasure
        (((c.step (Fin.succ 0)).frame Unit).post
          (Q.post (((c.step 0).frame Unit).post (c.init.prod (SubState.basis ())) ()) ()) ()) =
        c.final.outcomeMeasure ((oracleQuery H).post c.init ()) := by
    intro Q hQ
    rw [hc, hc, hp, hp, DSubInstrument.outcomeMeasure_frame, hQ]
  exact h.trans (main _ (traceRight_post_combQuery H c.init))

end oneQuery

/-! ## Grover's algorithm on four items -/

section grover

/-- The search space: two qubits. -/
abbrev GX : Type := Fin 2 × Fin 2

/-- The register of Grover's algorithm: the query register and one response qubit. -/
abbrev GReg : Type := GX × Fin 2

/-- The oracle with the single marked item `w`. -/
def mark (w : GX) : GX → Fin 2 := fun x ↦ if x = w then 1 else 0

/-- Twice the amplitudes of `|+⟩|+⟩|-⟩` up to normalization: `(-1)^y / 2`, a vector of squared
norm `2`. -/
noncomputable def gamp : GReg → ℂ :=
  fun m ↦ sgn m.2 / 2

/-- The state `|+⟩|+⟩|-⟩`: the uniform superposition of the four items, with the response qubit
in `|-⟩`. -/
noncomputable def groverInit : SubState GReg where
  matrix := (1 / 2 : ℂ) • vecMulVec gamp (star gamp)
  posSemidef := (Matrix.posSemidef_vecMulVec_self_star gamp).smul (by rw [Complex.le_def]; norm_num)
  trace_re_le_one := by
    norm_num [Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two, gamp, sgn]

/-- The Kraus operator `(|k⟩⟨k| D) ⊗ 1` of "apply the diffusion `D = 2|s⟩⟨s| - 1` to the query
register, then measure it in the computational basis and read `k`". -/
noncomputable def gK (k : GX) : Matrix GReg GReg ℂ :=
  Matrix.of fun m m' ↦
    if m.2 = m'.2 ∧ m.1 = k then (if m'.1 = k then -1 / 2 else 1 / 2) else 0

theorem sum_conjTranspose_gK_mul_gK : ∑ k, (gK k)ᴴ * gK k = 1 := by
  ext ⟨⟨x₁, x₂⟩, y⟩ ⟨⟨x₁', x₂'⟩, y'⟩
  rcases eq_zero_or_one x₁ with rfl | rfl <;> rcases eq_zero_or_one x₂ with rfl | rfl <;>
    rcases eq_zero_or_one y with rfl | rfl <;> rcases eq_zero_or_one x₁' with rfl | rfl <;>
    rcases eq_zero_or_one x₂' with rfl | rfl <;> rcases eq_zero_or_one y' with rfl | rfl <;>
    norm_num [Fin.sum_univ_two, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, gK,
      Matrix.sum_apply, map_ofNat]

/-- Grover's algorithm for four items as a one-query circuit: start in `|+⟩|+⟩|-⟩`, query once,
apply the diffusion and measure the query register. -/
noncomputable def grover : QuantumComb GReg GX 1 where
  init := groverInit
  step _ := SubInstrument.pure ()
  lossless_step _ := DSubInstrument.lossless_ret (fun _ : Unit ↦ GReg) ()
  final := DSubInstrument.ofKraus gK sum_conjTranspose_gK_mul_gK
  lossless_final := DSubInstrument.lossless_ofKraus _ _

/-- After the query to the oracle marking `w`, the final measurement reads `w` with weight
one. -/
theorem trace_conj_gK (w k : GX) :
    (MatrixMap.conj (gK k)
      (MatrixMap.conj (oracleUnitary (mark w))
        ((1 / 2 : ℂ) • vecMulVec gamp (star gamp)))).trace = if k = w then 1 else 0 := by
  have h : MatrixMap.conj (oracleUnitary (mark w)) (vecMulVec gamp (star gamp)) =
      vecMulVec (fun m ↦ gamp ((oracleEquiv (mark w)).symm m))
        (star fun m ↦ gamp ((oracleEquiv (mark w)).symm m)) := by
    rw [oracleUnitary, conj_basisMatrix_equiv]
    rfl
  rw [map_smul, map_smul, Matrix.trace_smul, h, trace_conj_vecMulVec]
  obtain ⟨w₁, w₂⟩ := w
  obtain ⟨k₁, k₂⟩ := k
  rcases eq_zero_or_one w₁ with rfl | rfl <;> rcases eq_zero_or_one w₂ with rfl | rfl <;>
    rcases eq_zero_or_one k₁ with rfl | rfl <;> rcases eq_zero_or_one k₂ with rfl | rfl <;>
    norm_num [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, gK, gamp, sgn,
      oracleEquiv_symm_apply, mark, map_ofNat]

/-- The final measurement on the state after the query reports the marked item with certainty. -/
theorem outcomeMeasure_final_grover (w : GX) :
    grover.final.outcomeMeasure ((oracleQuery (mark w)).post groverInit ()) =
      Measure.dirac w := by
  have h : ∀ k, (grover.final.branch k ((oracleQuery (mark w)).post groverInit ()).matrix).trace =
      if k = w then 1 else 0 := fun k ↦ by
    have h₁ : ((oracleQuery (mark w)).post groverInit ()).matrix =
        MatrixMap.conj (oracleUnitary (mark w)) ((1 / 2 : ℂ) • vecMulVec gamp (star gamp)) := by
      simp [MatrixMap.conj_apply, groverInit]
    rw [h₁]
    change ((DSubInstrument.ofKraus gK sum_conjTranspose_gK_mul_gK).branch k _).trace = _
    rw [DSubInstrument.branch_ofKraus_apply]
    exact trace_conj_gK w k
  rw [DSubInstrument.outcomeMeasure_eq_sum_univ]
  simp only [h]
  rw [Finset.sum_eq_single w (fun k _ hk ↦ by simp [hk]) (fun hw ↦ absurd (Finset.mem_univ _) hw)]
  simp

/-- Grover's algorithm as a query program in the model of `PQ/QROM`: the program of the circuit
`grover`, whose call goes to the whole register (trivial remainder). -/
noncomputable def groverComp : QComp (qromSpec GX (Fin 2)) (QReg.of GReg) (QReg.of GReg) GX :=
  grover.toComp () (QReg.of Unit) (Equiv.prodPUnit GReg).symm (Equiv.prodPUnit GReg)

/-- Grover's program makes ONE oracle call. -/
theorem queryBounded_grover : QueryBounded groverComp 1 :=
  queryBounded_comb grover (QReg.of Unit) (Equiv.prodPUnit GReg).symm (Equiv.prodPUnit GReg)

/-- Grover's program is lossless. -/
theorem lossless_grover : groverComp.Lossless .instruments :=
  grover.lossless_toComp (spec := qromSpec GX (Fin 2)) () _ _ _

/-- The input state `|+⟩|+⟩|-⟩` is normalized. -/
theorem trace_groverInit : groverInit.matrix.trace = 1 := by
  norm_num [groverInit, Matrix.trace, vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    gamp, sgn]

/-- **Grover's algorithm on four items.**  For every position `w` of the single marked item,
Grover's program (one oracle call, `queryBounded_grover`), run from `|+⟩|+⟩|-⟩` against the
oracle unitary of `mark w`, outputs `w` with probability one. -/
theorem qprob_grover (w : GX) :
    qprob .instruments (mark w) groverComp groverInit
        (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of GReg) GX).symm p = w) = 1 := by
  have h := (evalDist₂_comb_one grover (fun _ ↦ rfl) (mark w)).trans
    (outcomeMeasure_final_grover w)
  have h' := qprob_eq_evalDist₂ .instruments (mark w) groverComp groverInit (fun a ↦ a = w)
    (measurableSet_singleton w)
  refine h'.trans ((congrArg (fun μ : Measure GX ↦ μ {a | a = w}) h).trans ?_)
  simp

/-- Stated for an arbitrary oracle with exactly one marked item. -/
theorem qprob_grover_of_unique (H : GX → Fin 2) (w : GX) (hw : ∀ x, H x = 1 ↔ x = w) :
    qprob .instruments H groverComp groverInit
        (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of GReg) GX).symm p = w) = 1 := by
  have hH : H = mark w := funext fun x ↦ by
    unfold mark
    split_ifs with h
    · exact (hw x).2 h
    · rcases eq_zero_or_one (H x) with h0 | h1
      · exact h0
      · exact absurd ((hw x).1 h1) h
  rw [hH]
  exact qprob_grover w

/-- The average over a uniform marked position. -/
theorem qprob_grover_avg :
    ∑ w : GX, (Fintype.card GX : ℝ≥0∞)⁻¹ *
        qprob .instruments (mark w) groverComp groverInit
          (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of GReg) GX).symm p = w) = 1 := by
  rw [Finset.sum_congr rfl fun w _ ↦ congrArg _ (qprob_grover w)]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact natCast_mul_inv_cancel Fintype.card_ne_zero

end grover

/-! ## Classical one-query search on four items -/

section classicalSearch

/-- A deterministic classical one-query search strategy: query the item `a`, output `g (H a)`. -/
def classicalSearch (a : GX) (g : Fin 2 → GX) : OracleComp (GX →ₒ Fin 2) GX := do
  let z ← liftM ((GX →ₒ Fin 2).query a)
  pure (g z)

theorem isTotalQueryBound_classicalSearch (a : GX) (g : Fin 2 → GX) :
    OracleComp.IsTotalQueryBound (classicalSearch a g) 1 := by
  rw [classicalSearch, OracleComp.isTotalQueryBound_query_bind_iff]
  exact ⟨Nat.one_pos, fun _ ↦ trivial⟩

/-- Its program makes one oracle call. -/
theorem queryBounded_classicalSearch (a : GX) (g : Fin 2 → GX) :
    QueryBounded (classicalSearch a g).toQuantum 1 :=
  OracleComp.isQueryBound_toQuantum (isTotalQueryBound_classicalSearch a g)

/-- Every deterministic classical one-query strategy finds the marked item for at most two of
the four positions. -/
theorem classical_search_card_le (a : GX) (g : Fin 2 → GX) :
    (Finset.univ.filter fun w : GX ↦ g (mark w a) = w).card ≤ 2 := by
  have h : (Finset.univ.filter fun w : GX ↦ g (mark w a) = w) ⊆ {g 0, g 1} := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases eq_zero_or_one (mark w a) with h0 | h1
    · exact Or.inl (hw.2.symm.trans (congrArg g h0))
    · exact Or.inr (hw.2.symm.trans (congrArg g h1))
  exact (Finset.card_le_card h).trans Finset.card_le_two

/-- The bound `2` is attained: query `(0, 0)`, answer `(0, 0)` if it is marked and `(0, 1)`
otherwise. -/
theorem classical_search_card_eq :
    (Finset.univ.filter fun w : GX ↦
      (fun z : Fin 2 ↦ if z = 1 then ((0, 0) : GX) else (0, 1)) (mark w (0, 0)) = w).card = 2 := by
  decide

/-- Against the oracle marking `w`, the program of a classical one-query strategy outputs `w`
with probability `1` or `0` according to whether `g (mark w a) = w`. -/
theorem qprob_classicalSearch (a : GX) (g : Fin 2 → GX) (w : GX) :
    qprob .instruments (mark w) (classicalSearch a g).toQuantum (SubState.basis ())
        (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) GX).symm p = w) =
      if g (mark w a) = w then 1 else 0 :=
  qprob_toQuantum (mark w) (classicalSearch a g) fun b ↦ b = w

theorem two_mul_inv_four : (2 : ℝ≥0∞) * 4⁻¹ = 1 / 2 := by
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_one]
  norm_num

/-- **Classical one-query search.**  Every deterministic classical one-query strategy, embedded
as a quantum program, finds the single marked item among four with probability at most `1/2`
over a uniform marked position; Grover's program achieves `1` (`qprob_grover_avg`). -/
theorem qprob_classical_search_le (a : GX) (g : Fin 2 → GX) :
    ∑ w : GX, (Fintype.card GX : ℝ≥0∞)⁻¹ *
        qprob .instruments (mark w) (classicalSearch a g).toQuantum (SubState.basis ())
          (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) GX).symm p = w) ≤ 1 / 2 := by
  have h : ∀ w : GX, (Fintype.card GX : ℝ≥0∞)⁻¹ *
      qprob .instruments (mark w) (classicalSearch a g).toQuantum (SubState.basis ())
        (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) GX).symm p = w) =
      if g (mark w a) = w then (Fintype.card GX : ℝ≥0∞)⁻¹ else 0 := fun w ↦ by
    refine (congrArg _ (qprob_classicalSearch a g w)).trans ?_
    split_ifs <;> simp
  have hc : (Fintype.card GX : ℝ≥0∞) = 4 := by simp
  rw [Finset.sum_congr rfl fun w _ ↦ h w, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hc,
    ← two_mul_inv_four]
  gcongr
  exact_mod_cast classical_search_card_le a g

/-- **Randomised classical one-query search.**  Every mixture, with weights `p i` of total mass
at most one over an arbitrary finite index type, of deterministic classical one-query strategies
finds the marked item with probability at most `1/2`. -/
theorem qprob_classical_search_mixture_le {ι : Type*} [Fintype ι] (p : ι → ℝ≥0∞)
    (hp : ∑ i, p i ≤ 1) (a : ι → GX) (g : ι → Fin 2 → GX) :
    ∑ i, p i * ∑ w : GX, (Fintype.card GX : ℝ≥0∞)⁻¹ *
        qprob .instruments (mark w) (classicalSearch (a i) (g i)).toQuantum (SubState.basis ())
          (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) GX).symm p = w) ≤ 1 / 2 :=
  calc _ ≤ ∑ i, p i * (1 / 2) :=
        Finset.sum_le_sum fun i _ ↦ by
          gcongr
          exact qprob_classical_search_le (a i) (g i)
    _ = (∑ i, p i) * (1 / 2) := (Finset.sum_mul ..).symm
    _ ≤ 1 * (1 / 2) := by gcongr
    _ = 1 / 2 := one_mul _

end classicalSearch

/-! ## Randomised classical strategies for the parity -/

section parityMixture

/-- **Randomised classical one-query strategies do not compute the parity.**  Every mixture,
with probability weights `p i` over an arbitrary finite index type, of deterministic classical
one-query strategies `(a i, g i)` outputs `H 0 + H 1` with probability exactly `1/2` over a
uniform `H : Fin 2 → Fin 2`. -/
theorem classical_parity_mixture {ι : Type*} [Fintype ι] (p : ι → ℝ≥0∞) (hp : ∑ i, p i = 1)
    (a : ι → Fin 2) (g : ι → Fin 2 → Fin 2) :
    ∑ i, p i * ∑ H : Fin 2 → Fin 2, (Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹ *
        qprob .instruments H (classicalOneQuery (a i) (g i)).toQuantum (SubState.basis ())
          (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) (Fin 2)).symm p = H 0 + H 1) =
      1 / 2 := by
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg _ (qprob_classical_oneQuery_parity (a i) (g i)),
    ← Finset.sum_mul, hp, one_mul]

end parityMixture

/-! ## Randomised classical algorithms inside the model: uniform private coins -/

section coin

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- **A randomised classical algorithm as a query program.**  Flip a uniform private coin
`i : Ω` (the local instrument `SubInstrument.uniform Ω`, the measurement of a fresh uniform
register), then run the program of the classical algorithm `oa i`. -/
noncomputable def coinMix {Ω α : Type} [Fintype Ω] [Nonempty Ω] (oa : Ω → OracleComp (X →ₒ Y) α) :
    QComp (qromSpec X Y) (QReg.of Unit) (QReg.of Unit) α :=
  (QComp.act (SubInstrument.uniform Ω Unit)).bind fun i ↦ (oa i).toQuantum

/-- The coin makes no oracle call: the budget of `coinMix` is that of its branches. -/
theorem queryBounded_coinMix {Ω α : Type} [Fintype Ω] [Nonempty Ω]
    (oa : Ω → OracleComp (X →ₒ Y) α) (q : ℕ) (hq : ∀ i, OracleComp.IsTotalQueryBound (oa i) q) :
    QueryBounded (coinMix oa) q :=
  (QComp.isQueryBound_act_bind_iff _ _ _).2 fun i ↦ OracleComp.isQueryBound_toQuantum (hq i)

/-- An instrument on the trivial registers that reports `e` with weight one on the basis state
reports `e` with weight `c` on the scaled basis state `c |()⟩⟨()|`. -/
theorem outcomeMeasure_of_basis_smul {α : Type} [MeasurableSpace α] [DecidableEq α]
    (P : SubInstrument (Unit × Unit) (Unit × Unit) α) (e : α)
    (hP : ∀ b, P.branch b (Matrix.single ((), ()) ((), ()) 1) =
      if e = b then Matrix.single ((), ()) ((), ()) 1 else 0)
    (σ : SubState (Unit × Unit)) (c : ℂ)
    (hσ : σ.matrix = c • Matrix.single ((), ()) ((), ()) 1) :
    P.outcomeMeasure σ = ENNReal.ofReal c.re • Measure.dirac e := by
  have hb : ∀ b, P.branch b σ.matrix =
      if e = b then c • Matrix.single ((), ()) ((), ()) 1 else 0 := fun b ↦ by
    rw [hσ, map_smul, hP]
    split_ifs <;> simp
  ext t ht
  rw [DSubInstrument.outcomeMeasure_apply _ _ ht,
    tsum_eq_single e fun b hb' ↦ by
      rw [hb, ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hb'))]
      simp,
    hb, ite_eq_left_of_eq_true _ _ (eq_self e), smul_apply, Measure.dirac_apply' _ ht]
  simp

/-- The program of a classical algorithm, started from the scaled basis state `c |()⟩⟨()|`,
reports the value of the algorithm with weight `c`. -/
theorem outcomeMeasure_toQuantum_smul {α : Type} [MeasurableSpace α] [DecidableEq α] (H : X → Y)
    (oa : OracleComp (X →ₒ Y) α) (σ : SubState (Unit × Unit)) (c : ℂ)
    (hσ : σ.matrix = c • Matrix.single ((), ()) ((), ()) 1) :
    DSubInstrument.outcomeMeasure (A := Unit × Unit)
        ((additiveOracleRuntime H).run₂ .instruments oa.toQuantum) σ =
      ENNReal.ofReal c.re • Measure.dirac (evalWithAnswerFn (QueryImpl.ofFn H) oa) := by
  exact outcomeMeasure_of_basis_smul _ _
    (fun b ↦ run_toQuantum_branch_of_basis H (additiveOracleRuntime_step_branch_single H) oa () b)
    σ c hσ

/-- **The coin averages.**  Against a fixed `H`, the probability that `coinMix oa` ends in a
value satisfying `E` is the uniform average, over the coin `i`, of the probability for the
program of `oa i`. -/
theorem qprob_coinMix {Ω α : Type} [Fintype Ω] [Nonempty Ω] (H : X → Y)
    (oa : Ω → OracleComp (X →ₒ Y) α) (E : α → Prop) :
    qprob .instruments H (coinMix oa) (SubState.basis ())
        (fun p ↦ E ((QuantumComp₂.leafEquiv (QReg.of Unit) α).symm p)) =
      ∑ i, (Fintype.card Ω : ℝ≥0∞)⁻¹ *
        qprob .instruments H (oa i).toQuantum (SubState.basis ())
          (fun p ↦ E ((QuantumComp₂.leafEquiv (QReg.of Unit) α).symm p)) := by
  classical
  let : MeasurableSpace α := ⊤
  have hpost : ∀ i : Ω, (((SubInstrument.uniform Ω Unit).frame Unit).post
      ((SubState.basis ()).prod (SubState.basis ())) i).matrix =
        ((Fintype.card Ω : ℂ)⁻¹) • Matrix.single ((), ()) ((), ()) 1 := fun i ↦ by
    rw [DSubInstrument.matrix_post, DSubInstrument.branch_frame_apply]
    ext x x'
    simp [SubInstrument.branch_uniform_apply, MatrixMap.amplify_apply, SubState.matrix_basis]
  have hrun : (additiveOracleRuntime H).evalDist₂ .instruments (coinMix oa) (SubState.basis ()) =
      Measure.sum fun i : Ω ↦ ENNReal.ofReal ((Fintype.card Ω : ℂ)⁻¹).re •
        Measure.dirac (evalWithAnswerFn (QueryImpl.ofFn H) (oa i)) := by
    have h1 := (additiveOracleRuntime H).run₂_act_bind (A := QReg.of Unit) (B := QReg.of Unit)
      (SubInstrument.uniform Ω Unit) fun i ↦ (oa i).toQuantum
    have h2 := DSubInstrument.outcomeMeasure_bind ((SubInstrument.uniform Ω Unit).frame Unit)
      (fun i ↦ (additiveOracleRuntime H).run₂ .instruments (oa i).toQuantum)
      ((SubState.basis ()).prod (SubState.basis ()))
    refine (congrArg (fun p : SubInstrument (Unit × Unit) (Unit × Unit) α ↦
      p.outcomeMeasure ((SubState.basis ()).prod (SubState.basis ()))) h1).trans (h2.trans ?_)
    exact congrArg Measure.sum (funext fun i ↦ outcomeMeasure_toQuantum_smul H (oa i) _ _ (hpost i))
  have hc : ENNReal.ofReal ((Fintype.card Ω : ℂ)⁻¹).re = (Fintype.card Ω : ℝ≥0∞)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re,
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast]
  refine (qprob_eq_evalDist₂ .instruments H (coinMix oa) (SubState.basis ()) E
    MeasurableSpace.measurableSet_top).trans ?_
  rw [hrun, Measure.sum_apply _ MeasurableSpace.measurableSet_top, tsum_fintype, hc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_apply, smul_eq_mul]
  refine congrArg _ ?_
  rw [Measure.dirac_apply' _ MeasurableSpace.measurableSet_top]
  exact ((qprob_toQuantum H (oa i) E).trans (by
    by_cases h : E (evalWithAnswerFn (QueryImpl.ofFn H) (oa i)) <;> simp [h])).symm

/-- Averaging a coin mixture over a finite weighted family of oracles: the value is the uniform
average over the coin of the values of the branches. -/
theorem sum_qprob_coinMix {Ω α κ : Type} [Fintype Ω] [Nonempty Ω] [Fintype κ]
    (c : ℝ≥0∞) (Hs : κ → X → Y) (oa : Ω → OracleComp (X →ₒ Y) α) (E : κ → α → Prop) :
    ∑ j, c * qprob .instruments (Hs j) (coinMix oa) (SubState.basis ())
        (fun p ↦ E j ((QuantumComp₂.leafEquiv (QReg.of Unit) α).symm p)) =
      ∑ i, (Fintype.card Ω : ℝ≥0∞)⁻¹ *
        ∑ j, c * qprob .instruments (Hs j) (oa i).toQuantum (SubState.basis ())
          (fun p ↦ E j ((QuantumComp₂.leafEquiv (QReg.of Unit) α).symm p)) := by
  rw [Finset.sum_congr rfl fun j _ ↦ congrArg _ (qprob_coinMix (Hs j) oa (E j))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _

end coin

/-! ## Randomised classical one-query programs: parity and search -/

section coinGames

/-- **Randomised classical one-query programs do not compute the parity.**  A program that flips
a uniform private coin `i : Ω` and then runs the deterministic classical one-query strategy
`(a i, g i)` (one oracle call, `queryBounded_coin_classical_parity`) outputs `H 0 + H 1` with
probability exactly `1/2` over a uniform `H : Fin 2 → Fin 2`. -/
theorem qprob_coin_classical_parity {Ω : Type} [Fintype Ω] [Nonempty Ω] (a : Ω → Fin 2)
    (g : Ω → Fin 2 → Fin 2) :
    ∑ H : Fin 2 → Fin 2, (Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹ *
        qprob .instruments H (coinMix fun i ↦ classicalOneQuery (a i) (g i)) (SubState.basis ())
          (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) (Fin 2)).symm p = H 0 + H 1) =
      1 / 2 := by
  have h := sum_qprob_coinMix (Ω := Ω) (Fintype.card (Fin 2 → Fin 2) : ℝ≥0∞)⁻¹
    (fun H : Fin 2 → Fin 2 ↦ H) (fun i ↦ classicalOneQuery (a i) (g i))
    (fun H b ↦ b = H 0 + H 1)
  refine h.trans ?_
  rw [Finset.sum_congr rfl fun i _ ↦ congrArg _ (qprob_classical_oneQuery_parity (a i) (g i)),
    ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    natCast_mul_inv_cancel Fintype.card_ne_zero, one_mul]

theorem queryBounded_coin_classical_parity {Ω : Type} [Fintype Ω] [Nonempty Ω] (a : Ω → Fin 2)
    (g : Ω → Fin 2 → Fin 2) :
    QueryBounded (coinMix fun i ↦ classicalOneQuery (a i) (g i)) 1 :=
  queryBounded_coinMix _ 1 fun i ↦ isTotalQueryBound_classicalOneQuery (a i) (g i)

/-- **Randomised classical one-query search.**  A program that flips a uniform private coin
`i : Ω` and then runs the deterministic classical one-query search strategy `(a i, g i)` finds
the single marked item among four with probability at most `1/2` over a uniform marked
position. -/
theorem qprob_coin_classical_search_le {Ω : Type} [Fintype Ω] [Nonempty Ω] (a : Ω → GX)
    (g : Ω → Fin 2 → GX) :
    ∑ w : GX, (Fintype.card GX : ℝ≥0∞)⁻¹ *
        qprob .instruments (mark w) (coinMix fun i ↦ classicalSearch (a i) (g i))
          (SubState.basis ())
          (fun p ↦ (QuantumComp₂.leafEquiv (QReg.of Unit) GX).symm p = w) ≤ 1 / 2 := by
  have h := sum_qprob_coinMix (Ω := Ω) (Fintype.card GX : ℝ≥0∞)⁻¹ mark
    (fun i ↦ classicalSearch (a i) (g i)) (fun w b ↦ b = w)
  refine h.le.trans ?_
  calc _ ≤ ∑ _i : Ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (1 / 2) :=
        Finset.sum_le_sum fun i _ ↦ by
          gcongr
          exact qprob_classical_search_le (a i) (g i)
    _ = 1 / 2 := by
        rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          natCast_mul_inv_cancel Fintype.card_ne_zero, one_mul]

theorem queryBounded_coin_classical_search {Ω : Type} [Fintype Ω] [Nonempty Ω] (a : Ω → GX)
    (g : Ω → Fin 2 → GX) :
    QueryBounded (coinMix fun i ↦ classicalSearch (a i) (g i)) 1 :=
  queryBounded_coinMix _ 1 fun i ↦ isTotalQueryBound_classicalSearch (a i) (g i)

end coinGames

/-! ## Grover against the proven search bound -/

section bound

/-- A uniformly placed single marked item among four is `1/4`-hidden from the trivial view. -/
theorem hidden_mark :
    Hidden (fun _ : GX ↦ (Fintype.card GX : ℝ≥0∞)⁻¹) (fun _ : GX ↦ ()) (fun w : GX ↦ {w})
      (Fintype.card GX : ℝ≥0∞)⁻¹ := by
  intro k φ
  simp only [Finset.mem_singleton, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc (Fintype.card GX : ℝ≥0∞), natCast_mul_inv_cancel Fintype.card_ne_zero, one_mul]

/-- The `HybridModel` of Grover's program. -/
noncomputable def groverModel : HybridModel GX (Fin 2) GX 1 :=
  HybridModel.ofProgram .instruments groverComp groverInit 1 queryBounded_grover
    (QuantumComp₂.leafEquiv (QReg.of GReg) GX).symm

/-- The search experiment of `Hidden.search_le` (uniform single marked item among four, the
algorithm sees nothing but its oracle) has value exactly `1` for Grover's one-query program. -/
theorem search_game_grover :
    ∑ w : GX, (Fintype.card GX : ℝ≥0∞)⁻¹ *
        groverModel.prob (mark w) (fun p ↦ id p ∈ ({w} : Finset GX)) = 1 := by
  have h : ∀ w : GX, groverModel.prob (mark w) (fun p ↦ id p ∈ ({w} : Finset GX)) = 1 :=
    fun w ↦ by
      simp only [Finset.mem_singleton, id]
      exact qprob_grover w
  rw [Finset.sum_congr rfl fun w _ ↦ congrArg _ (h w)]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact natCast_mul_inv_cancel Fintype.card_ne_zero

/-- **Grover against the proven bound.**  `Hidden.search_le`, instantiated at this experiment
(`q = 1`, `ε = 1/4`), gives the bound `(2·1+1)² · 1/4 = 9/4` for the value that Grover's program
makes equal to `1`: the general bound `(2q+1)² ε` has the right order `q² ε` (a `q`-independent
or linear-in-`q` bound `c · ε` or `c · q · ε` with `c < 4` would be false at `q = 1`), and its
constant is within a factor `9/4` of optimal at `q = 1`, `ε = 1/4`. -/
example : (1 : ℝ≥0∞) ≤ (2 * ((1 : ℕ) : ℝ≥0∞) + 1) ^ 2 * (Fintype.card GX : ℝ≥0∞)⁻¹ := by
  refine search_game_grover.symm.le.trans ?_
  exact hidden_mark.search_le
    (by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact (natCast_mul_inv_cancel Fintype.card_ne_zero).le)
    (fun _ ↦ groverModel) mark (fun _ _ ↦ 0)
    (fun w k hk ↦ by
      rw [Finset.mem_singleton]
      by_contra hne
      exact hk (by simp [mark, hne]))
    (fun _ p ↦ p)

end bound

end PQ.QROM.NonVacuity

#print axioms PQ.QROM.NonVacuity.evalDist₂_comb_one
#print axioms PQ.QROM.NonVacuity.queryBounded_grover
#print axioms PQ.QROM.NonVacuity.lossless_grover
#print axioms PQ.QROM.NonVacuity.trace_groverInit
#print axioms PQ.QROM.NonVacuity.qprob_grover
#print axioms PQ.QROM.NonVacuity.qprob_grover_of_unique
#print axioms PQ.QROM.NonVacuity.qprob_grover_avg
#print axioms PQ.QROM.NonVacuity.classical_search_card_le
#print axioms PQ.QROM.NonVacuity.classical_search_card_eq
#print axioms PQ.QROM.NonVacuity.qprob_classical_search_le
#print axioms PQ.QROM.NonVacuity.qprob_classical_search_mixture_le
#print axioms PQ.QROM.NonVacuity.classical_parity_mixture
#print axioms PQ.QROM.NonVacuity.queryBounded_coinMix
#print axioms PQ.QROM.NonVacuity.qprob_coinMix
#print axioms PQ.QROM.NonVacuity.qprob_coin_classical_parity
#print axioms PQ.QROM.NonVacuity.queryBounded_coin_classical_parity
#print axioms PQ.QROM.NonVacuity.qprob_coin_classical_search_le
#print axioms PQ.QROM.NonVacuity.queryBounded_coin_classical_search
#print axioms PQ.QROM.NonVacuity.hidden_mark
#print axioms PQ.QROM.NonVacuity.search_game_grover
