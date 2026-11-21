import PQ.QROM.TwoPhaseAdv
import PolyFun.IPFunctor.Free.Lens
import VCVio.Quantum.Oracle.Emulated

/-!
# Multi-phase QROM experiments: the `P`-port hash oracle and phase-retargeted adversaries

This file generalises the two-port material of `PQ/QROM/TwoPhase.lean` to an arbitrary type `P`
of ports, and provides the *phase discipline* used by the adaptive games
(`PQ/QROM/MultiPhaseGame.lean`, `PQ/QROM/ExactItsr.lean`).

* `qromNSpec P X Y`, `nRuntime G`: the hash oracle with one port per `p : P`, all on the register
  `X × Y`; `nRuntime G` answers port `p` with the oracle unitary of `G p : X → Y`.  The ports only
  name the *phase* of a call: the real games answer every port with the same function.
* `nRuntime_sqrt_le_kraus`, `nRuntime_sqrt_le_kraus'`: the square-root hybrid bound between two
  `P`-port runtimes; `tsum_rpow_queryWeightN_le`: the Kraus weights of the change, for a program
  making at most `q` calls IN TOTAL (over all ports) on every path, by `4 q` times the index
  masses of one run on the pairs (port, input) where the two families differ (`diffMass`);
  `tsum_massN_le`: all masses add up to at most `q` times the trace.
* `retarget p x`: the single-port program `x` (over `qromSpec X Y`) with every call sent to port
  `p`.
* `IAdv.pflat ch n s x`: the *port-agnostic* interactive adversary `x` (an `IAdv` over the
  single-port signature `qromSpec X Y`) run against the deterministic challenger `ch`, where the
  segment executed while the challenger is in state `t` is retargeted to port `t`: **ports are
  challenger states**.  The adversary is syntactically unable to call the port of any other
  phase; in particular it cannot use "the oracle of a later phase" early.
* `pflat_isTotalBound`: total query budgets transfer from the single-port flattening
  `IAdv.flat` to `IAdv.pflat`.
* Locality: `pflat_branch_eq_zero`, `pflat_branch_congr` (the post-state of a leaf with recorded
  challenger state `t` only depends on the port functions of the states from which `t` is
  reachable), `pflat_queryWeight_eq_zero`, `pflat_queryWeight_congr` (the weights of the calls of
  the ports from which `t` is reachable depend neither on the other ports nor on what the
  challenger answers once `t` is unreachable).
-/

open MeasureTheory ENNReal Quantum Matrix IPFunctor
open scoped Kronecker ComplexOrder

universe u v w w₂ w₃

namespace PQ.QROM

/-! ## Total call budgets

(The same notion as `Quantum.QuantumComp.IsTotalQueryBound` of
`VCVio/Quantum/Comp/TotalQueryBound.lean`, restated here because that module is not among the
built dependencies of this project.) -/

section Total

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{0, 0}} {W : QReg → Type w}
  {W₂ : QReg → Type w₂} {A : QReg}

/-- The charge of a command: one for a call and zero for a local operation. -/
def cmdCharge : {A : QReg} → QuantumComp.Cmd L spec A → ℕ
  | _, .prim _ => 0
  | _, .query _ _ _ => 1

/-- Every path makes at most `n` oracle calls in total (over all ports). -/
def IsTotalBound (x : QuantumComp L spec W A) (n : ℕ) : Prop :=
  IFreeM.IsChargeBound x (fun _ c ↦ cmdCharge c) n

theorem isTotalBound_pure (a : W A) (n : ℕ) :
    IsTotalBound (QuantumComp.pure a : QuantumComp L spec W A) n :=
  IFreeM.isChargeBound_pure a n

theorem isTotalBound_primBind_iff (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec W (L.next o b)) (n : ℕ) :
    IsTotalBound (QuantumComp.primBind o k) n ↔ ∀ b, IsTotalBound (k b) n := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := QuantumComp.toIPFunctor L spec)
    (c := fun _ c ↦ cmdCharge c) (.prim o) (QuantumComp.onDown k) n).trans ?_
  simp only [cmdCharge, Nat.zero_le, Nat.sub_zero, true_and]
  exact ULift.forall

theorem isTotalBound_queryBind_iff (i : spec.Port) (B : QReg) (e : A ≃ spec.In i × B)
    (k : spec.Result i → QuantumComp L spec W (QReg.of (spec.Out i × B))) (n : ℕ) :
    IsTotalBound (QuantumComp.queryBind i B e k) n ↔
      0 < n ∧ ∀ r, IsTotalBound (k r) (n - 1) := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := QuantumComp.toIPFunctor L spec)
    (c := fun _ c ↦ cmdCharge c) (.query i B e) (QuantumComp.onDown k) n).trans ?_
  exact and_congr Nat.succ_le_iff ULift.forall

/-- On a single port, the per-port and total budgets coincide. -/
theorem isTotalBound_iff_isQueryBound [Unique spec.Port] (x : QuantumComp L spec W A) (n : ℕ) :
    IsTotalBound x n ↔ x.IsQueryBound (fun _ ↦ n) := by
  have h : ∀ (i : spec.Port), IsTotalBound x n ↔ x.IsQueryBoundAt i n := by
    intro i
    induction x using QuantumComp.inductionOn generalizing n with
    | pure _ _ => exact ⟨fun _ ↦ QuantumComp.isQueryBoundAt_pure _ _ _, fun _ ↦ isTotalBound_pure _ _⟩
    | primBind _ o k ih =>
      rw [isTotalBound_primBind_iff, QuantumComp.isQueryBoundAt_primBind_iff]
      exact forall_congr' fun b ↦ ih b n
    | queryBind _ j B e k ih =>
      rw [isTotalBound_queryBind_iff, QuantumComp.isQueryBoundAt_queryBind_iff]
      simp only [Subsingleton.elim j i, true_implies, ne_self_iff_false, false_implies, and_true]
      exact and_congr Iff.rfl (forall_congr' fun r ↦ ih r (n - 1))
  exact ⟨fun hx i ↦ (h i).mp hx, fun hx ↦ (h default).mpr (hx default)⟩

variable (R : QuantumRuntime spec) (I : L.Interp)
  {wt : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}

/-- No query weight occurs at or beyond the total call budget. -/
theorem queryWeight_eq_zero_of_isTotalBound {x : QuantumComp L spec W A} {n j : ℕ}
    (hx : IsTotalBound x n) (hj : n ≤ j) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.queryWeight I wt x ρ j = 0 := by
  induction x using QuantumComp.inductionOn generalizing n j with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [isTotalBound_primBind_iff] at hx
    rw [QuantumRuntime.queryWeight_primBind]
    exact tsum_eq_zero_iff.mpr fun b ↦ ih b (hx b) hj _
  | queryBind _ i B e k ih =>
    rw [isTotalBound_queryBind_iff] at hx
    cases j with
    | zero => have := hx.1; omega
    | succ j =>
      rw [QuantumRuntime.queryWeight_queryBind_succ]
      exact tsum_eq_zero_iff.mpr fun r ↦ ih r (hx.2 r) (by omega) _

/-- The total mass, summed over every port, is bounded by total calls times input trace. -/
theorem tsum_queryMass_le_of_isTotalBound
    {x : QuantumComp L spec W A} {n : ℕ} (hx : IsTotalBound x n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    ∑' i, R.queryMass I x ρ i ≤ n * ENNReal.ofReal ρ.trace.re := by
  classical
  simp only [QuantumRuntime.queryMass]
  rw [tsum_comm]
  rw [tsum_eq_sum (s := Finset.range n) (fun j hj ↦ ?_)]
  · calc
      _ ≤ ∑ _j ∈ Finset.range n, ENNReal.ofReal ρ.trace.re :=
        Finset.sum_le_sum fun j _ ↦ R.tsum_queryMassAt_le I x hρ j
      _ = _ := by simp
  · exact tsum_eq_zero_iff.mpr fun i ↦
      queryWeight_eq_zero_of_isTotalBound R I hx (by simpa using hj) ρ

/-- **Cauchy–Schwarz over the calls, total budget.**  For a program making at most `q` calls in
total on every path. -/
theorem tsum_rpow_queryWeight_le_of_total
    {x : QuantumComp L spec W A} {q : ℕ} (hx : IsTotalBound x q)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    ∑' j, R.queryWeight I wt x ρ j ^ (2⁻¹ : ℝ) ≤
      ((q : ℝ≥0∞) * ∑' j, R.queryWeight I wt x ρ j) ^ (2⁻¹ : ℝ) := by
  have hz : ∀ j ∉ Finset.range q, R.queryWeight I wt x ρ j ^ (2⁻¹ : ℝ) = 0 :=
    fun j hj ↦ by
      rw [queryWeight_eq_zero_of_isTotalBound R I hx (by simpa using hj) ρ,
        ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hz, ENNReal.le_rpow_inv_iff (by norm_num)]
  calc (∑ j ∈ Finset.range q, R.queryWeight I wt x ρ j ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)
      ≤ ((Finset.range q).card : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
          ∑ j ∈ Finset.range q, (R.queryWeight I wt x ρ j ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ (by norm_num)
    _ = (q : ℝ≥0∞) * ∑ j ∈ Finset.range q, R.queryWeight I wt x ρ j := by
        have e : ∀ y : ℝ≥0∞, (y ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = y := fun y ↦ by
          rw [← ENNReal.rpow_mul]; norm_num
        simp only [Finset.card_range, e]
        norm_num
    _ ≤ _ := by
        gcongr
        exact sum_le_tsum _

end Total

variable {P X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ## The `P`-port hash oracle -/

/-- The signature of a hash oracle with one port for every `p : P`, all on the register `X × Y`
(query input, then response).  The signature names no function. -/
@[reducible]
def qromNSpec (P X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    QuantumOracleSpec.{0, 0} where
  Port := P
  In _ := QReg.of (X × Y)
  Out _ := QReg.of (X × Y)
  Result _ := Unit

/-- The projection `|k⟩⟨k| ⊗ 1_Y` on the register of any port. -/
noncomputable def blockN (P X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (i : (qromNSpec P X Y).Port) (k : X) :
    Matrix ((qromNSpec P X Y).In i) ((qromNSpec P X Y).In i) ℂ :=
  inputBlock X Y () k

theorem isCoherentIndex_blockN :
    Hybrid.IsCoherentIndex (spec := qromNSpec P X Y) (κ := fun _ ↦ X) (blockN P X Y)
      (blockN P X Y) where
  sum_eq_one _ := sum_inputBlock ()
  mul_self _ k := inputBlock_mul_self () k
  conjTranspose_mul_of_ne _ a b hab := by
    unfold blockN
    rw [inputBlock_conjTranspose]
    exact inputBlock_mul_of_ne () hab

theorem sum_conjTranspose_blockN_mul (i : (qromNSpec P X Y).Port) :
    ∑ k, (blockN P X Y i k)ᴴ * blockN P X Y i k = 1 :=
  sum_conjTranspose_inputBlock_mul ()

variable [AddCommGroup Y]

/-- The runtime answering port `p` with the oracle unitary of `G p`, with no private memory. -/
@[reducible]
noncomputable def nRuntime (G : P → X → Y) : QuantumRuntime (qromNSpec P X Y) where
  D := QReg.of Unit
  init := SubState.basis ()
  step p := (oracleQuery (G p)).frame Unit

/-- The Kraus operator of the step of `nRuntime G` on port `i`. -/
noncomputable def stepOpN (G : P → X → Y) (i : (qromNSpec P X Y).Port)
    (_ : (qromNSpec P X Y).Result i) :
    Matrix ((qromNSpec P X Y).Out i × Unit) ((qromNSpec P X Y).In i × Unit) ℂ :=
  stepOp (G i) () ()

theorem stepN_branch_eq (G : P → X → Y) (i : (qromNSpec P X Y).Port)
    (r : (qromNSpec P X Y).Result i) :
    ((oracleQuery (G i)).frame Unit).branch r = MatrixMap.conj (stepOpN G i r) :=
  step_branch_eq (G i) () ()

theorem respectsIndex_stepOpN (G : P → X → Y) :
    Hybrid.RespectsIndex (spec := qromNSpec P X Y) (κ := fun _ ↦ X) (blockN P X Y)
      (blockN P X Y) (D := Unit) (stepOpN G) := fun i _ k ↦
  respectsIndex_stepOp (G i) () () k

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- Index mass of the run of `x` against `nRuntime G` from `σ`, on the pair `c = ⟨p, k⟩` of a
port `p` and a query input `k`. -/
noncomputable def massN (I : L.Interp) (G : P → X → Y)
    (x : QuantumComp L (qromNSpec P X Y) W A) (σ : Matrix (A × Unit) (A × Unit) ℂ)
    (c : Σ _ : P, X) : ℝ≥0∞ :=
  (nRuntime G).indexMass I (κ := fun _ ↦ X) (blockN P X Y) x σ c

/-- All masses (all ports, all inputs) add up to at most the total number of calls times the
trace. -/
theorem tsum_massN_le (I : L.Interp) (G : P → X → Y)
    {x : QuantumComp L (qromNSpec P X Y) W A} {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) {q : ℕ} (hx : IsTotalBound x q) :
    ∑' c, massN I G x σ c ≤ q * ENNReal.ofReal σ.trace.re := by
  refine le_trans (le_of_eq (tsum_sigma (β := fun _ : P ↦ X)
    fun p k ↦ massN I G x σ ⟨p, k⟩)) ?_
  have h : ∀ p : P, ∑' k : X, massN I G x σ ⟨p, k⟩ = (nRuntime G).queryMass I x σ p := fun p ↦
    (nRuntime G).tsum_indexMass_eq_queryMass I (κ := fun _ ↦ X) (blockN P X Y) p
      (sum_conjTranspose_blockN_mul p) x hσ
  simp only [h]
  exact tsum_queryMass_le_of_isTotalBound (nRuntime G) I hx hσ

/-- The masses of the run against `G` on the pairs (port, input) where `H` and `G` differ. -/
noncomputable def diffMass (I : L.Interp) (H G : P → X → Y)
    (x : QuantumComp L (qromNSpec P X Y) W A) (σ : Matrix (A × Unit) (A × Unit) ℂ) : ℝ≥0∞ :=
  ∑' c : Σ _ : P, X, if H c.1 c.2 ≠ G c.1 c.2 then massN I G x σ c else 0

section HybridN

open scoped Matrix.Norms.L2Operator
open Classical in
/-- The observable of an event. -/
private noncomputable def obsN {W : QReg → Type w} (E : (Σ u, W u) → Prop) (p : Σ u, W u) :
    Matrix (p.1 × Unit) (p.1 × Unit) ℂ :=
  if E p then 1 else 0

private theorem obsN_posSemidef {W : QReg → Type w} (E : (Σ u, W u) → Prop) (p : Σ u, W u) :
    (1 - (obsN E p)ᴴ * obsN E p).PosSemidef := by
  unfold obsN
  by_cases h : E p <;> simp [h, Matrix.PosSemidef.one, Matrix.PosSemidef.zero]

private theorem leafProb_eq_obsN (I : L.Interp) (G : P → X → Y)
    (x : QuantumComp L (qromNSpec P X Y) W A) (σ : Matrix (A × Unit) (A × Unit) ℂ)
    (E : (Σ u, W u) → Prop) :
    leafProb (nRuntime G) I x σ E = ∑' p, ENNReal.ofReal (MatrixMap.conj (obsN E p)
      (((nRuntime G).run I x).branch p σ)).trace.re := by
  unfold leafProb obsN
  refine tsum_congr fun p ↦ ?_
  by_cases h : E p
  · rw [ind_of_true h, mul_one]; simp [h]
  · rw [ind_of_false h, mul_zero]; simp [h]

/-- **Square-root hybrid bound between `P`-port runtimes**, Kraus-weight form: the weights are
those of the run against `G`. -/
theorem nRuntime_sqrt_le_kraus (I : L.Interp) (H G : P → X → Y)
    (x : QuantumComp L (qromNSpec P X Y) W A) {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) (E : (Σ u, W u) → Prop) :
    leafProb (nRuntime H) I x σ E ^ (2⁻¹ : ℝ) ≤ leafProb (nRuntime G) I x σ E ^ (2⁻¹ : ℝ) +
      ∑' j, (nRuntime G).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ stepOpN G i r - stepOpN H i r) x σ j ^
          (2⁻¹ : ℝ) := by
  rw [leafProb_eq_obsN, leafProb_eq_obsN]
  have h := QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le' I (D := QReg.of Unit)
    (s₀ := fun b ↦ (oracleQuery (G b)).frame Unit) (s₁ := fun b ↦ (oracleQuery (H b)).frame Unit)
    (U := stepOpN G) (W := stepOpN H) (SubState.basis ()) (SubState.basis ())
    (stepN_branch_eq G) (stepN_branch_eq H) x (obsN E) (obsN_posSemidef E) hσ
  exact h

/-- Converse direction, same weights (of the run against `G`). -/
theorem nRuntime_sqrt_le_kraus' (I : L.Interp) (H G : P → X → Y)
    (x : QuantumComp L (qromNSpec P X Y) W A) {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) (E : (Σ u, W u) → Prop) :
    leafProb (nRuntime G) I x σ E ^ (2⁻¹ : ℝ) ≤ leafProb (nRuntime H) I x σ E ^ (2⁻¹ : ℝ) +
      ∑' j, (nRuntime G).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ stepOpN G i r - stepOpN H i r) x σ j ^
          (2⁻¹ : ℝ) := by
  rw [leafProb_eq_obsN, leafProb_eq_obsN]
  have h := QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le I (D := QReg.of Unit)
    (s₀ := fun b ↦ (oracleQuery (G b)).frame Unit) (s₁ := fun b ↦ (oracleQuery (H b)).frame Unit)
    (U := stepOpN G) (W := stepOpN H) (SubState.basis ()) (SubState.basis ())
    (stepN_branch_eq G) (stepN_branch_eq H) x (obsN E) (obsN_posSemidef E) hσ
  exact h

/-- The Kraus weights of the change between two `P`-port runtimes, for a program making at most
`q` calls in total, by the index masses of the run against `G` on the pairs (port, input) where
the functions differ. -/
theorem tsum_rpow_queryWeightN_le (I : L.Interp) (H G : P → X → Y)
    {x : QuantumComp L (qromNSpec P X Y) W A} {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) {q : ℕ} (hx : IsTotalBound x q) :
    ∑' j, (nRuntime G).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ stepOpN G i r - stepOpN H i r) x σ j ^
          (2⁻¹ : ℝ) ≤
      (4 * (q : ℝ≥0∞) * diffMass I H G x σ) ^ (2⁻¹ : ℝ) := by
  refine (tsum_rpow_queryWeight_le_of_total (nRuntime G) I hx σ).trans ?_
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hmass := (nRuntime G).tsum_queryWeight_krausWeight_le_tsum_mul_indexMass I
    isCoherentIndex_blockN ((respectsIndex_stepOpN G).sub (respectsIndex_stepOpN H)) x hσ
  rw [mul_comm 4 _, mul_assoc]
  refine mul_le_mul' le_rfl (hmass.trans ?_)
  unfold diffMass
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun c ↦ ?_
  have hr : ∀ f : (qromNSpec P X Y).Result c.1 → ℝ≥0∞, ∑' r, f r = f () := fun f ↦ by
    rw [tsum_fintype]
    exact Fintype.sum_unique f
  rw [hr]
  refine (mul_le_mul'
    (ofReal_l2_opNorm_sub_mul_inputBlock_le (H c.1) (G c.1) () () c.2) le_rfl).trans ?_
  split_ifs with hk
  · exact le_rfl
  · simp

/-- **Square-root hybrid bound between `P`-port runtimes, mass form**, for a program making at
most `q` calls in total: both directions, masses of the run against `G`. -/
theorem nRuntime_sqrt_le (I : L.Interp) (H G : P → X → Y)
    {x : QuantumComp L (qromNSpec P X Y) W A} {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) {q : ℕ} (hx : IsTotalBound x q) (E : (Σ u, W u) → Prop) :
    leafProb (nRuntime H) I x σ E ^ (2⁻¹ : ℝ) ≤ leafProb (nRuntime G) I x σ E ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * diffMass I H G x σ) ^ (2⁻¹ : ℝ) ∧
      leafProb (nRuntime G) I x σ E ^ (2⁻¹ : ℝ) ≤ leafProb (nRuntime H) I x σ E ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * diffMass I H G x σ) ^ (2⁻¹ : ℝ) :=
  ⟨(nRuntime_sqrt_le_kraus I H G x hσ E).trans
      (add_le_add le_rfl (tsum_rpow_queryWeightN_le I H G hσ hx)),
    (nRuntime_sqrt_le_kraus' I H G x hσ E).trans
      (add_le_add le_rfl (tsum_rpow_queryWeightN_le I H G hσ hx))⟩

end HybridN

/-! ## Retargeting a single-port program -/

omit [AddCommGroup Y] in
/-- The command lens sending every call of the single port to port `p`. -/
def portLens (L : LocalSig.{u, v}) (p : P) :
    Lens (QuantumComp.toIPFunctor L (qromSpec X Y))
      (QuantumComp.toIPFunctor L (qromNSpec P X Y)) where
  toFunA _
    | .prim o => .prim o
    | .query _ B e => .query p B e
  toFunB _ c := by cases c <;> exact id
  src_eq _ c _ := by cases c <;> rfl

/-- The single-port program `x` with every call sent to port `p`. -/
def retarget (p : P) : {A : QReg} → QuantumComp L (qromSpec X Y) W A →
    QuantumComp L (qromNSpec P X Y) W A :=
  fun {_} x ↦ IFreeM.mapLens (portLens L p) x

omit [AddCommGroup Y] in
@[simp]
theorem retarget_pure (p : P) (a : W A) :
    retarget p (QuantumComp.pure a : QuantumComp L (qromSpec X Y) W A) = QuantumComp.pure a :=
  rfl

omit [AddCommGroup Y] in
@[simp]
theorem retarget_primBind (p : P) (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L (qromSpec X Y) W (L.next o b)) :
    retarget p (QuantumComp.primBind o k) =
      QuantumComp.primBind o (fun b ↦ retarget p (k b)) :=
  rfl

omit [AddCommGroup Y] in
@[simp]
theorem retarget_queryBind (p : P) (i : (qromSpec X Y).Port) (B : QReg)
    (e : A ≃ (qromSpec X Y).In i × B)
    (k : (qromSpec X Y).Result i → QuantumComp L (qromSpec X Y) W (QReg.of ((qromSpec X Y).Out i × B))) :
    retarget p (QuantumComp.queryBind i B e k) =
      QuantumComp.queryBind (spec := qromNSpec P X Y) p B e (fun r ↦ retarget p (k r)) :=
  rfl

section RetargetBind

variable {W₂ : QReg → Type w₂} {W₃ : QReg → Type w₃}

omit [AddCommGroup Y] in
/-- Total budgets transfer through a retargeted prefix. -/
theorem isTotalBound_retarget_bind (p : P) (seg : QuantumComp L (qromSpec X Y) W A)
    (k : ∀ u, W u → QuantumComp L (qromSpec X Y) W₂ u)
    (k' : ∀ u, W u → QuantumComp L (qromNSpec P X Y) W₃ u)
    (hk : ∀ u y m, IsTotalBound (k u y) m → IsTotalBound (k' u y) m) (m : ℕ)
    (h : IsTotalBound (seg.bind k) m) : IsTotalBound ((retarget p seg).bind k') m := by
  induction seg using QuantumComp.inductionOn generalizing m with
  | pure _ y => exact hk _ y m h
  | primBind _ o k₀ ih =>
    rw [QuantumComp.primBind_bind, isTotalBound_primBind_iff] at h
    rw [retarget_primBind, QuantumComp.primBind_bind, isTotalBound_primBind_iff]
    exact fun b ↦ ih b m (h b)
  | queryBind _ i B e k₀ ih =>
    rw [QuantumComp.queryBind_bind, isTotalBound_queryBind_iff] at h
    rw [retarget_queryBind, QuantumComp.queryBind_bind,
      isTotalBound_queryBind_iff]
    exact ⟨h.1, fun r ↦ ih r (m - 1) (h.2 r)⟩

variable {D : QReg} {σ₁ σ₂ : SubState D}
  {s₁ s₂ : ∀ i, SubInstrument ((qromNSpec P X Y).In i × D) ((qromNSpec P X Y).Out i × D)
    ((qromNSpec P X Y).Result i)}

omit [AddCommGroup Y] in
/-- The branch of a retargeted prefix followed by continuations, against two runtimes whose
steps agree on the port of the prefix and whose continuations have the same branch. -/
theorem run_retarget_bind_branch_congr (I : L.Interp) (p : P) (hs : s₁ p = s₂ p)
    (seg : QuantumComp L (qromSpec X Y) W A)
    (k k' : ∀ u, W u → QuantumComp L (qromNSpec P X Y) W₂ u) (c : Σ u, W₂ u)
    (h : ∀ u y, ((QuantumRuntime.mk D σ₁ s₁).run I (k u y)).branch c =
      ((QuantumRuntime.mk D σ₂ s₂).run I (k' u y)).branch c) :
    ((QuantumRuntime.mk D σ₁ s₁).run I ((retarget p seg).bind k)).branch c =
      ((QuantumRuntime.mk D σ₂ s₂).run I ((retarget p seg).bind k')).branch c := by
  induction seg using QuantumComp.inductionOn with
  | pure _ y => exact h _ y
  | primBind _ o k₀ ih =>
    refine LinearMap.ext fun ρ ↦ ?_
    rw [retarget_primBind, QuantumComp.primBind_bind, QuantumComp.primBind_bind,
      QuantumRuntime.run_primBind, QuantumRuntime.run_primBind,
      DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply]
    exact tsum_congr fun b ↦ by rw [ih b]
  | queryBind _ i B e k₀ ih =>
    refine LinearMap.ext fun ρ ↦ ?_
    rw [retarget_queryBind, QuantumComp.queryBind_bind, QuantumComp.queryBind_bind,
      QuantumRuntime.run_queryBind, QuantumRuntime.run_queryBind,
      DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply]
    have hstep : (QuantumRuntime.mk D σ₁ s₁).queryStep p B e =
        (QuantumRuntime.mk D σ₂ s₂).queryStep p B e := by
      simp only [QuantumRuntime.queryStep, hs]
    rw [hstep]
    exact tsum_congr fun r ↦ by rw [ih r]

variable {wt : ∀ i, Matrix ((qromNSpec P X Y).In i × D) ((qromNSpec P X Y).In i × D) ℂ → ℝ≥0∞}

omit [AddCommGroup Y] in
/-- The weights of a retargeted prefix followed by continuations, against two runtimes whose
steps agree on the port of the prefix and whose continuations have the same weights. -/
theorem queryWeight_retarget_bind_congr (I : L.Interp) (p : P) (hs : s₁ p = s₂ p)
    (seg : QuantumComp L (qromSpec X Y) W A)
    (k k' : ∀ u, W u → QuantumComp L (qromNSpec P X Y) W₂ u)
    (h : ∀ u y ρ j, (QuantumRuntime.mk D σ₁ s₁).queryWeight I wt (k u y) ρ j =
      (QuantumRuntime.mk D σ₂ s₂).queryWeight I wt (k' u y) ρ j)
    (ρ : Matrix (A × D) (A × D) ℂ) (j : ℕ) :
    (QuantumRuntime.mk D σ₁ s₁).queryWeight I wt ((retarget p seg).bind k) ρ j =
      (QuantumRuntime.mk D σ₂ s₂).queryWeight I wt ((retarget p seg).bind k') ρ j := by
  induction seg using QuantumComp.inductionOn generalizing j with
  | pure _ y => exact h _ y ρ j
  | primBind _ o k₀ ih =>
    rw [retarget_primBind, QuantumComp.primBind_bind, QuantumComp.primBind_bind,
      QuantumRuntime.queryWeight_primBind, QuantumRuntime.queryWeight_primBind]
    exact tsum_congr fun b ↦ ih b _ j
  | queryBind _ i B e k₀ ih =>
    rw [retarget_queryBind, QuantumComp.queryBind_bind, QuantumComp.queryBind_bind]
    cases j with
    | zero =>
      rw [QuantumRuntime.queryWeight_queryBind_zero, QuantumRuntime.queryWeight_queryBind_zero]
    | succ j =>
      rw [QuantumRuntime.queryWeight_queryBind_succ, QuantumRuntime.queryWeight_queryBind_succ]
      have hstep : (QuantumRuntime.mk D σ₁ s₁).queryStep p B e =
          (QuantumRuntime.mk D σ₂ s₂).queryStep p B e := by
        simp only [QuantumRuntime.queryStep, hs]
      rw [hstep]
      exact tsum_congr fun r ↦ ih r _ j

omit [AddCommGroup Y] in
/-- A retargeted prefix on a port without weight, followed by continuations without weight, has
no weight. -/
theorem queryWeight_retarget_bind_eq_zero (I : L.Interp) (R : QuantumRuntime (qromNSpec P X Y))
    {wt : ∀ i, Matrix ((qromNSpec P X Y).In i × R.D) ((qromNSpec P X Y).In i × R.D) ℂ → ℝ≥0∞}
    (p : P) (hp : ∀ σ, wt p σ = 0)
    (seg : QuantumComp L (qromSpec X Y) W A)
    (k : ∀ u, W u → QuantumComp L (qromNSpec P X Y) W₂ u)
    (h : ∀ u y ρ j, R.queryWeight I wt (k u y) ρ j = 0)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I wt ((retarget p seg).bind k) ρ j = 0 := by
  induction seg using QuantumComp.inductionOn generalizing j with
  | pure _ y => exact h _ y ρ j
  | primBind _ o k₀ ih =>
    rw [retarget_primBind, QuantumComp.primBind_bind, QuantumRuntime.queryWeight_primBind]
    exact tsum_eq_zero_iff.mpr fun b ↦ ih b _ j
  | queryBind _ i B e k₀ ih =>
    rw [retarget_queryBind, QuantumComp.queryBind_bind]
    cases j with
    | zero => rw [QuantumRuntime.queryWeight_queryBind_zero]; exact hp _
    | succ j =>
      rw [QuantumRuntime.queryWeight_queryBind_succ]
      exact tsum_eq_zero_iff.mpr fun r ↦ ih r _ j

end RetargetBind

/-! ## Phase-retargeted flattening of interactive adversaries -/

variable {Req Resp St : Type} {Out : QReg → Type w}

namespace IAdv

/-- Run the port-agnostic interactive adversary `x` against the challenger `ch` from the state
`s`, sending the calls of the segment executed in challenger state `t` to port `t`, and stop
with the final output and the final challenger state. -/
def pflat (ch : Req → St → Resp × St) :
    (n : ℕ) → {A : QReg} → St → IAdv L (qromSpec X Y) Req Resp Out n A →
      QuantumComp L (qromNSpec St X Y) (fun u ↦ Out u × St) A
  | 0, _, s, x => QuantumComp.bind (X := Out) (retarget s x) fun _ o ↦ QuantumComp.pure (o, s)
  | n + 1, _, s, x =>
    QuantumComp.bind (X := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L (qromSpec X Y) Req Resp Out n u)))
      (retarget s x) fun _ r ↦ match r with
        | .inl o => QuantumComp.pure (o, s)
        | .inr rc => pflat ch n (ch rc.1 s).2 (rc.2 (ch rc.1 s).1)

omit [AddCommGroup Y] in
/-- Total budgets transfer from the single-port flattening to the phase-retargeted one. -/
theorem pflat_isTotalBound_of (ch : Req → St → Resp × St) (n : ℕ) {A : QReg} (s : St)
    (x : IAdv L (qromSpec X Y) Req Resp Out n A) (m : ℕ)
    (h : IsTotalBound (flat ch (stop (L := L) (spec := qromSpec X Y)) n s x) m) :
    IsTotalBound (pflat ch n s x) m := by
  induction n generalizing A s m with
  | zero =>
    refine isTotalBound_retarget_bind (W := Out) s x _ _ (fun u y m' _ ↦ ?_) m h
    exact isTotalBound_pure _ _
  | succ n ih =>
    refine isTotalBound_retarget_bind
      (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L (qromSpec X Y) Req Resp Out n u))) s x _ _
      (fun u y m' hy ↦ ?_) m h
    cases y with
    | inl o => exact isTotalBound_pure _ _
    | inr rc => exact ih _ _ m' hy

omit [AddCommGroup Y] in
/-- An adversary making at most `q` calls on every path (`IAdv.IsQueryBound` on its single
port), run with phase-retargeted calls, makes at most `q` calls in total on every path. -/
theorem pflat_isTotalBound (ch : Req → St → Resp × St) {n : ℕ} {A : QReg} (s : St)
    {x : IAdv L (qromSpec X Y) Req Resp Out n A} {q : ℕ}
    (hx : IsQueryBound n x (fun _ ↦ q)) : IsTotalBound (pflat ch n s x) q :=
  pflat_isTotalBound_of ch n s x q
    ((isTotalBound_iff_isQueryBound (spec := qromSpec X Y) _ q).2 (hx St ch s))

end IAdv

/-! ## Locality -/

section Locality

variable (I : L.Interp)

omit [AddCommGroup Y] in
/-- A leaf whose recorded challenger state `t` is not reachable from the current state `s` is
not reached. -/
theorem pflat_branch_eq_zero (R : QuantumRuntime (qromNSpec St X Y))
    (ch : Req → St → Resp × St) (ext : St → St → Prop)
    (hrefl : ∀ s, ext s s) (hstep : ∀ req s t, ext (ch req s).2 t → ext s t)
    (n : ℕ) {A : QReg} (s : St) (x : IAdv L (qromSpec X Y) Req Resp Out n A) (u : QReg)
    (o : Out u) (t : St) (h : ¬ ext s t) :
    (R.run I (IAdv.pflat ch n s x)).branch ⟨u, (o, t)⟩ = 0 := by
  induction n generalizing A s with
  | zero =>
    refine run_bind_branch_eq_zero R I (W := Out) (retarget s x) _ _ fun p ↦ ?_
    rw [QuantumRuntime.run_pure]
    refine DSubInstrument.branch_ret_of_ne _ fun heq ↦ h ?_
    cases heq
    exact hrefl _
  | succ n ih =>
    refine run_bind_branch_eq_zero R I
      (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L (qromSpec X Y) Req Resp Out n u)))
      (retarget s x) _ _ fun p ↦ ?_
    obtain ⟨u', r⟩ := p
    cases r with
    | inl o' =>
      rw [QuantumRuntime.run_pure]
      refine DSubInstrument.branch_ret_of_ne _ fun heq ↦ h ?_
      cases heq
      exact hrefl _
    | inr rc => exact ih _ _ fun h' ↦ h (hstep _ _ _ h')

variable {D : QReg} {σ₁ σ₂ : SubState D}
  {s₁ s₂ : ∀ i, SubInstrument ((qromNSpec St X Y).In i × D) ((qromNSpec St X Y).Out i × D)
    ((qromNSpec St X Y).Result i)}

omit [AddCommGroup Y] in
/-- **Locality in the ports.** The post-state of a leaf with recorded challenger state `t` only
depends on the steps of the ports (challenger states) from which `t` is reachable. -/
theorem pflat_branch_congr (ch : Req → St → Resp × St) (ext : St → St → Prop)
    (hrefl : ∀ s, ext s s) (hstep : ∀ req s t, ext (ch req s).2 t → ext s t) (t : St)
    (hs : ∀ p, ext p t → s₁ p = s₂ p)
    (n : ℕ) {A : QReg} (s : St) (x : IAdv L (qromSpec X Y) Req Resp Out n A) (u : QReg)
    (o : Out u) :
    ((QuantumRuntime.mk D σ₁ s₁).run I (IAdv.pflat ch n s x)).branch ⟨u, (o, t)⟩ =
      ((QuantumRuntime.mk D σ₂ s₂).run I (IAdv.pflat ch n s x)).branch ⟨u, (o, t)⟩ := by
  by_cases hst : ext s t
  · induction n generalizing A s with
    | zero =>
      refine run_retarget_bind_branch_congr (W := Out) I s (hs s hst) x _ _ _ fun u' y ↦ ?_
      rw [QuantumRuntime.run_pure, QuantumRuntime.run_pure]
    | succ n ih =>
      refine run_retarget_bind_branch_congr
        (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L (qromSpec X Y) Req Resp Out n u)))
        I s (hs s hst) x _ _ _ fun u' y ↦ ?_
      cases y with
      | inl o' => rw [QuantumRuntime.run_pure, QuantumRuntime.run_pure]
      | inr rc =>
        by_cases h' : ext (ch rc.1 s).2 t
        · exact ih _ _ h'
        · simp only
          rw [pflat_branch_eq_zero I _ ch ext hrefl hstep n _ _ u o t h',
            pflat_branch_eq_zero I _ ch ext hrefl hstep n _ _ u o t h']
  · rw [pflat_branch_eq_zero I _ ch ext hrefl hstep n _ _ u o t hst,
      pflat_branch_eq_zero I _ ch ext hrefl hstep n _ _ u o t hst]

omit [AddCommGroup Y] in
/-- From a challenger state from which `t` is not reachable, no call carries a weight that
vanishes on the ports from which `t` is not reachable. -/
theorem pflat_queryWeight_eq_zero (R : QuantumRuntime (qromNSpec St X Y))
    {wt : ∀ i, Matrix ((qromNSpec St X Y).In i × R.D) ((qromNSpec St X Y).In i × R.D) ℂ → ℝ≥0∞}
    (ch : Req → St → Resp × St) (ext : St → St → Prop)
    (hstep : ∀ req s t, ext (ch req s).2 t → ext s t) (t : St)
    (hw : ∀ p, ¬ ext p t → ∀ σ, wt p σ = 0)
    (n : ℕ) {A : QReg} (s : St) (x : IAdv L (qromSpec X Y) Req Resp Out n A) (h : ¬ ext s t)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I wt (IAdv.pflat ch n s x) ρ j = 0 := by
  induction n generalizing A s j with
  | zero =>
    refine queryWeight_retarget_bind_eq_zero (W := Out) I R s (hw s h) x _ (fun u y ρ' j' ↦ ?_) ρ j
    rw [QuantumRuntime.queryWeight_pure]
  | succ n ih =>
    refine queryWeight_retarget_bind_eq_zero
      (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L (qromSpec X Y) Req Resp Out n u)))
      I R s (hw s h) x _ (fun u y ρ' j' ↦ ?_) ρ j
    cases y with
    | inl o' => rw [QuantumRuntime.queryWeight_pure]
    | inr rc => exact ih _ _ (fun h' ↦ h (hstep _ _ _ h')) ρ' j'

variable {wt : ∀ i, Matrix ((qromNSpec St X Y).In i × D) ((qromNSpec St X Y).In i × D) ℂ → ℝ≥0∞}

omit [AddCommGroup Y] in
/-- **Locality of query weights.** For a weight that vanishes on the ports from which `t` is not
reachable: two runtimes whose steps agree on the ports from which `t` is reachable, and two
challengers that answer in the same way except when `t` is no longer reachable afterwards, give
the same weights. -/
theorem pflat_queryWeight_congr (ch ch' : Req → St → Resp × St) (ext : St → St → Prop)
    (hstep : ∀ req s t, ext (ch req s).2 t → ext s t)
    (hstep' : ∀ req s t, ext (ch' req s).2 t → ext s t) (t : St)
    (hloc : ∀ req s, ch req s = ch' req s ∨ (¬ ext (ch req s).2 t ∧ ¬ ext (ch' req s).2 t))
    (hs : ∀ p, ext p t → s₁ p = s₂ p)
    (hw : ∀ p, ¬ ext p t → ∀ σ, wt p σ = 0)
    (n : ℕ) {A : QReg} (s : St) (x : IAdv L (qromSpec X Y) Req Resp Out n A)
    (ρ : Matrix (A × D) (A × D) ℂ) (j : ℕ) :
    (QuantumRuntime.mk D σ₁ s₁).queryWeight I wt (IAdv.pflat ch n s x) ρ j =
      (QuantumRuntime.mk D σ₂ s₂).queryWeight I wt (IAdv.pflat ch' n s x) ρ j := by
  by_cases hst : ext s t
  · induction n generalizing A s j with
    | zero =>
      refine queryWeight_retarget_bind_congr (W := Out) I s (hs s hst) x _ _
        (fun u' y ρ' j' ↦ ?_) ρ j
      rw [QuantumRuntime.queryWeight_pure, QuantumRuntime.queryWeight_pure]
    | succ n ih =>
      refine queryWeight_retarget_bind_congr
        (W := fun u ↦ Out u ⊕ (Req × (Resp → IAdv L (qromSpec X Y) Req Resp Out n u)))
        I s (hs s hst) x _ _ (fun u' y ρ' j' ↦ ?_) ρ j
      cases y with
      | inl o' => rw [QuantumRuntime.queryWeight_pure, QuantumRuntime.queryWeight_pure]
      | inr rc =>
        rcases hloc rc.1 s with heq | ⟨h1, h2⟩
        · by_cases h' : ext (ch rc.1 s).2 t
          · simp only [← heq]
            exact ih _ _ ρ' j' h'
          · simp only
            rw [pflat_queryWeight_eq_zero I (QuantumRuntime.mk D σ₁ s₁) ch ext hstep t hw n _ _
                h',
              pflat_queryWeight_eq_zero I (QuantumRuntime.mk D σ₂ s₂) ch' ext hstep' t hw n _ _
                (heq ▸ h')]
        · simp only
          rw [pflat_queryWeight_eq_zero I (QuantumRuntime.mk D σ₁ s₁) ch ext hstep t hw n _ _ h1,
            pflat_queryWeight_eq_zero I (QuantumRuntime.mk D σ₂ s₂) ch' ext hstep' t hw n _ _ h2]
  · rw [pflat_queryWeight_eq_zero I (QuantumRuntime.mk D σ₁ s₁) ch ext hstep t hw n _ _ hst,
      pflat_queryWeight_eq_zero I (QuantumRuntime.mk D σ₂ s₂) ch' ext hstep' t hw n _ _ hst]

end Locality

end PQ.QROM

#print axioms PQ.QROM.nRuntime_sqrt_le
#print axioms PQ.QROM.tsum_massN_le
#print axioms PQ.QROM.IAdv.pflat_isTotalBound
#print axioms PQ.QROM.pflat_branch_congr
#print axioms PQ.QROM.pflat_queryWeight_congr
