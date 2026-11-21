import PQ.QROM.MultiPhaseGame

/-!
# Multi-phase reprogramming, phase-weighted form

`mp_reprogram` (`PQ/QROM/MultiPhaseGame.lean`) charges every quantum query for the rows of all
`s` randomizers.  A query made after `i` target requests only has to be hidden from the rows of
the `s − i` randomizers that are not issued yet.  This file states the reprogramming step with
the *phase-weighted* budget.

* `IsWeightedBound x κ n`: on every path of `x`, the sum over the oracle calls of `κ (port)` is
  at most `n` (`κ : Port → ℕ`; local operations are free).  With `κ = 1` this is `IsTotalBound`.
* `tsum_queryWeight_le_of_isWeightedBound`, `tsum_weighted_massN_le`: the masses, weighted by
  `κ`, add up to at most `n` times the trace.
* `mp_reprogram_weighted`: if every path of the game's composite program satisfies
  `∑_{calls} (s − #requests made before the call) ≤ W`
  (`∀ Rs, IsWeightedBound (mpComp s x Rs) (fun t ↦ s - t.length) W`), then
  `√real ≤ √hybrid + √(4 q W / |K|)`.
  For an adversary making at most `qᵢ` queries after exactly `i` requests on every path,
  `W = ∑ᵢ qᵢ (s − i)` satisfies the hypothesis (not formalised as a separate per-phase
  predicate: `W` is the per-path quantity itself).
* Extreme cases: `mpComp_isWeightedBound` (every adversary with `q` queries has `W = s q`:
  this recovers `mp_reprogram`), and `mp_reprogram_zero` (`W = 0`, e.g. an adversary that makes
  all `s` requests before its first quantum query: no reprogramming loss, `√real ≤ √hybrid`).

The factor `q` in `4 q W / |K|` is the Cauchy–Schwarz factor over the calls and is still the
total number of calls.
-/

open MeasureTheory ENNReal Quantum Matrix IPFunctor
open scoped Kronecker ComplexOrder

universe u v w

namespace PQ.QROM

/-! ## Weighted call budgets -/

section Weighted

variable {L : LocalSig.{u, v}} {spec : QuantumOracleSpec.{0, 0}} {W : QReg → Type w} {A : QReg}

/-- The weighted charge of a command: `κ i` for a call of port `i`, zero for a local
operation. -/
def cmdWCharge (κ : spec.Port → ℕ) : {A : QReg} → QuantumComp.Cmd L spec A → ℕ
  | _, .prim _ => 0
  | _, .query i _ _ => κ i

/-- On every path, the sum over the oracle calls of `κ (port of the call)` is at most `n`. -/
def IsWeightedBound (x : QuantumComp L spec W A) (κ : spec.Port → ℕ) (n : ℕ) : Prop :=
  IFreeM.IsChargeBound x (fun _ c ↦ cmdWCharge κ c) n

theorem isWeightedBound_pure (a : W A) (κ : spec.Port → ℕ) (n : ℕ) :
    IsWeightedBound (QuantumComp.pure a : QuantumComp L spec W A) κ n :=
  IFreeM.isChargeBound_pure a n

theorem isWeightedBound_primBind_iff (κ : spec.Port → ℕ) (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec W (L.next o b)) (n : ℕ) :
    IsWeightedBound (QuantumComp.primBind o k) κ n ↔ ∀ b, IsWeightedBound (k b) κ n := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := QuantumComp.toIPFunctor L spec)
    (c := fun _ c ↦ cmdWCharge κ c) (.prim o) (QuantumComp.onDown k) n).trans ?_
  simp only [cmdWCharge, Nat.zero_le, Nat.sub_zero, true_and]
  exact ULift.forall

theorem isWeightedBound_queryBind_iff (κ : spec.Port → ℕ) (i : spec.Port) (B : QReg)
    (e : A ≃ spec.In i × B)
    (k : spec.Result i → QuantumComp L spec W (QReg.of (spec.Out i × B))) (n : ℕ) :
    IsWeightedBound (QuantumComp.queryBind i B e k) κ n ↔
      κ i ≤ n ∧ ∀ r, IsWeightedBound (k r) κ (n - κ i) := by
  refine (IFreeM.isChargeBound_liftBind_iff (P := QuantumComp.toIPFunctor L spec)
    (c := fun _ c ↦ cmdWCharge κ c) (.query i B e) (QuantumComp.onDown k) n).trans ?_
  exact and_congr Iff.rfl ULift.forall

theorem IsWeightedBound.mono {x : QuantumComp L spec W A} {κ : spec.Port → ℕ} {n m : ℕ}
    (hx : IsWeightedBound x κ n) (h : n ≤ m) : IsWeightedBound x κ m :=
  IFreeM.IsChargeBound.mono hx h

/-- A program with at most `q` calls in total, each of weight at most `m`, has weighted budget
`m q`. -/
theorem isWeightedBound_of_isTotalBound {κ : spec.Port → ℕ} {m : ℕ} (hκ : ∀ i, κ i ≤ m)
    {x : QuantumComp L spec W A} {q : ℕ} (hx : IsTotalBound x q) :
    IsWeightedBound x κ (m * q) := by
  induction x using QuantumComp.inductionOn generalizing q with
  | pure _ _ => exact isWeightedBound_pure _ _ _
  | primBind _ o k ih =>
    rw [isTotalBound_primBind_iff] at hx
    rw [isWeightedBound_primBind_iff]
    exact fun b ↦ ih b (hx b)
  | queryBind _ i B e k ih =>
    rw [isTotalBound_queryBind_iff] at hx
    rw [isWeightedBound_queryBind_iff]
    obtain ⟨hq, hk⟩ := hx
    have h1 : m * (q - 1) + m = m * q := by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      simp [Nat.mul_succ]
    refine ⟨(hκ i).trans (by rw [← h1]; omega), fun r ↦ (ih r (hk r)).mono ?_⟩
    have := hκ i
    omega

variable (R : QuantumRuntime spec) (I : L.Interp)
  {wt : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}

/-- **Weighted masses.** If the weight of a call of port `i` is at most `κ i` times its trace,
the weights summed over all calls of a program of weighted budget `n` are at most `n` times the
trace of the input. -/
theorem tsum_queryWeight_le_of_isWeightedBound {κ : spec.Port → ℕ}
    (hw : ∀ i σ, σ.PosSemidef → wt i σ ≤ (κ i : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)
    {x : QuantumComp L spec W A} {n : ℕ} (hx : IsWeightedBound x κ n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    ∑' j, R.queryWeight I wt x ρ j ≤ n * ENNReal.ofReal ρ.trace.re := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ _ => simp
  | primBind _ o k ih =>
    rw [isWeightedBound_primBind_iff] at hx
    simp only [QuantumRuntime.queryWeight_primBind]
    rw [tsum_comm]
    refine (tsum_le_tsum fun b ↦
      ih b (hx b) (((I o).frame R.D).posSemidef_branch_apply b hρ)).trans ?_
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul' le_rfl ((((I o).frame R.D).isCPTNIFamily).tsum_ofReal_trace_re_le hρ)
  | queryBind _ i E ℓ k ih =>
    rw [isWeightedBound_queryBind_iff] at hx
    obtain ⟨hi, hk⟩ := hx
    rw [tsum_eq_zero_add' CompleteLattice.summable]
    have h0 : R.queryWeight I wt (QuantumComp.queryBind i E ℓ k) ρ 0 ≤
        (κ i : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re := by
      simpa using hw i _ (QuantumRuntime.posSemidef_callInput ℓ hρ)
    have h1 : ∑' j, R.queryWeight I wt (QuantumComp.queryBind i E ℓ k) ρ (j + 1) ≤
        ((n - κ i : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re := by
      simp only [QuantumRuntime.queryWeight_queryBind_succ]
      rw [tsum_comm]
      refine (tsum_le_tsum fun r ↦
        ih r (hk r) ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ)).trans ?_
      rw [ENNReal.tsum_mul_left]
      exact mul_le_mul' le_rfl ((R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ)
    refine (add_le_add h0 h1).trans (le_of_eq ?_)
    rw [← add_mul, ← Nat.cast_add, Nat.add_sub_cancel' hi]

/-- The query masses of the ports, weighted by `κ`, add up to at most the weighted budget times
the trace. -/
theorem tsum_weighted_queryMass_le {κ : spec.Port → ℕ}
    {x : QuantumComp L spec W A} {n : ℕ} (hx : IsWeightedBound x κ n)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    ∑' i, (κ i : ℝ≥0∞) * R.queryMass I x ρ i ≤ n * ENNReal.ofReal ρ.trace.re := by
  classical
  have e : ∑' i, (κ i : ℝ≥0∞) * R.queryMass I x ρ i =
      ∑' j, R.queryWeight I (fun i' σ ↦ ∑' i : spec.Port,
        (κ i : ℝ≥0∞) * (if i' = i then ENNReal.ofReal σ.trace.re else 0)) x ρ j := by
    simp only [QuantumRuntime.queryMass, QuantumRuntime.queryMassAt, ← ENNReal.tsum_mul_left]
    rw [tsum_comm]
    refine tsum_congr fun j ↦ ?_
    rw [← QuantumRuntime.tsum_queryWeight]
    exact tsum_congr fun i ↦ (QuantumRuntime.queryWeight_const_mul R I _ x ρ j).symm
  rw [e]
  refine tsum_queryWeight_le_of_isWeightedBound R I (fun i' σ _ ↦ ?_) hx hρ
  rw [tsum_eq_single i' fun i hi ↦ by simp [Ne.symm hi]]
  simp

end Weighted

/-! ## Weighted masses of the `P`-port oracle -/

section MassN

variable {P X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The index masses, weighted by a function `κ` of the port, add up to at most the weighted
budget times the trace. -/
theorem tsum_weighted_massN_le (I : L.Interp) (G : P → X → Y)
    {x : QuantumComp L (qromNSpec P X Y) W A} {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) (κ : P → ℕ) {n : ℕ} (hx : IsWeightedBound x κ n) :
    ∑' c : Σ _ : P, X, (κ c.1 : ℝ≥0∞) * massN I G x σ c ≤ n * ENNReal.ofReal σ.trace.re := by
  refine le_trans (le_of_eq (tsum_sigma (β := fun _ : P ↦ X)
    fun p k ↦ (κ p : ℝ≥0∞) * massN I G x σ ⟨p, k⟩)) ?_
  have h : ∀ p : P, ∑' k : X, massN I G x σ ⟨p, k⟩ = (nRuntime G).queryMass I x σ p := fun p ↦
    (nRuntime G).tsum_indexMass_eq_queryMass I (κ := fun _ ↦ X) (blockN P X Y) p
      (sum_conjTranspose_blockN_mul p) x hσ
  simp only [ENNReal.tsum_mul_left, h]
  exact tsum_weighted_queryMass_le (nRuntime G) I hx hσ

end MassN

/-! ## The reprogramming step with the phase-weighted budget -/

section Game

variable {K M Y Req : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype M] [DecidableEq M]
  [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {L : LocalSig.{u, v}} {Out : QReg → Type w} {A : QReg}
  {I : L.Interp} {ρ : SubState A} {s : ℕ} {x : IAdv L (qromSpec (K × M) Y) Req K Out s A}
  {win : (Fin s → K) → (K × M → Y) → (Σ u, Out u × List Req) → Prop} {q Wt : ℕ}

omit [AddCommGroup Y] in
/-- Every adversary with at most `q` queries has phase-weighted budget `s q`. -/
theorem mpComp_isWeightedBound (hx : IAdv.IsQueryBound s x (fun _ ↦ q)) (Rs : Fin s → K) :
    IsWeightedBound (mpComp s x Rs) (fun t : List Req ↦ s - t.length) (s * q) :=
  isWeightedBound_of_isTotalBound (fun _ ↦ Nat.sub_le _ _) (mpComp_isTotalBound hx Rs)

theorem sum_fin_ite_le (s l : ℕ) (m : ℝ≥0∞) :
    ∑ j : Fin s, (if l ≤ j.1 then m else 0) = ((s - l : ℕ) : ℝ≥0∞) * m := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ if l ≤ j then m else 0) s, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  have : (Finset.range s).filter (fun j ↦ l ≤ j) = Finset.Ico l s := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

/-- The averaged mass term, phase-weighted. -/
theorem avg_mp_diffMass_le_weighted
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Req ↦ s - t.length) Wt) :
    (avg fun Rs : Fin s → K ↦ avg fun Φ : (K × M) × Bool → Y ↦
      diffMass I (fun _ ↦ mpFn Rs Φ s) (fun t : List Req ↦ mpFn Rs Φ t.length) (mpComp s x Rs)
        (joint ρ)) ≤ (Fintype.card K : ℝ≥0∞)⁻¹ * Wt := by
  refine (avg_mono fun Rs ↦ avg_mono fun Φ ↦ mp_diffMass_le Rs Φ).trans ?_
  rw [avg_comm]
  refine avg_le fun Φ ↦ ?_
  rw [avg_finset_sum]
  have hj : ∀ j : Fin s, (avg fun Rs : Fin s → K ↦ ∑' c : Σ _ : List Req, K × M,
      if c.1.length ≤ j.1 then (if Rs j = c.2.1 then mpMass I ρ s x Rs Φ c else 0) else 0) ≤
      (Fintype.card K : ℝ≥0∞)⁻¹ * avg fun Rs : Fin s → K ↦ ∑' c : Σ _ : List Req, K × M,
        if c.1.length ≤ j.1 then mpMass I ρ s x Rs Φ c else 0 := by
    intro j
    rw [avg_tsum, avg_tsum, ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun c ↦ ?_
    by_cases hlen : c.1.length ≤ j.1
    · simp only [hlen, ↓reduceIte]
      exact (avg_coord_eq j c.2.1 (fun Rs ↦ mpMass I ρ s x Rs Φ c)
        fun Rs r ↦ mpMass_update Rs Φ j r c hlen).le
    · simp only [hlen, ↓reduceIte]
      exact (avg_le (c := 0) fun _ ↦ le_rfl).trans zero_le
  refine (Finset.sum_le_sum fun j _ ↦ hj j).trans ?_
  rw [← Finset.mul_sum, ← avg_finset_sum]
  refine mul_le_mul' le_rfl (avg_le fun Rs ↦ ?_)
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  simp only [sum_fin_ite_le]
  exact (tsum_weighted_massN_le I _ (joint_posSemidef ρ) _ (hW Rs)).trans
    ((mul_le_mul' le_rfl (ofReal_trace_joint_le_one ρ)).trans (mul_one _).le)

/-- **Multi-phase reprogramming, phase-weighted.**  If on every path the sum over the quantum
queries of `s − (number of requests made before the query)` is at most `Wt`, then
`√(real) ≤ √(hybrid) + √(4 q Wt / |K|)`. -/
theorem mp_reprogram_weighted [Nonempty Y] (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Req ↦ s - t.length) Wt) :
    mpExp I ρ s x win ^ (2⁻¹ : ℝ) ≤
      mpHybExp I ρ s x win ^ (2⁻¹ : ℝ) +
        (4 * (q : ℝ≥0∞) * ((Fintype.card K : ℝ≥0∞)⁻¹ * Wt)) ^ (2⁻¹ : ℝ) := by
  rw [mpExp_eq']
  refine (sqrt_avg_le _ _ _ fun Rs ↦ sqrt_avg_le _ _ _ fun Φ ↦
    (nRuntime_sqrt_le I (fun _ ↦ mpFn Rs Φ s) (fun t : List Req ↦ mpFn Rs Φ t.length)
      (joint_posSemidef ρ) (mpComp_isTotalBound hx Rs) (win Rs (mpFn Rs Φ s))).1).trans
    (add_le_add le_rfl (sqrt_le_sqrt ?_))
  simp only [avg_mul_left]
  exact mul_le_mul' le_rfl (avg_mp_diffMass_le_weighted hW)

/-- **No reprogramming loss** for an adversary whose quantum queries all come after its `s`-th
request (phase-weighted budget `0`): `√(real) ≤ √(hybrid)`, hence `real ≤ hybrid`. -/
theorem mp_reprogram_zero [Nonempty Y] (hx : IAdv.IsQueryBound s x (fun _ ↦ q))
    (hW : ∀ Rs : Fin s → K,
      IsWeightedBound (mpComp s x Rs) (fun t : List Req ↦ s - t.length) 0) :
    mpExp I ρ s x win ≤ mpHybExp I ρ s x win := by
  have h := mp_reprogram_weighted (I := I) (ρ := ρ) (win := win) hx hW
  simp only [Nat.cast_zero, mul_zero] at h
  rw [ENNReal.zero_rpow_of_pos (by norm_num), add_zero] at h
  calc mpExp I ρ s x win = (mpExp I ρ s x win ^ (2⁻¹ : ℝ)) ^ 2 := (sq_sqrt _).symm
    _ ≤ (mpHybExp I ρ s x win ^ (2⁻¹ : ℝ)) ^ 2 := pow_le_pow_left' h 2
    _ = _ := sq_sqrt _

end Game

end PQ.QROM

#print axioms PQ.QROM.tsum_weighted_massN_le
#print axioms PQ.QROM.mpComp_isWeightedBound
#print axioms PQ.QROM.mp_reprogram_weighted
#print axioms PQ.QROM.mp_reprogram_zero
