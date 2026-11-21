import QuantumFoundations.DSubInstrument
import QuantumFoundations.Pure.State

/-!
# Event weights of dependent subinstruments on pure inputs (branch sums)

Infrastructure for extending the tight bounds from circuits to arbitrary VCVio programs
(`PQ/QROM/PurifyProgram.lean`, `PQ/QROM/PurifyTight.lean`).

* `DW p E`: the weight of the outcome event `E` of a dependent subinstrument `p`, as a
  ℂ-linear functional of the input operator (`∑' i ∈ E, tr (p.branch i σ)`).
* `gv p E v := re (DW p E |v⟩⟨v|)`: the same on a pure (unnormalised) input vector.
* `gv_bind`: the weight of a composite on a pure input is a **branch sum**: with Kraus operators
  `krausOf p i κ` of the branches of `p`, `gv (p.bind k) E v = ∑' i, ∑ κ, gv (k i) E (K i κ v)`,
  and `kraus_sum_le`: `∑ i ∈ s, ∑ κ, ‖K i κ v‖² ≤ ‖v‖²` for every finite set `s` of outcomes.
-/

open Quantum Matrix
open scoped ComplexOrder

namespace PQ.QROM.Purify

variable {A : Type*} [Fintype A] {ι κ : Type*} {B : ι → Type*}
  [∀ i, Fintype (B i)] {C : κ → Type*} [∀ c, Fintype (C c)]

/-- The restriction of a dependent subinstrument to the outcomes in `E`. -/
noncomputable def restr (p : DSubInstrument A ι B) (E : ι → Prop) :
    DSubInstrument A {i // E i} fun i ↦ B i.1 :=
  p.comap Subtype.val Subtype.val_injective

/-- The weight of the event `E` of `p`, as a linear functional of the input operator. -/
noncomputable def DW (p : DSubInstrument A ι B) (E : ι → Prop) : Matrix A A ℂ →ₗ[ℂ] ℂ :=
  MatrixMap.familyTrace (restr p E).branch

theorem DW_apply (p : DSubInstrument A ι B) (E : ι → Prop) (σ : Matrix A A ℂ) :
    DW p E σ = ∑' c : {i // E i}, (p.branch c.1 σ).trace :=
  (restr p E).isCPTNIFamily.familyTrace_apply σ

theorem DW_re (p : DSubInstrument A ι B) (E : ι → Prop) (σ : Matrix A A ℂ) :
    (DW p E σ).re = ∑' c : {i // E i}, (p.branch c.1 σ).trace.re := by
  rw [DW_apply]
  exact (restr p E).isCPTNIFamily.re_tsum_trace_apply σ

theorem DW_re_nonneg (p : DSubInstrument A ι B) (E : ι → Prop) {σ : Matrix A A ℂ}
    (hσ : σ.PosSemidef) : 0 ≤ (DW p E σ).re := by
  rw [DW_re]
  exact tsum_nonneg fun c ↦ p.trace_re_branch_apply_nonneg c.1 hσ

theorem DW_re_le (p : DSubInstrument A ι B) (E : ι → Prop) {σ : Matrix A A ℂ}
    (hσ : σ.PosSemidef) : (DW p E σ).re ≤ σ.trace.re := by
  rw [DW_re]
  exact (restr p E).tsum_trace_re_le hσ

theorem DW_eq_ofReal (p : DSubInstrument A ι B) (E : ι → Prop) {σ : Matrix A A ℂ}
    (hσ : σ.PosSemidef) : DW p E σ = ((DW p E σ).re : ℂ) := by
  rw [DW_re, DW_apply, Complex.ofReal_tsum]
  exact tsum_congr fun c ↦ ((p.posSemidef_branch_apply c.1 hσ).ofReal_trace_re).symm

theorem restr_bind (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    (E : κ → Prop) : restr (p.bind k) E = p.bind fun i ↦ restr (k i) E :=
  DSubInstrument.ext rfl

theorem DW_bind (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    (E : κ → Prop) (σ : Matrix A A ℂ) :
    DW (p.bind k) E σ = ∑' i, DW (k i) E (p.branch i σ) := by
  rw [DW, restr_bind]
  exact DSubInstrument.familyTrace_bind p (fun i ↦ restr (k i) E) σ

/-- The weight of a composite: real form, with summability. -/
theorem DW_bind_re (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    (E : κ → Prop) {σ : Matrix A A ℂ} (hσ : σ.PosSemidef) :
    Summable (fun i ↦ (DW (k i) E (p.branch i σ)).re) ∧
      (DW (p.bind k) E σ).re = ∑' i, (DW (k i) E (p.branch i σ)).re := by
  have hs : Summable (fun i ↦ (DW (k i) E (p.branch i σ)).re) :=
    summable_of_sum_le (fun i ↦ DW_re_nonneg _ _ (p.posSemidef_branch_apply i hσ)) fun s ↦
      (Finset.sum_le_sum fun i _ ↦ DW_re_le _ _ (p.posSemidef_branch_apply i hσ)).trans
        (p.sum_trace_re_le s hσ)
  refine ⟨hs, ?_⟩
  rw [DW_bind]
  have hc : Summable (fun i ↦ DW (k i) E (p.branch i σ)) :=
    (Complex.summable_ofReal.mpr hs).congr fun i ↦
      (DW_eq_ofReal _ _ (p.posSemidef_branch_apply i hσ)).symm
  exact Complex.re_tsum hc

theorem DW_ret (i : ι) (E : ι → Prop) [Decidable (E i)] (σ : Matrix (B i) (B i) ℂ) :
    DW (DSubInstrument.ret B i) E σ = if E i then σ.trace else 0 := by
  classical
  by_cases h : E i
  · simp only [h, ↓reduceIte]
    rw [DW, MatrixMap.familyTrace_apply_of_forall_notMem (s := {⟨i, h⟩})]
    · rw [Finset.sum_singleton]
      change ((DSubInstrument.ret B i).branch i σ).trace = _
      rw [DSubInstrument.branch_ret_self]
      rfl
    · intro c hc
      have hne : c.1 ≠ i := fun e ↦ hc (Finset.mem_singleton.2 (Subtype.ext e))
      exact DSubInstrument.branch_ret_of_ne B hne
  · simp only [h, ↓reduceIte]
    rw [DW, MatrixMap.familyTrace_apply_of_forall_notMem (s := ∅)]
    · rfl
    · intro c _
      have hne : c.1 ≠ i := fun e ↦ h (e ▸ c.2)
      exact DSubInstrument.branch_ret_of_ne B hne

/-- An event and its complement have total weight at most the trace of the input. -/
theorem DW_re_add_compl_le (p : DSubInstrument A ι B) (E : ι → Prop) {σ : Matrix A A ℂ}
    (hσ : σ.PosSemidef) : (DW p E σ).re + (DW p (fun i ↦ ¬ E i) σ).re ≤ σ.trace.re := by
  rw [DW_re, DW_re]
  have hs := p.isCPTNIFamily.summable_trace_re_apply hσ
  have h := hs.tsum_subtype_add_tsum_subtype_compl {i | E i}
  exact (le_of_eq h).trans (p.tsum_trace_re_le hσ)

/-! ### Pure inputs -/

/-- The weight of the event `E` of `p` on the pure input `|v⟩⟨v|` (not necessarily normalised). -/
noncomputable def gv (p : DSubInstrument A ι B) (E : ι → Prop) (v : EuclideanSpace ℂ A) : ℝ :=
  (DW p E (ketBra v v)).re

theorem gv_nonneg (p : DSubInstrument A ι B) (E : ι → Prop) (v : EuclideanSpace ℂ A) :
    0 ≤ gv p E v := DW_re_nonneg p E (posSemidef_ketBra_self v)

theorem gv_le (p : DSubInstrument A ι B) (E : ι → Prop) (v : EuclideanSpace ℂ A) :
    gv p E v ≤ ‖v‖ ^ 2 :=
  (DW_re_le p E (posSemidef_ketBra_self v)).trans (le_of_eq (trace_re_ketBra_self v))

theorem gv_ret (i : ι) (E : ι → Prop) [Decidable (E i)] (v : EuclideanSpace ℂ (B i)) :
    gv (DSubInstrument.ret B i) E v = if E i then ‖v‖ ^ 2 else 0 := by
  rw [gv, DW_ret]
  split_ifs
  · exact trace_re_ketBra_self v
  · rfl

/-- Kraus operators of the branch `i` of `p`. -/
noncomputable def krausOf (p : DSubInstrument A ι B) (i : ι) : B i × A → Matrix (B i) A ℂ :=
  Classical.choose (p.exists_kraus_branch i)

theorem branch_eq_sum_krausOf (p : DSubInstrument A ι B) (i : ι) :
    p.branch i = ∑ c, MatrixMap.conj (krausOf p i c) :=
  Classical.choose_spec (p.exists_kraus_branch i)

theorem branch_ketBra [DecidableEq A] (p : DSubInstrument A ι B) (i : ι) (v : EuclideanSpace ℂ A) :
    p.branch i (ketBra v v) =
      ∑ c, ketBra (Matrix.toEuclideanLin (krausOf p i c) v)
        (Matrix.toEuclideanLin (krausOf p i c) v) := by
  rw [branch_eq_sum_krausOf, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun c _ ↦ conj_ketBra_self _ v

/-- **Kraus bound.** The squared norms of the Kraus images over any finite set of outcomes sum
to at most the squared norm of the input. -/
theorem kraus_sum_le [DecidableEq A] (p : DSubInstrument A ι B) (s : Finset ι) (v : EuclideanSpace ℂ A) :
    ∑ i ∈ s, ∑ c, ‖Matrix.toEuclideanLin (krausOf p i c) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have h := p.sum_trace_re_le s (posSemidef_ketBra_self v)
  rw [trace_re_ketBra_self] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_)) h
  rw [branch_ketBra, Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun c _ ↦ (trace_re_ketBra_self _).symm

/-- **Branch sum.** The weight of a composite on a pure input is the sum over the outcomes and
Kraus indices of the first step of the weights of the continuations on the Kraus images. -/
theorem gv_bind [DecidableEq A] (p : DSubInstrument A ι B) (k : (i : ι) → DSubInstrument (B i) κ C)
    (E : κ → Prop) (v : EuclideanSpace ℂ A) :
    Summable (fun i ↦ ∑ c, gv (k i) E (Matrix.toEuclideanLin (krausOf p i c) v)) ∧
      gv (p.bind k) E v = ∑' i, ∑ c, gv (k i) E (Matrix.toEuclideanLin (krausOf p i c) v) := by
  obtain ⟨hs, he⟩ := DW_bind_re p k E (posSemidef_ketBra_self v)
  have e : ∀ i, (DW (k i) E (p.branch i (ketBra v v))).re =
      ∑ c, gv (k i) E (Matrix.toEuclideanLin (krausOf p i c) v) := fun i ↦ by
    rw [branch_ketBra, map_sum, Complex.re_sum]
    rfl
  exact ⟨hs.congr e, he.trans (tsum_congr e)⟩

end PQ.QROM.Purify

#print axioms PQ.QROM.Purify.gv_bind
#print axioms PQ.QROM.Purify.kraus_sum_le
