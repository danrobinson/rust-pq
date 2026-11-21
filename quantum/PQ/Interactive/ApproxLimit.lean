import PQ.Interactive.Approx
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Limit collapse: quantum machines with arbitrary amplitudes

For a quantum machine whose Born probabilities are arbitrary reals there is no exact classical
simulation with uniform sampling, but there is a sequence of classical *approximants*:

* `sampN n` samples the outcome of an instrument node from the rational probability vector
  `⌊(n+1)·pᵢ⌋/(n+1)` (index `0` takes the remainder), with one uniform query;
* `toProbCompN n Q ρ = toProbCompWith (sampN n) Q ρ` tracks the TRUE unnormalised post-states.

`BornApprox samp` is the abstract property of a sequence of samplers used by the limit theorems:
on every positive-semidefinite state of non-zero trace the `n`-th sampler draws from a weight
vector that converges pointwise to the Born probabilities.  `bornApprox_sampN` proves it for
`sampN`.

Main theorems (no rationality hypothesis):

* `tendsto_bind_closed`: limit collapse of a closed machine, continuation form;
* `tendsto_close_bind`: limit collapse of an open machine run against a classical oracle
  implementation, continuation form;
* `tendsto_prEvent_close`: for a density matrix `ρ`,
  `Pr[p | impl run on toProbCompWith (samp n) Q ρ] → qWeight p (close impl Q s) ρ`;
* `le_of_forall_classical_of_tendsto`: a classical inequality valid for all classical adversaries
  passes to the limit.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Filter Topology
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}
variable {ι' : Type} {spec' : OracleSpec ι'} {σ : Type}

/-! ## Elementary facts -/

lemma prob_le_one {κ : Type} {cs : OracleSpec κ} [OracleSpec.AnswerMeasure cs]
    (mx : OracleComp cs β) (p : β → Prop) : prob mx p ≤ 1 :=
  prEvent_le_one _

/-- If `aₙ → t < ∞`, `0 ≤ xₙ ≤ 1` and `t * xₙ → L`, then `aₙ * xₙ → L`. -/
lemma tendsto_mul_of_le_one {a x : ℕ → ℝ≥0∞} {t L : ℝ≥0∞} (ht : t ≠ ∞)
    (ha : Tendsto a atTop (𝓝 t)) (hx : ∀ n, x n ≤ 1)
    (h : Tendsto (fun n ↦ t * x n) atTop (𝓝 L)) :
    Tendsto (fun n ↦ a n * x n) atTop (𝓝 L) := by
  by_cases h0 : t = 0
  · subst h0
    have hL : L = 0 := by
      simp only [zero_mul] at h
      exact tendsto_nhds_unique h tendsto_const_nhds
    subst hL
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ha
      (fun n ↦ bot_le) fun n ↦ ?_
    calc a n * x n ≤ a n * 1 := by gcongr; exact hx n
      _ = a n := mul_one _
  · have hx' : Tendsto x atTop (𝓝 (L / t)) := by
      have := ENNReal.Tendsto.div_const (b := t) h (Or.inr h0)
      refine this.congr fun n ↦ ?_
      rw [mul_comm, ENNReal.mul_div_cancel_right h0 ht]
    have hLt : L / t ≠ ∞ := by
      have hL : L ≤ t := by
        refine le_of_tendsto' h fun n ↦ ?_
        calc t * x n ≤ t * 1 := by gcongr; exact hx n
          _ = t := mul_one _
      exact ENNReal.div_ne_top (ne_top_of_le_ne_top ht hL) h0
    have := ENNReal.Tendsto.mul ha (Or.inr hLt) hx' (Or.inr ht)
    rwa [ENNReal.mul_div_cancel h0 ht] at this

/-! ## Samplers converging to the Born rule -/

/-- The sequence of samplers `samp` converges to the Born rule: on every positive-semidefinite
state `ρ` of non-zero trace, `samp n j ρ` draws from a weight vector `w n` (in the sense that the
probability of any event after any continuation is the `w n`-average), and `w n i` tends to the
Born probability of outcome `i`. -/
def BornApprox (samp : ℕ → Sampler W) : Prop :=
  ∀ (j : InstrIdx W) (ρ : Matrix W W ℂ), ρ.PosSemidef → ρ.trace.re ≠ 0 →
    ∃ w : ℕ → Fin (j.1 + 1) → ℝ≥0∞,
      (∀ (n : ℕ) (β : Type) (k : Fin (j.1 + 1) → ProbComp β) (p : β → Prop),
        prob (samp n j ρ >>= k) p = ∑ i, w n i * prob (k i) p) ∧
      ∀ i, Tendsto (fun n ↦ w n i) atTop (𝓝 (bornW j.2.1 ρ i))

/-! ## Limit collapse -/

/-- Classical pre-processing, limit form. -/
lemma tendsto_liftU_bind (p : β → Prop) [DecidablePred p] (oa : ProbComp γ)
    (F : γ → Closed W β) (G : ℕ → γ → ProbComp β) (c : ℝ≥0∞) (ρ : Matrix W W ℂ)
    (h : ∀ x, Tendsto (fun n ↦ c * prob (G n x) p) atTop (𝓝 (qWeight p (F x) ρ))) :
    Tendsto (fun n ↦ c * prob (oa >>= G n) p) atTop (𝓝 (qWeight p (liftU oa >>= F) ρ)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using h a
  | query_bind m k ih =>
    rw [liftU_query_bind, bind_assoc, qWeight_unif_bind]
    simp only [bind_assoc, prob_unif_query_bind]
    have e : ∀ n, c * (((m : ℝ≥0∞) + 1)⁻¹ * ∑ i, prob (k i >>= G n) p) =
        ((m : ℝ≥0∞) + 1)⁻¹ * ∑ i, c * prob (k i >>= G n) p := fun n ↦ by
      rw [mul_left_comm, Finset.mul_sum]
    simp only [e]
    exact ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun i _ ↦ ih i) (Or.inr (by simp))

/-- **Limit collapse of a closed machine, continuation form.**  If the continuations `g n`
converge to the quantum continuation `f` (in the sense of Born weights, for every
positive-semidefinite state), then so do the composites with the approximate classical strategies
of `X`. -/
theorem tendsto_bind_closed {samp : ℕ → Sampler W} (hs : BornApprox samp)
    (p : β → Prop) [DecidablePred p] (f : α → Closed W β) (g : ℕ → α → ProbComp β)
    (hfg : ∀ x (ρ' : Matrix W W ℂ), ρ'.PosSemidef →
      Tendsto (fun n ↦ ENNReal.ofReal ρ'.trace.re * prob (g n x) p) atTop
        (𝓝 (qWeight p (f x) ρ')))
    (X : Closed W α) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) :
    Tendsto (fun n ↦ ENNReal.ofReal ρ.trace.re *
        prob (toProbCompCWith (samp n) X ρ >>= g n) p) atTop
      (𝓝 (qWeight p (X >>= f) ρ)) := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => simpa using hfg a ρ hρ
  | query_bind t k ih =>
    rcases t with j | m
    · rw [bind_assoc, qWeight_instr_bind]
      simp only [toProbCompCWith_instr_bind, bind_assoc]
      have hnn : ∀ i, 0 ≤ (j.2.1.branch i ρ).trace.re := fun i ↦
        (posSemidef_branch j i hρ).trace_re_nonneg
      have hsum : ∑ i, (j.2.1.branch i ρ).trace.re = ρ.trace.re := by
        rw [← Complex.re_sum]
        exact congrArg Complex.re (j.2.2.sum_trace_eq (s := Finset.univ) (by simp) ρ)
      by_cases hc : ρ.trace.re = 0
      · have h0 : ∀ i, (j.2.1.branch i ρ).trace.re = 0 := fun i ↦
          (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnn i).mp (hsum.trans hc) i
            (Finset.mem_univ i)
        have hz : ∀ i, qWeight p (k i >>= f) (j.2.1.branch i ρ) = 0 := fun i ↦ by
          have := qWeight_le_trace p (k i >>= f) (posSemidef_branch j i hρ)
          simpa [h0 i] using this
        simp [hz, hc]
      · have hcpos : 0 < ρ.trace.re := lt_of_le_of_ne hρ.trace_re_nonneg (Ne.symm hc)
        obtain ⟨w, hw, hwlim⟩ := hs j ρ hρ hc
        simp only [hw, Finset.mul_sum]
        refine tendsto_finsetSum _ fun i _ ↦ ?_
        simp only [← mul_assoc]
        refine tendsto_mul_of_le_one (t := ENNReal.ofReal (j.2.1.branch i ρ).trace.re)
          ENNReal.ofReal_ne_top ?_ (fun n ↦ prob_le_one _ _)
          (ih i _ (posSemidef_branch j i hρ))
        have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ρ.trace.re) (hwlim i)
          (Or.inr ENNReal.ofReal_ne_top)
        rwa [bornW, ← ENNReal.ofReal_mul hcpos.le, mul_div_cancel₀ _ hc] at this
    · rw [bind_assoc, qWeight_unif_bind]
      refine (ENNReal.Tendsto.const_mul (a := ((m : ℝ≥0∞) + 1)⁻¹)
        (tendsto_finsetSum _ fun i _ ↦ ih i ρ hρ) (Or.inr (by simp))).congr fun n ↦ ?_
      rw [toProbCompCWith_unif_bind, bind_assoc, prob_unif_query_bind]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ mul_left_comm _ _ _

/-- **Limit collapse of a closed machine.** -/
theorem tendsto_closed {samp : ℕ → Sampler W} (hs : BornApprox samp)
    (p : α → Prop) [DecidablePred p] (X : Closed W α) (ρ : Matrix W W ℂ)
    (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ Pr{let y ← toProbCompCWith (samp n) X ρ}[p y]) atTop
      (𝓝 (qWeight p X ρ)) := by
  have := tendsto_bind_closed hs p pure (fun _ ↦ pure)
    (fun x ρ' _ ↦ by simp) X ρ hρ
  simpa [h1, prob_def] using this

/-- **Limit collapse (L1), continuation form.**  `impl` is any classical stateful probabilistic
implementation of the oracles of `Q` forwarding uniform sampling; the classical continuations
`g n` converge to the quantum continuation `f`.  Then the classical probabilities of the
approximate strategies of `Q` run against `impl` (times `tr ρ`) converge to the Born weight of the
closed quantum machine. -/
theorem tendsto_close_bind {samp : ℕ → Sampler W} (hs : BornApprox samp)
    (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp)) (himpl : ForwardsUnif impl)
    (p : β → Prop) [DecidablePred p] (f : α × σ → Closed W β) (g : ℕ → α × σ → ProbComp β)
    (hfg : ∀ x (ρ' : Matrix W W ℂ), ρ'.PosSemidef →
      Tendsto (fun n ↦ ENNReal.ofReal ρ'.trace.re * prob (g n x) p) atTop
        (𝓝 (qWeight p (f x) ρ')))
    (Q : QOC W (unifSpec + spec') α) (s : σ) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) :
    Tendsto (fun n ↦ ENNReal.ofReal ρ.trace.re *
        prob ((simulateQ impl (toProbCompWith (samp n) Q ρ)).run s >>= g n) p) atTop
      (𝓝 (qWeight p (close impl Q s >>= f) ρ)) := by
  refine (tendsto_bind_closed hs p f g hfg (close impl Q s) ρ hρ).congr fun n ↦ ?_
  rw [toProbCompCWith_close _ impl himpl]

/-- **Limit collapse (L1).**  For a density matrix `ρ`, the probability of the event `p` when
`impl` is run on the `n`-th classical approximant of `Q` tends to the Born probability of `p` for
the closed quantum machine. -/
theorem tendsto_prEvent_close {samp : ℕ → Sampler W} (hs : BornApprox samp)
    (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp)) (himpl : ForwardsUnif impl)
    (p : α × σ → Prop) [DecidablePred p] (Q : QOC W (unifSpec + spec') α) (s : σ)
    (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ Pr{let y ← (simulateQ impl (toProbCompWith (samp n) Q ρ)).run s}[p y])
      atTop (𝓝 (qWeight p (close impl Q s) ρ)) := by
  have := tendsto_close_bind hs impl himpl p pure (fun _ ↦ pure)
    (fun x ρ' _ ↦ by simp) Q s ρ hρ
  simpa [h1, prob_def] using this

/-- **Passing a classical inequality to the limit.**  If `f A ≤ g A` for every classical
adversary `A`, and along a sequence of classical adversaries `A n` the two sides converge to `x`
and `y`, then `x ≤ y`. -/
theorem le_of_forall_classical_of_tendsto {Adv : Type*} {f g : Adv → ℝ≥0∞}
    (hfg : ∀ A, f A ≤ g A) (A : ℕ → Adv) {x y : ℝ≥0∞}
    (hx : Tendsto (fun n ↦ f (A n)) atTop (𝓝 x)) (hy : Tendsto (fun n ↦ g (A n)) atTop (𝓝 y)) :
    x ≤ y :=
  le_of_tendsto_of_tendsto' hx hy fun n ↦ hfg (A n)

/-! ## A concrete sequence of rational samplers -/

/-- `⌊(n+1)·x⌋ / (n+1)`. -/
noncomputable def floorN (n : ℕ) (x : ℝ) : ℝ := (⌊((n : ℝ) + 1) * x⌋₊ : ℝ) / ((n : ℝ) + 1)

lemma floorN_nonneg (n : ℕ) (x : ℝ) : 0 ≤ floorN n x := by
  unfold floorN; positivity

lemma floorN_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : floorN n x ≤ x := by
  unfold floorN
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hn, mul_comm]
  exact Nat.floor_le (by positivity)

lemma tendsto_floorN {x : ℝ} (hx : 0 ≤ x) : Tendsto (fun n ↦ floorN n x) atTop (𝓝 x) := by
  have h := tendsto_nat_floor_mul_div_atTop (R := ℝ) hx
  have hn : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine (h.comp hn).congr fun n ↦ ?_
  simp [floorN, mul_comm]

/-- The rational approximation of the weight vector `q`: `⌊(n+1)·qᵢ⌋/(n+1)` for `i ≠ 0`, the
remainder at `i = 0`. -/
noncomputable def approxW {m : ℕ} (n : ℕ) (q : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  fun i ↦ if i = 0 then 1 - ∑ i' ∈ Finset.univ.erase 0, floorN n (q i') else floorN n (q i)

lemma sum_approxW {m : ℕ} (n : ℕ) (q : Fin (m + 1) → ℝ) : ∑ i, approxW n q i = 1 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
  have : ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), approxW n q i =
      ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), floorN n (q i) :=
    Finset.sum_congr rfl fun i hi ↦ by simp [approxW, Finset.ne_of_mem_erase hi]
  rw [this]
  simp [approxW]

lemma approxW_nonneg {m : ℕ} (n : ℕ) {q : Fin (m + 1) → ℝ} (h0 : ∀ i, 0 ≤ q i)
    (h1 : ∑ i, q i = 1) (i : Fin (m + 1)) : 0 ≤ approxW n q i := by
  unfold approxW
  split_ifs with hi
  · have h : ∑ i' ∈ Finset.univ.erase (0 : Fin (m + 1)), floorN n (q i') ≤
        ∑ i' ∈ Finset.univ.erase (0 : Fin (m + 1)), q i' :=
      Finset.sum_le_sum fun i' _ ↦ floorN_le n (h0 i')
    have h2 := Finset.add_sum_erase Finset.univ q (Finset.mem_univ (0 : Fin (m + 1)))
    have := h0 0
    linarith
  · exact floorN_nonneg n _

lemma approxW_rat {m : ℕ} (n : ℕ) (q : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∃ r : ℚ, approxW n q i = r := by
  have hf : ∀ x : ℝ, floorN n x = ((((⌊((n : ℝ) + 1) * x⌋₊ : ℕ) : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) :=
    fun x ↦ by unfold floorN; push_cast; rfl
  unfold approxW
  split_ifs with hi
  · refine ⟨1 - ∑ i' ∈ Finset.univ.erase (0 : Fin (m + 1)),
      ((⌊((n : ℝ) + 1) * q i'⌋₊ : ℕ) : ℚ) / ((n : ℚ) + 1), ?_⟩
    push_cast
    simp only [hf]
    push_cast
    rfl
  · exact ⟨_, hf _⟩

lemma tendsto_approxW {m : ℕ} {q : Fin (m + 1) → ℝ} (h0 : ∀ i, 0 ≤ q i) (h1 : ∑ i, q i = 1)
    (i : Fin (m + 1)) : Tendsto (fun n ↦ approxW n q i) atTop (𝓝 (q i)) := by
  by_cases hi : i = 0
  · subst hi
    simp only [approxW, ite_true]
    have h2 : q 0 = 1 - ∑ i' ∈ Finset.univ.erase (0 : Fin (m + 1)), q i' := by
      have := Finset.add_sum_erase Finset.univ q (Finset.mem_univ (0 : Fin (m + 1)))
      linarith
    rw [h2]
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ fun i' _ ↦ tendsto_floorN (h0 i'))
  · simp only [approxW, hi, ite_false]
    exact tendsto_floorN (h0 i)

/-- The `n`-th rational sampler: sample the outcome of the instrument `j` in the state `ρ` from
the rational approximation `approxW n` of the Born probabilities, with one uniform query. -/
noncomputable def sampN (n : ℕ) : Sampler W := fun j ρ ↦
  sampleOf fun i ↦ ENNReal.ofReal
    (approxW n (fun i ↦ (j.2.1.branch i ρ).trace.re / ρ.trace.re) i)

/-- The rational samplers converge to the Born rule. -/
theorem bornApprox_sampN : BornApprox (sampN (W := W)) := by
  intro j ρ hρ hc
  have hcpos : 0 < ρ.trace.re := lt_of_le_of_ne hρ.trace_re_nonneg (Ne.symm hc)
  have hnn : ∀ i, 0 ≤ (j.2.1.branch i ρ).trace.re / ρ.trace.re := fun i ↦
    div_nonneg (posSemidef_branch j i hρ).trace_re_nonneg hcpos.le
  have hsum : ∑ i, (j.2.1.branch i ρ).trace.re / ρ.trace.re = 1 := by
    rw [← Finset.sum_div, ← Complex.re_sum,
      congrArg Complex.re (j.2.2.sum_trace_eq (s := Finset.univ) (by simp) ρ), div_self hc]
  refine ⟨fun n i ↦ ENNReal.ofReal
    (approxW n (fun i ↦ (j.2.1.branch i ρ).trace.re / ρ.trace.re) i), fun n β k p ↦ ?_,
    fun i ↦ ?_⟩
  · exact prob_sampleOf_bind (isUnifSampleable_of_rat _ (approxW_nonneg n hnn hsum)
      (sum_approxW n _) (approxW_rat n _)) k p
  · exact (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_approxW hnn hsum i)

/-- The `n`-th classical approximant of the quantum machine `Q` started in `ρ`. -/
noncomputable abbrev toProbCompN (n : ℕ) (Q : QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    OracleComp (unifSpec + spec') α :=
  toProbCompWith (sampN n) Q ρ

/-- The `n`-th classical approximant of the closed machine `X` started in `ρ`. -/
noncomputable abbrev toProbCompCN (n : ℕ) (X : Closed W α) (ρ : Matrix W W ℂ) : ProbComp α :=
  toProbCompCWith (sampN n) X ρ

/-- **Limit collapse for the rational approximants (L1), unconditional.** -/
theorem tendsto_prEvent_close_toProbCompN
    (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp)) (himpl : ForwardsUnif impl)
    (p : α × σ → Prop) [DecidablePred p] (Q : QOC W (unifSpec + spec') α) (s : σ)
    (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) :
    Tendsto (fun n ↦ Pr{let y ← (simulateQ impl (toProbCompN n Q ρ)).run s}[p y])
      atTop (𝓝 (qWeight p (close impl Q s) ρ)) :=
  tendsto_prEvent_close bornApprox_sampN impl himpl p Q s ρ hρ h1

end PQ.Interactive

open PQ.Interactive in
#print axioms tendsto_bind_closed
open PQ.Interactive in
#print axioms tendsto_close_bind
open PQ.Interactive in
#print axioms bornApprox_sampN
open PQ.Interactive in
#print axioms tendsto_prEvent_close_toProbCompN
