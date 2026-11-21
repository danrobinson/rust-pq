import PQ.Interactive.Model

/-!
# Collapse of a quantum adversary with rational Born probabilities into `ProbComp`

`Q.toProbComp ρ` is the classical strategy that tracks the (unnormalised) workspace state of the
quantum machine `Q` and replaces every instrument node by a classical sample of its outcome with
the Born probabilities, drawn with a single uniform query.  This is possible when the Born
probabilities are rational (`RationalBorn Q ρ`).

Main theorem (`qWeight_close_eq`): for every classical stateful probabilistic implementation
`impl` of the oracles (forwarding uniform sampling), the Born weight of any event of the closed
quantum machine equals the classical probability of the same event when `impl` is run on the
classical strategy.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}

/-! ## Classical probability rules used below -/

/-- Probability that the output of the oracle computation `mx` satisfies `p`; this is VCVio's
`Pr{let x ← mx}[p x]` (see `prob_def`), kept as a named function so that the computation can be
rewritten. -/
noncomputable def prob {κ : Type} {cs : OracleSpec κ} [OracleSpec.AnswerMeasure cs]
    (mx : OracleComp cs β) (p : β → Prop) : ℝ≥0∞ :=
  Pr{let x ← mx}[p x]

lemma prob_def {κ : Type} {cs : OracleSpec κ} [OracleSpec.AnswerMeasure cs]
    (mx : OracleComp cs β) (p : β → Prop) : prob mx p = Pr{let x ← mx}[p x] := rfl

@[simp] lemma prob_pure {κ : Type} {cs : OracleSpec κ} [OracleSpec.AnswerMeasure cs]
    (a : β) (p : β → Prop) [Decidable (p a)] :
    prob (pure a : OracleComp cs β) p = if p a then 1 else 0 :=
  prEvent_pure a p

/-- Probability of an event after one uniform query. -/
lemma prob_unif_query_bind (n : ℕ) (k : Fin (n + 1) → ProbComp β) (p : β → Prop) :
    prob (liftM (unifSpec.query n) >>= k) p =
      ((n : ℝ≥0∞) + 1)⁻¹ * ∑ i, prob (k i) p := by
  unfold prob
  let _ : MeasurableSpace (Fin (n + 1)) := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, lintegral_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm]
  congr 1
  rw [evalDist_liftM_query_apply (spec := unifSpec) n (MeasurableSet.of_discrete)]
  simp

/-- Pre-processing by classical probabilistic code: if every continuation collapses with the same
factor `c`, so does the composite. -/
lemma qWeight_liftU_bind (p : β → Prop) [DecidablePred p] (oa : ProbComp γ)
    (f : γ → Closed W β) (g : γ → ProbComp β) (c : ℝ≥0∞) (ρ : Matrix W W ℂ)
    (h : ∀ x, qWeight p (f x) ρ = c * prob (g x) p) :
    qWeight p (liftU oa >>= f) ρ = c * prob (oa >>= g) p := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using h a
  | query_bind n k ih =>
    rw [liftU_query_bind, bind_assoc, bind_assoc, qWeight_unif_bind, prob_unif_query_bind]
    simp only [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_left_comm]

/-! ## Sampling a rational distribution with one uniform query -/

/-- The weights `w` on `Fin (n+1)` are the fibre proportions of a map from some `Fin (b+1)`. -/
def IsUnifSampleable {n : ℕ} (w : Fin (n + 1) → ℝ≥0∞) : Prop :=
  ∃ (b : ℕ) (f : Fin (b + 1) → Fin (n + 1)),
    ∀ i, w i = ((Finset.univ.filter fun j ↦ f j = i).card : ℝ≥0∞) / ((b : ℝ≥0∞) + 1)

open Classical in
/-- Sample from the distribution `w` with a single uniform query (when `w` is sampleable;
otherwise an arbitrary value). -/
noncomputable def sampleOf {n : ℕ} (w : Fin (n + 1) → ℝ≥0∞) : ProbComp (Fin (n + 1)) :=
  if h : IsUnifSampleable w then
    h.choose_spec.choose <$> (liftM (unifSpec.query h.choose) : ProbComp _)
  else pure 0

lemma prob_sampleOf_bind {n : ℕ} {w : Fin (n + 1) → ℝ≥0∞} (hw : IsUnifSampleable w)
    (k : Fin (n + 1) → ProbComp β) (p : β → Prop) :
    prob (sampleOf w >>= k) p = ∑ i, w i * prob (k i) p := by
  classical
  have hspec := hw.choose_spec.choose_spec
  set b := hw.choose
  set f := hw.choose_spec.choose
  have h1 : sampleOf w >>= k = (liftM (unifSpec.query b) : ProbComp _) >>= fun j ↦ k (f j) := by
    simp [sampleOf, hw, b, f]
  rw [h1, prob_unif_query_bind,
    ← Finset.sum_fiberwise Finset.univ f fun j ↦ prob (k (f j)) p, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_congr rfl (g := fun _ ↦ prob (k i) p)
    (fun j hj ↦ by rw [(Finset.mem_filter.mp hj).2]),
    Finset.sum_const, nsmul_eq_mul, hspec i, div_eq_mul_inv]
  ring

/-- Nonnegative rational weights summing to one are sampleable with one uniform query. -/
lemma isUnifSampleable_of_rat {n : ℕ} (w : Fin (n + 1) → ℝ) (h0 : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) (hq : ∀ i, ∃ q : ℚ, w i = q) :
    IsUnifSampleable fun i ↦ ENNReal.ofReal (w i) := by
  classical
  choose q hq using hq
  have hq0 : ∀ i, 0 ≤ q i := fun i ↦ by have := h0 i; rw [hq i] at this; exact_mod_cast this
  have hq1 : ∑ i, q i = 1 := by
    have : ((∑ i, q i : ℚ) : ℝ) = 1 := by rw [← h1]; push_cast; exact Finset.sum_congr rfl fun i _ ↦ (hq i).symm
    exact_mod_cast this
  -- common denominator
  set D : ℕ := ∏ i, (q i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ ↦ (q i).den_pos
  choose e he using fun i ↦ Finset.dvd_prod_of_mem (fun i ↦ (q i).den) (Finset.mem_univ i)
  let a : Fin (n + 1) → ℕ := fun i ↦ (q i).num.toNat * e i
  have ha : ∀ i, q i = (a i : ℚ) / D := fun i ↦ by
    have hnum : ((q i).num.toNat : ℚ) = (q i).num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq0 i))
    have hden : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_nz
    have hDe : (D : ℚ) = (q i).den * e i := by rw [hD]; exact_mod_cast he i
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    have he0 : (e i : ℚ) ≠ 0 := by
      intro h; rw [h, mul_zero] at hDe; exact hD0 hDe
    calc q i = (q i).num / (q i).den := (Rat.num_div_den _).symm
      _ = (a i : ℚ) / D := by
        rw [div_eq_div_iff hden hD0, hDe]; simp only [a]; push_cast; rw [hnum]; ring
  have hsum : ∑ i, a i = D := by
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    have : (∑ i, (a i : ℚ)) = D := by
      have h := hq1
      simp only [ha, ← Finset.sum_div] at h
      rwa [div_eq_one_iff_eq hD0] at h
    exact_mod_cast this
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hDpos.ne'
  have hsum' : b + 1 = ∑ i, a i := by rw [hsum, hb]
  let E : Fin (b + 1) ≃ (Σ i, Fin (a i)) := (finCongr hsum').trans finSigmaFinEquiv.symm
  refine ⟨b, fun j ↦ (E j).1, fun i ↦ ?_⟩
  have hcard : (Finset.univ.filter fun j ↦ (E j).1 = i).card = a i := by
    rw [Finset.card_filter, Equiv.sum_comp E fun x ↦ if x.1 = i then 1 else 0,
      Fintype.sum_sigma]
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp
  have hbD : ((b : ℝ≥0∞) + 1) = (D : ℝ≥0∞) := by rw [hb]; push_cast; rfl
  change ENNReal.ofReal (w i) = _
  rw [hcard, hbD, hq i, ha i]
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  push_cast
  rw [ENNReal.ofReal_div_of_pos hDR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-! ## The classical strategy of a quantum machine -/

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- Born probabilities of the outcomes of the instrument `I` on the unnormalised state `ρ`. -/
noncomputable def bornW {n : ℕ} (I : SubInstrument W W (Fin (n + 1))) (ρ : Matrix W W ℂ) :
    Fin (n + 1) → ℝ≥0∞ :=
  fun i ↦ ENNReal.ofReal ((I.branch i ρ).trace.re / ρ.trace.re)

/-- All instrument nodes reachable from the unnormalised state `ρ` (following every classical
answer and every outcome) have rational outcome probabilities. -/
def RationalBorn (Q : QOC W spec α) : Matrix W W ℂ → Prop :=
  OracleComp.construct (C := fun _ ↦ Matrix W W ℂ → Prop) (fun _ _ ↦ True)
    (fun t _ ih ρ ↦
      match t, ih with
      | .inl j, ih =>
          (ρ.trace.re ≠ 0 →
            ∀ i, ∃ q : ℚ, (j.2.1.branch i ρ).trace.re / ρ.trace.re = (q : ℝ)) ∧
          ∀ i, ih i (j.2.1.branch i ρ)
      | .inr _, ih => ∀ u, ih u ρ) Q

@[simp] lemma rationalBorn_pure (a : α) (ρ : Matrix W W ℂ) :
    RationalBorn (pure a : QOC W spec α) ρ := trivial

lemma rationalBorn_instr_bind (j : InstrIdx W) (k : Fin (j.1 + 1) → QOC W spec α)
    (ρ : Matrix W W ℂ) :
    RationalBorn (liftM ((instrSpec W + spec).query (Sum.inl j)) >>= k) ρ ↔
      (ρ.trace.re ≠ 0 →
        ∀ i, ∃ q : ℚ, (j.2.1.branch i ρ).trace.re / ρ.trace.re = (q : ℝ)) ∧
      ∀ i, RationalBorn (k i) (j.2.1.branch i ρ) := Iff.rfl

lemma rationalBorn_query_bind (t : spec.Domain) (k : spec.Range t → QOC W spec α)
    (ρ : Matrix W W ℂ) :
    RationalBorn (liftM ((instrSpec W + spec).query (Sum.inr t)) >>= k) ρ ↔
      ∀ u, RationalBorn (k u) ρ := Iff.rfl

variable {ι' : Type} {spec' : OracleSpec ι'}

/-- Embed classical probabilistic code into computations with further oracles. -/
def liftL (oa : ProbComp α) : OracleComp (unifSpec + spec') α :=
  simulateQ (fun n ↦ liftM ((unifSpec + spec').query (Sum.inl n))) oa

/-- The classical strategy of the quantum machine `Q` started in the (unnormalised) state `ρ`:
each instrument node is replaced by a classical sample of its outcome with the Born
probabilities, after which the tracked state is updated to the post-measurement state. -/
noncomputable def toProbComp (Q : QOC W (unifSpec + spec') α) :
    Matrix W W ℂ → OracleComp (unifSpec + spec') α :=
  OracleComp.construct (C := fun _ ↦ Matrix W W ℂ → OracleComp (unifSpec + spec') α)
    (fun a _ ↦ pure a)
    (fun t _ ih ρ ↦
      match t, ih with
      | .inl j, ih => liftL (sampleOf (bornW j.2.1 ρ)) >>= fun i ↦ ih i (j.2.1.branch i ρ)
      | .inr t, ih => liftM ((unifSpec + spec').query t) >>= fun u ↦ ih u ρ) Q

@[simp] lemma toProbComp_pure (a : α) (ρ : Matrix W W ℂ) :
    toProbComp (pure a : QOC W (unifSpec + spec') α) ρ = pure a := rfl

lemma toProbComp_instr_bind (j : InstrIdx W) (k : Fin (j.1 + 1) → QOC W (unifSpec + spec') α)
    (ρ : Matrix W W ℂ) :
    toProbComp (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inl j)) >>= k) ρ =
      liftL (sampleOf (bornW j.2.1 ρ)) >>= fun i ↦ toProbComp (k i) (j.2.1.branch i ρ) := rfl

lemma toProbComp_query_bind (t : (unifSpec + spec').Domain)
    (k : (unifSpec + spec').Range t → QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbComp (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inr t)) >>= k) ρ =
      liftM ((unifSpec + spec').query t) >>= fun u ↦ toProbComp (k u) ρ := rfl

/-! ## Classical implementations that forward uniform sampling -/

/-- The implementation answers uniform-sampling queries by sampling, without touching its
state. -/
def ForwardsUnif (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp)) : Prop :=
  ∀ (n : ℕ) (s : σ),
    (impl (Sum.inl n)).run s = (fun u ↦ (u, s)) <$> (liftM (unifSpec.query n) : ProbComp _)

lemma ForwardsUnif.run_simulateQ_liftL {impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp)}
    (h : ForwardsUnif impl) (oa : ProbComp γ) (s : σ) :
    (simulateQ impl (liftL oa)).run s = (fun u ↦ (u, s)) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [liftL]
  | query_bind n k ih =>
    have : (liftL (liftM (unifSpec.query n) >>= k) : OracleComp (unifSpec + spec') γ) =
        liftM ((unifSpec + spec').query (Sum.inl n)) >>= fun i ↦ liftL (k i) := by
      simp [liftL]
    rw [this, simulateQ_bind, StateT.run_bind, simulateQ_spec_query, h n s]
    simp [ih]

lemma ForwardsUnif.run_simulateQ_liftL_bind
    {impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp)} (h : ForwardsUnif impl)
    (oa : ProbComp γ) (K : γ → OracleComp (unifSpec + spec') α) (s : σ) :
    (simulateQ impl (liftL oa >>= K)).run s = oa >>= fun u ↦ (simulateQ impl (K u)).run s := by
  rw [simulateQ_bind, StateT.run_bind, h.run_simulateQ_liftL]
  simp

/-! ## The collapse theorem -/

/-- **Collapse, continuation form.**  Let `impl` be any classical stateful probabilistic
implementation of the oracles of `Q` (forwarding uniform sampling), and let the continuation
`f` (a closed machine reading the output and final oracle state) collapse to the classical
continuation `g`.  Then the Born weight of the closed composite equals `tr ρ` times the classical
probability of the composite of the classical strategy `Q.toProbComp ρ` run against `impl`. -/
theorem qWeight_close_bind (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ForwardsUnif impl) (p : β → Prop) [DecidablePred p]
    (f : α × σ → Closed W β) (g : α × σ → ProbComp β)
    (hfg : ∀ x (ρ' : Matrix W W ℂ), ρ'.PosSemidef →
      qWeight p (f x) ρ' = ENNReal.ofReal ρ'.trace.re * prob (g x) p)
    (Q : QOC W (unifSpec + spec') α) (s : σ) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (hQ : RationalBorn Q ρ) :
    qWeight p (close impl Q s >>= f) ρ =
      ENNReal.ofReal ρ.trace.re *
        prob ((simulateQ impl (toProbComp Q ρ)).run s >>= g) p := by
  induction Q using OracleComp.inductionOn generalizing s ρ with
  | pure a => simpa using hfg (a, s) ρ hρ
  | query_bind t k ih =>
    rcases t with j | t
    · -- instrument node
      rw [rationalBorn_instr_bind] at hQ
      rw [close_instr_bind, bind_assoc, qWeight_instr_bind, toProbComp_instr_bind,
        himpl.run_simulateQ_liftL_bind, bind_assoc]
      simp only [ih _ _ _ (posSemidef_branch j _ hρ) (hQ.2 _)]
      have hnn : ∀ i, 0 ≤ (j.2.1.branch i ρ).trace.re := fun i ↦
        (posSemidef_branch j i hρ).trace_re_nonneg
      have hsum : ∑ i, (j.2.1.branch i ρ).trace.re = ρ.trace.re := by
        rw [← Complex.re_sum]
        exact congrArg Complex.re (j.2.2.sum_trace_eq (s := Finset.univ) (by simp) ρ)
      by_cases hc : ρ.trace.re = 0
      · have h0 : ∀ i, (j.2.1.branch i ρ).trace.re = 0 := fun i ↦
          (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnn i).mp (hsum.trans hc) i
            (Finset.mem_univ i)
        simp [h0, hc]
      · have hcpos : 0 < ρ.trace.re := lt_of_le_of_ne hρ.trace_re_nonneg (Ne.symm hc)
        have hsamp : IsUnifSampleable (bornW j.2.1 ρ) :=
          isUnifSampleable_of_rat _ (fun i ↦ div_nonneg (hnn i) hcpos.le)
            (by rw [← Finset.sum_div, hsum, div_self hc]) (hQ.1 hc)
        rw [prob_sampleOf_bind hsamp, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← mul_assoc, bornW, ← ENNReal.ofReal_mul hcpos.le, mul_div_cancel₀ _ hc]
    · -- classical query
      rw [rationalBorn_query_bind] at hQ
      rw [close_query_bind, bind_assoc, toProbComp_query_bind, simulateQ_bind, StateT.run_bind,
        simulateQ_spec_query, bind_assoc]
      exact qWeight_liftU_bind p _ _ _ _ ρ fun x ↦ ih _ _ _ hρ (hQ _)

/-- **Collapse (T1).**  For every classical stateful probabilistic oracle implementation `impl`
(forwarding uniform sampling), every positive semidefinite initial state `ρ` and every machine
`Q` with rational Born probabilities from `ρ`, the Born weight of an event of the closed quantum
machine is `tr ρ` times the probability of the event when `impl` is run on the classical
strategy `Q.toProbComp ρ`. -/
theorem qWeight_close_eq_mul (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ForwardsUnif impl) (p : α × σ → Prop) [DecidablePred p]
    (Q : QOC W (unifSpec + spec') α) (s : σ) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (hQ : RationalBorn Q ρ) :
    qWeight p (close impl Q s) ρ =
      ENNReal.ofReal ρ.trace.re * prob ((simulateQ impl (toProbComp Q ρ)).run s) p := by
  have := qWeight_close_bind impl himpl p pure pure
    (fun x ρ' _ ↦ by simp) Q s ρ hρ hQ
  simpa using this

/-- **Collapse (T1), normalised state.** -/
theorem qWeight_close_eq (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ForwardsUnif impl) (p : α × σ → Prop) [DecidablePred p]
    (Q : QOC W (unifSpec + spec') α) (s : σ) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) (hQ : RationalBorn Q ρ) :
    qWeight p (close impl Q s) ρ =
      Pr{let y ← (simulateQ impl (toProbComp Q ρ)).run s}[p y] := by
  rw [qWeight_close_eq_mul impl himpl p Q s ρ hρ hQ, h1, prob_def]
  simp

end PQ.Interactive

open PQ.Interactive in
#print axioms qWeight_close_bind
open PQ.Interactive in
#print axioms qWeight_close_eq
