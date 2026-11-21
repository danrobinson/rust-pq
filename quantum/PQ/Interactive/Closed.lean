import PQ.Interactive.Wrap

/-!
# Classical strategies of closed machines

A closed machine (`Closed W α = QOC W unifSpec α`: instrument nodes and uniform sampling only) with
rational Born probabilities has a classical strategy `toProbCompC X ρ : ProbComp α`.

* `qWeight_bind_closed`: the Born weight of an event of a closed machine (followed by a
  continuation that collapses) is the classical probability for its classical strategy;
* `toProbCompC_close`: closing an open machine and then classicalising *is* running the oracle
  implementation on the classical strategy of the open machine (equality of programs), so the
  collapse theorem of `Collapse.lean` factors through these two facts;
* pre/post-processing lemmas.

This is what multi-stage games need: a phase in which a quantum machine runs without game oracles
is a closed machine.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}
variable {ι' : Type} {spec' : OracleSpec ι'} {σ : Type}

/-- The classical strategy of a closed machine started in the state `ρ`. -/
noncomputable def toProbCompC (X : Closed W α) : Matrix W W ℂ → ProbComp α :=
  OracleComp.construct (C := fun _ ↦ Matrix W W ℂ → ProbComp α)
    (fun a _ ↦ pure a)
    (fun t _ ih ρ ↦
      match t, ih with
      | .inl j, ih => sampleOf (bornW j.2.1 ρ) >>= fun i ↦ ih i (j.2.1.branch i ρ)
      | .inr n, ih => liftM (unifSpec.query n) >>= fun u ↦ ih u ρ) X

@[simp] lemma toProbCompC_pure (a : α) (ρ : Matrix W W ℂ) :
    toProbCompC (pure a : Closed W α) ρ = pure a := rfl

lemma toProbCompC_instr_bind (j : InstrIdx W) (k : Fin (j.1 + 1) → Closed W α)
    (ρ : Matrix W W ℂ) :
    toProbCompC (liftM ((instrSpec W + unifSpec).query (Sum.inl j)) >>= k) ρ =
      sampleOf (bornW j.2.1 ρ) >>= fun i ↦ toProbCompC (k i) (j.2.1.branch i ρ) := rfl

lemma toProbCompC_unif_bind (n : ℕ) (k : Fin (n + 1) → Closed W α) (ρ : Matrix W W ℂ) :
    toProbCompC (liftM ((instrSpec W + unifSpec).query (Sum.inr n)) >>= k) ρ =
      liftM (unifSpec.query n) >>= fun u ↦ toProbCompC (k u) ρ := rfl

/-- Classical pre-processing commutes with classicalisation. -/
lemma toProbCompC_liftU_bind (oa : ProbComp γ) (F : γ → Closed W α) (ρ : Matrix W W ℂ) :
    toProbCompC (liftU oa >>= F) ρ = oa >>= fun x ↦ toProbCompC (F x) ρ := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    rw [liftU_query_bind, bind_assoc, toProbCompC_unif_bind, bind_assoc]
    simp only [ih]

@[simp] lemma toProbCompC_liftU (oa : ProbComp α) (ρ : Matrix W W ℂ) :
    toProbCompC (liftU oa : Closed W α) ρ = oa := by
  simpa using toProbCompC_liftU_bind oa (pure : α → Closed W α) ρ

/-- Classical post-processing commutes with classicalisation. -/
lemma toProbCompC_bind_liftU (X : Closed W α) (post : α → ProbComp β) (ρ : Matrix W W ℂ) :
    toProbCompC (X >>= fun a ↦ liftU (post a)) ρ = toProbCompC X ρ >>= post := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | n
    · rw [bind_assoc, toProbCompC_instr_bind, toProbCompC_instr_bind, bind_assoc]
      simp only [ih]
    · rw [bind_assoc, toProbCompC_unif_bind, toProbCompC_unif_bind, bind_assoc]
      simp only [ih]

lemma rationalBorn_liftU_bind (oa : ProbComp γ) (F : γ → Closed W α) (ρ : Matrix W W ℂ)
    (h : ∀ x, RationalBorn (F x) ρ) : RationalBorn (liftU oa >>= F) ρ :=
  rationalBorn_liftQ_bind (spec := unifSpec) oa F ρ h

lemma rationalBorn_bind_liftU (X : Closed W α) (post : α → ProbComp β) (ρ : Matrix W W ℂ)
    (h : RationalBorn X ρ) : RationalBorn (X >>= fun a ↦ liftU (post a)) ρ :=
  rationalBorn_bind_liftQ (spec := unifSpec) X post ρ h

/-- **Collapse of a closed machine, continuation form.** -/
theorem qWeight_bind_closed (p : β → Prop) [DecidablePred p]
    (f : α → Closed W β) (g : α → ProbComp β)
    (hfg : ∀ x (ρ' : Matrix W W ℂ), ρ'.PosSemidef →
      qWeight p (f x) ρ' = ENNReal.ofReal ρ'.trace.re * prob (g x) p)
    (X : Closed W α) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (hX : RationalBorn X ρ) :
    qWeight p (X >>= f) ρ = ENNReal.ofReal ρ.trace.re * prob (toProbCompC X ρ >>= g) p := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => simpa using hfg a ρ hρ
  | query_bind t k ih =>
    rcases t with j | n
    · rw [rationalBorn_instr_bind] at hX
      rw [bind_assoc, qWeight_instr_bind, toProbCompC_instr_bind, bind_assoc]
      simp only [ih _ _ (posSemidef_branch j _ hρ) (hX.2 _)]
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
            (by rw [← Finset.sum_div, hsum, div_self hc]) (hX.1 hc)
        rw [prob_sampleOf_bind hsamp, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← mul_assoc, bornW, ← ENNReal.ofReal_mul hcpos.le, mul_div_cancel₀ _ hc]
    · rw [rationalBorn_query_bind] at hX
      rw [bind_assoc, qWeight_unif_bind, toProbCompC_unif_bind, bind_assoc,
        prob_unif_query_bind, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [ih _ _ hρ (hX _), mul_left_comm]

/-- **Collapse of a closed machine.** -/
theorem qWeight_closed (p : α → Prop) [DecidablePred p] (X : Closed W α) (ρ : Matrix W W ℂ)
    (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) (hX : RationalBorn X ρ) :
    qWeight p X ρ = Pr{let y ← toProbCompC X ρ}[p y] := by
  have := qWeight_bind_closed p pure pure (fun x ρ' _ ↦ by simp) X ρ hρ hX
  simpa [h1, prob_def] using this

/-- **Closing commutes with classicalisation.**  The classical strategy of the closed machine
`close impl Q s` is the implementation `impl` run on the classical strategy of `Q`. -/
theorem toProbCompC_close (impl : QueryImpl (unifSpec + spec') (StateT σ ProbComp))
    (himpl : ForwardsUnif impl) (Q : QOC W (unifSpec + spec') α) (s : σ) (ρ : Matrix W W ℂ) :
    toProbCompC (close impl Q s) ρ = (simulateQ impl (toProbComp Q ρ)).run s := by
  induction Q using OracleComp.inductionOn generalizing s ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | t
    · rw [close_instr_bind, toProbCompC_instr_bind, toProbComp_instr_bind,
        himpl.run_simulateQ_liftL_bind]
      simp only [ih]
    · rw [close_query_bind, toProbCompC_liftU_bind, toProbComp_query_bind, simulateQ_bind,
        StateT.run_bind, simulateQ_spec_query]
      simp only [ih]

/-- Closing preserves rationality of the Born probabilities. -/
theorem rationalBorn_close {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (Q : QOC W spec α) (s : σ) (ρ : Matrix W W ℂ)
    (h : RationalBorn Q ρ) : RationalBorn (close impl Q s) ρ := by
  induction Q using OracleComp.inductionOn generalizing s ρ with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [rationalBorn_instr_bind] at h
      rw [close_instr_bind, rationalBorn_instr_bind]
      exact ⟨h.1, fun i ↦ ih i _ _ (h.2 i)⟩
    · rw [rationalBorn_query_bind] at h
      rw [close_query_bind]
      exact rationalBorn_liftU_bind _ _ _ fun x ↦ ih _ _ _ (h _)

end PQ.Interactive

open PQ.Interactive in
#print axioms qWeight_bind_closed
open PQ.Interactive in
#print axioms toProbCompC_close
