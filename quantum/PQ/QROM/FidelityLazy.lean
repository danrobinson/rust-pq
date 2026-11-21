import PQ.QROM.FidelityGen

/-!
# Lazy sampling at fresh indices is eager pre-sampling

VCVio's challenge oracles (SM-DT-PRE, SM-DT-UD, …) draw a fresh uniform value `x ← M` at every
accepted challenge; the exact QROM games pre-sample a table `xs : T → M` and average outside.
This file proves, for classical computations, that the two give the same probability.

Setting: a stateful randomised oracle implementation `impl : QueryImpl spec (StateT S ProbComp)`
and a family of deterministic steps `eag xs : (t : spec.Domain) → S → spec.Range t × S`, such
that every step of `impl` at a state `s` either is deterministic and agrees with `eag xs` for
every table (`FidLazyStep`, first alternative), or draws `x ← $ᵗ M` and then does what `eag xs`
does with `xs i = x`, for an index `i` that is dead afterwards (second alternative).  A dead
index stays dead and is never read again (`hdead`, `hind`).

`fidLazy_eq_eager`: for every continuation `cont`,
`Pr[(simulateQ impl oa).run s >>= cont] = avg_xs Pr[cont (fidEagRun (eag xs) oa s)]`.
-/

open OracleComp OracleSpec ENNReal

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {T M : Type} [Fintype T] [DecidableEq T] [Fintype M]

/-- Splitting off one coordinate of a uniform table: if `H x ·` does not depend on the
coordinate `i`, the average of `H (xs i) xs` over tables is the average over an independent
value `x` and a table. -/
theorem avg_coord [Nonempty M] (i : T) (H : M → (T → M) → ℝ≥0∞)
    (hH : ∀ x xs x', H x (Function.update xs i x') = H x xs) :
    (avg fun xs : T → M ↦ H (xs i) xs) = avg fun x : M ↦ avg fun xs : T → M ↦ H x xs := by
  let F : (T → M) → ℝ≥0∞ := fun xs ↦ H (xs i) xs
  have h1 : ∀ x xs, H x xs = F (Function.update xs i x) := fun x xs ↦ by
    simp only [F, Function.update_self]
    exact (hH x xs x).symm
  let sw : M × (T → M) → M × (T → M) := fun p ↦ (p.2 i, Function.update p.2 i p.1)
  have hsw : Function.Involutive sw := fun p ↦ by
    simp [sw]
  have e : ∑ p : M × (T → M), F (Function.update p.2 i p.1) = ∑ p : M × (T → M), F p.2 :=
    Equiv.sum_comp hsw.toPerm fun p ↦ F p.2
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at e
  have h2 : (fun x : M ↦ avg fun xs : T → M ↦ H x xs) =
      fun x ↦ avg fun xs ↦ F (Function.update xs i x) := by
    funext x
    exact avg_congr (h1 x)
  rw [h2]
  change avg F = _
  unfold avg
  simp only [Finset.mul_sum]
  simp only [← mul_assoc, ← Finset.mul_sum]
  simp only at e
  rw [e]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_comm (Fintype.card M : ℝ≥0∞)⁻¹, mul_assoc,
    ← mul_assoc _ (Fintype.card M : ℝ≥0∞),
    ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]

theorem avg_const' {T' : Type} [Fintype T'] [Nonempty T'] (c : ℝ≥0∞) :
    avg (fun _ : T' ↦ c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {S α : Type}

/-- The deterministic run of `oa` with the step function `step`. -/
def fidEagRun (step : (t : spec.Domain) → S → spec.Range t × S) :
    OracleComp spec α → S → α × S :=
  OracleComp.construct (C := fun _ ↦ S → α × S) (fun a s ↦ (a, s))
    (fun t _ ih s ↦ ih (step t s).1 (step t s).2)

variable [SampleableType M]

/-- One step of the lazy implementation at the state `s`, against the eager steps: either
deterministic, or a fresh uniform draw at an index that is dead afterwards. -/
def FidLazyStep (impl : QueryImpl spec (StateT S ProbComp))
    (eag : (T → M) → (t : spec.Domain) → S → spec.Range t × S) (dead : S → T → Prop)
    (t : spec.Domain) (s : S) : Prop :=
  (∀ xs, (impl t).run s = pure (eag xs t s)) ∨
    ∃ (i : T) (g : M → spec.Range t × S),
      (impl t).run s = (($ᵗ M : ProbComp M) >>= fun x ↦ pure (g x)) ∧
        (∀ xs, eag xs t s = g (xs i)) ∧ ∀ x, dead (g x).2 i

variable {impl : QueryImpl spec (StateT S ProbComp)}
  {eag : (T → M) → (t : spec.Domain) → S → spec.Range t × S} {dead : S → T → Prop}

/-- A dead index is not read: the eager run does not depend on the table at a dead index. -/
theorem fidEagRun_update
    (hdead : ∀ xs t s i, dead s i → dead (eag xs t s).2 i)
    (hind : ∀ xs t s i x, dead s i → eag (Function.update xs i x) t s = eag xs t s)
    (oa : OracleComp spec α) (xs : T → M) (s : S) (i : T) (x : M) (hs : dead s i) :
    fidEagRun (eag (Function.update xs i x)) oa s = fidEagRun (eag xs) oa s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    change fidEagRun (eag (Function.update xs i x)) (k (eag (Function.update xs i x) t s).1)
      (eag (Function.update xs i x) t s).2 = fidEagRun (eag xs) (k (eag xs t s).1) (eag xs t s).2
    rw [hind xs t s i x hs]
    exact ih _ _ (hdead xs t s i hs)

/-- **Lazy sampling at fresh indices is eager pre-sampling.** -/
theorem fidLazy_eq_eager [Nonempty M]
    (hstep : ∀ t s, FidLazyStep impl eag dead t s)
    (hdead : ∀ xs t s i, dead s i → dead (eag xs t s).2 i)
    (hind : ∀ xs t s i x, dead s i → eag (Function.update xs i x) t s = eag xs t s)
    (oa : OracleComp spec α) (s : S) (cont : α × S → ProbComp Bool) :
    fidPr ((simulateQ impl oa).run s >>= cont) =
      avg fun xs : T → M ↦ fidPr (cont (fidEagRun (eag xs) oa s)) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    rw [simulateQ_pure, StateT.run_pure, pure_bind]
    exact (avg_const' _).symm
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    have hR : ∀ xs, fidEagRun (eag xs) (liftM (OracleSpec.query t) >>= k) s =
        fidEagRun (eag xs) (k (eag xs t s).1) (eag xs t s).2 := fun xs ↦ rfl
    simp only [hR]
    rcases hstep t s with hd | ⟨i, g, hrun, hg, hgd⟩
    · obtain ⟨xs₀⟩ := (inferInstance : Nonempty (T → M))
      rw [hd xs₀, pure_bind, ih]
      refine avg_congr fun xs ↦ ?_
      have : eag xs t s = eag xs₀ t s :=
        (OracleComp.pure_inj _ _).1 ((hd xs).symm.trans (hd xs₀))
      rw [this]
    · rw [hrun, bind_assoc]
      simp only [pure_bind]
      rw [fidPr_uniform_bind]
      simp only [ih, hg]
      exact (avg_coord i (fun x xs ↦ fidPr (cont (fidEagRun (eag xs) (k (g x).1) (g x).2)))
        fun x xs x' ↦ by
          rw [fidEagRun_update hdead hind _ xs _ i x' (hgd x)]).symm

end PQ.QROM

#print axioms PQ.QROM.fidLazy_eq_eager
