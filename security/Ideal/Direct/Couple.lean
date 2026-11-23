import Ideal.Direct.RomGhost

/-!
# Coupling two stateful handlers through a joint handler (`status/DIRECT.md` §13)

The generic tool for the core.  A **joint handler** `J` on a state `σ` carries the states of two
handlers `h₁` (on `σ₁ = π₁ σ`) and `h₂` (on `σ₂ = π₂ σ`).  Assume

* (`hm`) the `σ₁`-marginal of every step of `J` IS the step of `h₁` (in distribution), on the
  states of an invariant `I` that `J` preserves;
* (`hd`) `J` is dominated by `h₂` through `π₂` until `bad` (VCVio's `DominatedUntilBad`: off
  `bad`, the answers and the `σ₂`-part of a step of `J` are a step of `h₂`).

Then (**`coupling_le`**) for every program, every final kernel `F` on `σ₁` and every event `A` of
its output,
```
Pr_h₁[win ∧ A (F σ₁)] ≤ Pr_h₂[win] + Pr_J[bad ∧ A (F (π₁ σ))].
```
The marginal statement is `map_run_eqD_of_step`.  Unlike `Engine.prEvent_le_untilBad`, `h₁` is
not a projection of `h₂`: the joint step may sample `h₂`'s randomness from `h₁`'s (a coupling).
-/

open OracleComp OracleSpec ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct

section Couple

variable {ι : Type} {spec : OracleSpec ι} {σ σ₁ σ₂ : Type}

/-- **The marginal of a joint run.** -/
theorem map_run_eqD_of_step (J : QueryImpl spec (StateT σ ProbComp))
    (h₁ : QueryImpl spec (StateT σ₁ ProbComp)) (π : σ → σ₁) (I : σ → Prop)
    (hI : QueryImpl.PreservesInv J I)
    (hm : ∀ t s, I s → (fun z => (z.1, π z.2)) <$> (J t).run s =ᵈ (h₁ t).run (π s))
    {α : Type} (oa : OracleComp spec α) (s : σ) (hs : I s) :
    (fun z => (z.1, π z.2)) <$> (simulateQ J oa).run s =ᵈ (simulateQ h₁ oa).run (π s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact EvalDistEq.refl _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    refine (OracleComp.EvalDistEq.bind_congr_of_support _ fun z hz => ih z.1 z.2 (hI t s hs z hz)).trans ?_
    have e : ((J t).run s >>= fun z => (simulateQ h₁ (k z.1)).run (π z.2)) =
        ((fun z => (z.1, π z.2)) <$> (J t).run s) >>= fun z => (simulateQ h₁ (k z.1)).run z.2 := by
      rw [bind_map_left]
    rw [e]
    exact EvalDistEq.bind_left (hm t s hs) _

/-- Events of a run followed by a kernel, as an event of one computation. -/
theorem prEvent_run_kernel {α β : Type} (X : ProbComp α) (F : α → ProbComp β)
    (E : α → β → Prop) :
    Pr{let z ← X; let w ← F z}[E z w] =
      Pr{let p ← X >>= fun z => (fun w => (z, w)) <$> F z}[E p.1 p.2] := by
  simp only [prEvent_norm]

/-- **Coupling through a joint handler.** -/
theorem coupling_le (J : QueryImpl spec (StateT σ ProbComp))
    (h₁ : QueryImpl spec (StateT σ₁ ProbComp)) (h₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (π₁ : σ → σ₁) (π₂ : σ → σ₂) (I bad : σ → Prop)
    (hI : QueryImpl.PreservesInv J I) (hbad : QueryImpl.PreservesInv J bad)
    (hm : ∀ t s, I s → (fun z => (z.1, π₁ z.2)) <$> (J t).run s =ᵈ (h₁ t).run (π₁ s))
    (hd : QueryImpl.DominatedUntilBad J h₂ π₂ I bad)
    (oa : OracleComp spec Bool) (s : σ) (hs : I s) {β : Type} (F : σ₁ → ProbComp β)
    (A : β → Prop) :
    Pr{let z ← (simulateQ h₁ oa).run (π₁ s); let w ← F z.2}[z.1 = true ∧ A w] ≤
      Pr{let z ← (simulateQ h₂ oa).run (π₂ s)}[z.1 = true] +
        Pr{let z ← (simulateQ J oa).run s; let w ← F (π₁ z.2)}[bad z.2 ∧ A w] := by
  have hmar := map_run_eqD_of_step J h₁ π₁ I hI hm oa s hs
  -- the left side is an event of the joint run
  have h1 : Pr{let z ← (simulateQ h₁ oa).run (π₁ s); let w ← F z.2}[z.1 = true ∧ A w] =
      Pr{let z ← (simulateQ J oa).run s; let w ← F (π₁ z.2)}[z.1 = true ∧ A w] := by
    rw [prEvent_run_kernel, prEvent_run_kernel]
    have hb := (EvalDistEq.symm hmar).bind_left
      (fun z => (fun w => (z, w)) <$> F z.2)
    rw [bind_map_left] at hb
    have := hb.prEvent_eq (fun p => p.1.1 = true ∧ A p.2)
    rw [this]
    have e : ((simulateQ J oa).run s >>= fun z => (fun w => ((z.1, π₁ z.2), w)) <$> F (π₁ z.2)) =
        (fun p => ((p.1.1, π₁ p.1.2), p.2)) <$>
          ((simulateQ J oa).run s >>= fun z => (fun w => (z, w)) <$> F (π₁ z.2)) := by
      simp only [map_bind, Functor.map_map]
    rw [e, prEvent_map]
  rw [h1]
  -- split on `bad`
  have h2 : Pr{let z ← (simulateQ J oa).run s; let w ← F (π₁ z.2)}[z.1 = true ∧ A w] ≤
      Pr{let z ← (simulateQ J oa).run s; let w ← F (π₁ z.2)}[z.1 = true ∧ ¬ bad z.2] +
        Pr{let z ← (simulateQ J oa).run s; let w ← F (π₁ z.2)}[bad z.2 ∧ A w] := by
    rw [prEvent_run_kernel, prEvent_run_kernel, prEvent_run_kernel]
    refine (prEvent_mono _ _ _ fun p hp => ?_).trans (prEvent_or_le _ _ _)
    by_cases hb : bad p.1.2
    · exact .inr ⟨hb, hp.2⟩
    · exact .inl ⟨hp.1, hb⟩
  refine h2.trans (add_le_add ?_ le_rfl)
  refine (Rom.prEvent_bind_drop _ _ _ (fun z : Bool × σ => z.1 = true ∧ ¬ bad z.2)
    fun _ _ _ _ h => h).trans ?_
  have := hd.prEvent_simulateQ_run_map_and_not_bad_le hI hbad oa s hs (fun z => z.1 = true)
  exact this

end Couple

end Ideal.Direct

#print axioms Ideal.Direct.map_run_eqD_of_step
#print axioms Ideal.Direct.coupling_le
