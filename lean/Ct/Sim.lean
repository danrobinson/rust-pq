import Ct.Rel

/-!
# One-sided simulation

The signing theorems say: *if the signer returns with trace `t`, then the simulator (a program
that is given no secret) returns with the same trace `t`*. The tools:

* `Rel.sim`: a `Rel` lemma turns a returning run of one side into a returning run of the other
  with the same trace, once the other side is known to return (from the functional theorems,
  through erasure).
* `loop_sim`: the loop rule for this one-sided judgment, whose invariant may refer to the final
  result of the first loop (the published signature), and whose body obligation may assume
  that the rest of the first loop returns that result.
* Inversion lemmas for returning runs.
-/

open Aeneas Aeneas.Std Lean.Order

namespace Ct

namespace Leak

theorem pure_bind {α : Type u} {β : Type v} (a : α) (f : α → Leak β) :
    Leak.bind (Leak.pure a) f = f a := by
  apply Leak.ext
  rw [Leak.run_bind]
  simp only [Leak.run_pure, bind_ok, List.nil_append]
  rcases Result.cases_flat (f a).run with ⟨⟨b, t⟩, h⟩ | ⟨e, h⟩ | h <;> rw [h] <;> simp

theorem pure_eq_ok {α : Type u} {a b : α} {t : Trace} :
    (Leak.pure a).run = .ok (b, t) ↔ a = b ∧ t = [] := by
  simp only [run_pure, Result.ok.injEq, Prod.mk.injEq]
  exact and_congr Iff.rfl eq_comm

theorem emit_eq_ok {t t' : Trace} {u : Unit} : (Leak.emit t).run = .ok (u, t') ↔ t' = t := by
  cases u
  simp only [run_emit, Result.ok.injEq, Prod.mk.injEq, true_and]
  exact eq_comm

theorem cond_eq_ok {α : Type u} {c : Prop} [Decidable c] {a b : Leak α} {x : α} {t : Trace} :
    (Leak.cond c a b).run = .ok (x, t) ↔
      ∃ t', t = .branch (decide c) :: t' ∧ (if c then a else b).run = .ok (x, t') := by
  rw [cond_eq, bind_eq_ok]
  constructor
  · rintro ⟨u, t₁, t₂, h1, h2, rfl⟩
    rw [emit_eq_ok] at h1; subst h1
    exact ⟨t₂, rfl, h2⟩
  · rintro ⟨t', rfl, h⟩
    exact ⟨(), _, t', rfl, h, rfl⟩

theorem run_ok_of_erase {α : Type u} {m : Leak α} {a : α} (h : m.erase = .ok a) :
    ∃ t, m.run = .ok (a, t) := erase_eq_ok.mp h

theorem run_ok_det {α : Type u} {m : Leak α} {a b : α} {t t' : Trace}
    (h1 : m.run = .ok (a, t)) (h2 : m.run = .ok (b, t')) : a = b ∧ t = t' := by
  rw [h1] at h2
  simp only [Result.ok.injEq, Prod.mk.injEq] at h2
  exact h2

end Leak

namespace Rel

/-- From a `Rel` lemma, a returning run of the first program, and the fact that the second
returns (its erasure is `ok`): the second returns with the same trace. -/
theorem sim {α : Type u} {β : Type v} {m : Leak α} {m' : Leak β} {R : α → β → Prop}
    (h : Rel m m' R) {a : α} {t : Trace} (h1 : m.run = .ok (a, t)) {b : β}
    (h2 : m'.erase = .ok b) : m'.run = .ok (b, t) ∧ R a b := by
  obtain ⟨t', ht'⟩ := Leak.erase_eq_ok.mp h2
  obtain ⟨rfl, hR⟩ := h a t b t' h1 ht'
  exact ⟨ht', hR⟩

end Rel

/-- The one-sided loop rule with an invariant that may depend on the final result `r` of the
first loop. -/
theorem loop_sim {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    {body : α → Leak (ControlFlow α β)} {body' : γ → Leak (ControlFlow γ δ)}
    (r : β) (I : α → γ → Prop) (Q : β → δ → Prop)
    (hbody : ∀ x x' c t₁, I x x' → (body x).run = .ok (c, t₁) →
      (∀ y, c = .cont y → ∃ t₂, (Leak.loop body y).run = .ok (r, t₂)) →
      (∀ b, c = .done b → b = r) →
      ∃ c', (body' x').run = .ok (c', t₁) ∧ CFRel I Q c c') :
    ∀ x t, (Leak.loop body x).run = .ok (r, t) → ∀ x', I x x' →
      ∃ b', (Leak.loop body' x').run = .ok (b', t) ∧ Q r b' := by
  have key : ∀ x b t, (Leak.loop body x).run = .ok (b, t) →
      (Leak.loop body x).run = .ok (r, t) → ∀ x', I x x' →
      ∃ b', (Leak.loop body' x').run = .ok (b', t) ∧ Q r b' := by
    refine Leak.loop.fixpoint_induct body
      (fun F => ∀ x b t, (F x).run = .ok (b, t) →
        (Leak.loop body x).run = .ok (r, t) → ∀ x', I x x' →
        ∃ b', (Leak.loop body' x').run = .ok (b', t) ∧ Q r b') ?_ ?_
    · exact admissible_pi_apply _ fun x =>
        Leak.admissible_leak_ok (fun b t => (Leak.loop body x).run = .ok (r, t) → ∀ x', I x x' →
          ∃ b', (Leak.loop body' x').run = .ok (b', t) ∧ Q r b')
    · intro F ih x b t h hreal x' hI
      obtain ⟨c, t₁, t₂, hc, hk, rfl⟩ := Leak.bind_eq_ok.mp h
      rw [Leak.loop_unfold] at hreal
      obtain ⟨c₀, t₁', t₂', hc', hk', ht⟩ := Leak.bind_eq_ok.mp hreal
      obtain ⟨rfl, rfl⟩ := Leak.run_ok_det hc hc'
      have ht2 : t₂ = t₂' := List.append_cancel_left ht
      subst ht2
      obtain ⟨c', hc'', hR⟩ := hbody x x' c t₁ hI hc
        (fun y hy => by subst hy; exact ⟨t₂, hk'⟩)
        (fun b' hb => by
          subst hb
          simp only [Leak.run_pure, Result.ok.injEq, Prod.mk.injEq] at hk'
          exact hk'.1)
      rw [Leak.loop_unfold]
      cases c with
      | cont y =>
        cases c' with
        | cont y' =>
          obtain ⟨b', hb', hQ⟩ := ih y b t₂ hk hk' y' hR
          exact ⟨b', Leak.bind_eq_ok.mpr ⟨_, t₁, t₂, hc'', hb', rfl⟩, hQ⟩
        | done _ => exact hR.elim
      | done d =>
        cases c' with
        | cont _ => exact hR.elim
        | done d' =>
          simp only [Leak.run_pure, Result.ok.injEq, Prod.mk.injEq] at hk'
          obtain ⟨rfl, rfl⟩ := hk'
          exact ⟨d', Leak.bind_eq_ok.mpr ⟨_, t₁, [], hc'', rfl, rfl⟩, hR⟩
  intro x t h x' hI
  exact key x r t h h x' hI

/-- "Every returning run from a state satisfies `P`", by fixpoint induction: a functional
property of loops (used for facts like "the final signature extends the current one"). -/
theorem loop_post {α : Type u} {β : Type v} {body : α → Leak (ControlFlow α β)}
    (P : α → β → Prop)
    (hstep : ∀ x c t₁, (body x).run = .ok (c, t₁) →
      (∀ y b, c = .cont y → P y b → P x b) ∧ (∀ b, c = .done b → P x b)) :
    ∀ x b t, (Leak.loop body x).run = .ok (b, t) → P x b := by
  refine Leak.loop.fixpoint_induct body
    (fun F => ∀ x b t, (F x).run = .ok (b, t) → P x b) ?_ ?_
  · exact admissible_pi_apply _ fun x => Leak.admissible_leak_ok (fun b _ => P x b)
  · intro F ih x b t h
    obtain ⟨c, t₁, t₂, hc, hk, rfl⟩ := Leak.bind_eq_ok.mp h
    have := hstep x c t₁ hc
    cases c with
    | cont y => exact this.1 y b rfl (ih y b t₂ hk)
    | done d =>
      simp only [Leak.run_pure, Result.ok.injEq, Prod.mk.injEq] at hk
      exact this.2 b (by rw [hk.1])

end Ct
