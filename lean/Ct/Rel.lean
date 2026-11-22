import Ct.Model

/-!
# A relational logic for the leakage monad

`Rel m m' R` (read: `m` and `m'` are *trace-equivalent with results related by `R`*) says that
if both computations return, they emitted the same trace and their results are related by `R`.
It is a partial-correctness judgment: termination (absence of failure and divergence) comes from
the functional-correctness theorems of `Slhdsa/Proofs` via erasure (`Ct/Erase.lean`).

Constant time for a function `f` is stated as

  `public args = public args' → Rel (f args) (f args') R`

where `R` says which parts of the results are again public-equal (equal, or of equal length),
so that the lemma composes in the caller.

The rules are syntax-directed: both programs are the same instrumented text applied to different
arguments, so they are stepped in lockstep (`ct_step`, at the end of this file).
-/

open Aeneas Aeneas.Std Lean.Order

namespace Ct

/-- Trace equivalence: if both runs return, the traces are equal and the results related. -/
def Rel {α : Type u} {β : Type v} (m : Leak α) (m' : Leak β) (R : α → β → Prop) : Prop :=
  ∀ a t b t', m.run = .ok (a, t) → m'.run = .ok (b, t') → t = t' ∧ R a b

/-- The relation on loop-body results: both continue (states related by `I`) or both stop
(results related by `Q`). -/
def CFRel {α : Type u} {α' : Type v} {β : Type w} {β' : Type x}
    (I : α → α' → Prop) (Q : β → β' → Prop) : ControlFlow α β → ControlFlow α' β' → Prop
  | .cont a, .cont a' => I a a'
  | .done b, .done b' => Q b b'
  | _, _ => False

@[simp] theorem CFRel_cont_cont {α α' β β'} {I : α → α' → Prop} {Q : β → β' → Prop} {a a'} :
    CFRel I Q (.cont a) (.cont a') = I a a' := rfl
@[simp] theorem CFRel_done_done {α α' β β'} {I : α → α' → Prop} {Q : β → β' → Prop} {b b'} :
    CFRel I Q (.done b) (.done b') = Q b b' := rfl
@[simp] theorem CFRel_cont_done {α α' β β'} {I : α → α' → Prop} {Q : β → β' → Prop} {a b'} :
    CFRel I Q (.cont a) (.done b') = False := rfl
@[simp] theorem CFRel_done_cont {α α' β β'} {I : α → α' → Prop} {Q : β → β' → Prop} {b a'} :
    CFRel I Q (.done b) (.cont a') = False := rfl

namespace Rel

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

/-- The point of the judgment: equal traces. -/
theorem trace_eq {m : Leak α} {m' : Leak β} {R} (h : Rel m m' R) {a t b t'}
    (h1 : m.run = .ok (a, t)) (h2 : m'.run = .ok (b, t')) : t = t' := (h a t b t' h1 h2).1

/-- Combine a `Rel` lemma with the functional results of the erased programs (for instance the
existing theorems that the verified functions return `ok`): both instrumented runs return
these results, with one and the same trace. -/
theorem same_trace {m : Leak α} {m' : Leak β} {R} (h : Rel m m' R) {a b}
    (h1 : m.erase = .ok a) (h2 : m'.erase = .ok b) :
    ∃ t, m.run = .ok (a, t) ∧ m'.run = .ok (b, t) ∧ R a b := by
  obtain ⟨t, ht⟩ := Leak.erase_eq_ok.mp h1
  obtain ⟨t', ht'⟩ := Leak.erase_eq_ok.mp h2
  obtain ⟨rfl, hR⟩ := h a t b t' ht ht'
  exact ⟨t, ht, ht', hR⟩

theorem mono {m : Leak α} {m' : Leak β} {R S : α → β → Prop} (h : Rel m m' R)
    (hRS : ∀ a b, R a b → S a b) : Rel m m' S := fun a t b t' h1 h2 =>
  let ⟨ht, hR⟩ := h a t b t' h1 h2; ⟨ht, hRS a b hR⟩

/-- Strengthen the postcondition with the functional results (those of the erased programs). -/
theorem with_erase {m : Leak α} {m' : Leak β} {R : α → β → Prop} (h : Rel m m' R) :
    Rel m m' (fun a b => R a b ∧ m.erase = .ok a ∧ m'.erase = .ok b) := by
  intro a t b t' h1 h2
  exact ⟨(h a t b t' h1 h2).1, (h a t b t' h1 h2).2,
    Leak.erase_eq_ok.mpr ⟨t, h1⟩, Leak.erase_eq_ok.mpr ⟨t', h2⟩⟩

/-- A deterministic computation run twice: same trace, same result. -/
theorem refl (m : Leak α) : Rel m m (fun a b => a = b ∧ m.erase = .ok a) := by
  intro a t b t' h1 h2
  rw [h1] at h2
  simp only [Result.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  exact ⟨rfl, rfl, Leak.erase_eq_ok.mpr ⟨t, h1⟩⟩

theorem pure {a : α} {b : β} {R : α → β → Prop} (h : R a b) : Rel (Leak.pure a) (Leak.pure b) R := by
  intro a' t b' t' h1 h2
  simp only [Leak.run_pure, Result.ok.injEq, Prod.mk.injEq] at h1 h2
  obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
  exact ⟨rfl, h⟩

theorem bind {m : Leak α} {m' : Leak β} {f : α → Leak γ} {f' : β → Leak δ}
    {R : α → β → Prop} {S : γ → δ → Prop}
    (h : Rel m m' R) (hf : ∀ a b, R a b → Rel (f a) (f' b) S) :
    Rel (Leak.bind m f) (Leak.bind m' f') S := by
  intro c t d t' h1 h2
  obtain ⟨a, t₁, t₂, ha, hc, rfl⟩ := Leak.bind_eq_ok.mp h1
  obtain ⟨b, t₁', t₂', hb, hd, rfl⟩ := Leak.bind_eq_ok.mp h2
  obtain ⟨rfl, hR⟩ := h a t₁ b t₁' ha hb
  obtain ⟨rfl, hS⟩ := hf a b hR c t₂ d t₂' hc hd
  exact ⟨rfl, hS⟩

theorem prim {t t' : Trace} {r : Result α} {r' : Result β} (ht : t = t') :
    Rel (Leak.prim t r) (Leak.prim t' r') (fun a b => r = .ok a ∧ r' = .ok b) := by
  intro a t₁ b t₂ h1 h2
  obtain ⟨ha, rfl⟩ := Leak.prim_eq_ok.mp h1
  obtain ⟨hb, rfl⟩ := Leak.prim_eq_ok.mp h2
  exact ⟨ht, ha, hb⟩

theorem lift {r : Result α} {r' : Result β} :
    Rel (Leak.lift r) (Leak.lift r') (fun a b => r = .ok a ∧ r' = .ok b) := prim rfl

theorem liftM {r : Result α} {r' : Result α} :
    Rel (_root_.liftM r : Leak α) (_root_.liftM r' : Leak α) (fun a b => r = .ok a ∧ r' = .ok b) := lift

theorem emit {t t' : Trace} (ht : t = t') :
    Rel (Leak.emit t) (Leak.emit t') (fun _ _ => True) := by
  intro a t₁ b t₂ h1 h2
  simp only [Leak.run_emit, Result.ok.injEq, Prod.mk.injEq] at h1 h2
  exact ⟨h1.2 ▸ h2.2 ▸ ht, trivial⟩

/-- The conditional: the two tests must agree (the outcome is emitted). -/
theorem cond {c c' : Prop} [Decidable c] [Decidable c'] {a b : Leak α} {a' b' : Leak β}
    {R : α → β → Prop} (hc : decide c = decide c')
    (ht : c → c' → Rel a a' R) (he : ¬ c → ¬ c' → Rel b b' R) :
    Rel (Leak.cond c a b) (Leak.cond c' a' b') R := by
  rw [Leak.cond_eq, Leak.cond_eq]
  refine bind (emit (by rw [hc])) fun _ _ _ => ?_
  by_cases h : c
  · have h' : c' := by simpa [h] using hc
    simp only [h, h', ite_true]; exact ht h h'
  · have h' : ¬ c' := by simpa [h] using hc
    simp only [h, h', ite_false]; exact he h h'

theorem uncurry {f : α → β → Leak γ} {f' : α' → β' → Leak δ} {p : α × β} {p' : α' × β'}
    {S : γ → δ → Prop} (h : Rel (f p.1 p.2) (f' p'.1 p'.2) S) :
    Rel (Aeneas.Std.uncurry f p) (Aeneas.Std.uncurry f' p') S := by
  cases p; cases p'; exact h

/-! ### Loops -/

/-- The loop rule: an invariant `I` relating the two loop states, preserved in lockstep.
Termination is not needed (`Rel` is about runs that return). -/
theorem loop {body : α → Leak (ControlFlow α β)} {body' : γ → Leak (ControlFlow γ δ)}
    (I : α → γ → Prop) {Q : β → δ → Prop}
    (hbody : ∀ x x', I x x' → Rel (body x) (body' x') (CFRel I Q))
    {x : α} {x' : γ} (hx : I x x') :
    Rel (Leak.loop body x) (Leak.loop body' x') Q := by
  -- fixpoint induction on the first loop
  have key : ∀ x b t, (Leak.loop body x).run = .ok (b, t) →
      ∀ x' b' t', I x x' → (Leak.loop body' x').run = .ok (b', t') → t = t' ∧ Q b b' := by
    refine Leak.loop.fixpoint_induct body
      (fun F => ∀ x b t, (F x).run = .ok (b, t) →
        ∀ x' b' t', I x x' → (Leak.loop body' x').run = .ok (b', t') → t = t' ∧ Q b b') ?_ ?_
    · exact admissible_pi_apply _ fun x =>
        Leak.admissible_leak_ok (fun b t => ∀ x' b' t', I x x' →
          (Leak.loop body' x').run = .ok (b', t') → t = t' ∧ Q b b')
    · intro F ih x b t h x' b' t' hI h'
      obtain ⟨r, t₁, t₂, hr, hk, rfl⟩ := Leak.bind_eq_ok.mp h
      rw [Leak.loop_unfold] at h'
      obtain ⟨r', t₁', t₂', hr', hk', rfl⟩ := Leak.bind_eq_ok.mp h'
      obtain ⟨rfl, hR⟩ := hbody x x' hI r t₁ r' t₁' hr hr'
      cases r with
      | cont y =>
        cases r' with
        | cont y' =>
          obtain ⟨rfl, hQ⟩ := ih y b t₂ hk y' b' t₂' hR hk'
          exact ⟨rfl, hQ⟩
        | done _ => exact hR.elim
      | done c =>
        cases r' with
        | cont _ => exact hR.elim
        | done c' =>
          simp only [Leak.run_pure, Result.ok.injEq, Prod.mk.injEq] at hk hk'
          obtain ⟨rfl, rfl⟩ := hk; obtain ⟨rfl, rfl⟩ := hk'
          exact ⟨rfl, hR⟩
  intro b t b' t' h h'
  exact key x b t h x' b' t' hx h'

/-! ### Derived rules for `bind` (the forms `ct_step` uses) -/

/-- Both sides run the very same computation (on public data): same trace, same result. -/
theorem bind_refl {m : Leak α} {f : α → Leak γ} {f' : α → Leak δ} {S : γ → δ → Prop}
    (hf : ∀ a, m.erase = .ok a → Rel (f a) (f' a) S) : Rel (Leak.bind m f) (Leak.bind m f') S :=
  bind (refl m) fun a _ ⟨hab, ha⟩ => hab ▸ hf a ha

theorem bind_prim {t t' : Trace} {r : Result α} {r' : Result β} {f : α → Leak γ}
    {f' : β → Leak δ} {S : γ → δ → Prop} (ht : t = t')
    (hf : ∀ a b, r = .ok a → r' = .ok b → Rel (f a) (f' b) S) :
    Rel (Leak.bind (Leak.prim t r) f) (Leak.bind (Leak.prim t' r') f') S :=
  bind (prim ht) fun a b ⟨ha, hb⟩ => hf a b ha hb

theorem bind_liftM {r r' : Result α} {f : α → Leak γ} {f' : α → Leak δ} {S : γ → δ → Prop}
    (hf : ∀ a b, r = .ok a → r' = .ok b → Rel (f a) (f' b) S) :
    Rel (Leak.bind (_root_.liftM r : Leak α) f) (Leak.bind (_root_.liftM r' : Leak α) f') S :=
  bind liftM fun a b ⟨ha, hb⟩ => hf a b ha hb

theorem bind_pure {a : α} {b : β} {f : α → Leak γ} {f' : β → Leak δ} {S : γ → δ → Prop}
    (hf : Rel (f a) (f' b) S) : Rel (Leak.bind (Leak.pure a) f) (Leak.bind (Leak.pure b) f') S :=
  bind (R := fun x y => x = a ∧ y = b) (pure ⟨rfl, rfl⟩) fun _ _ ⟨ha, hb⟩ => ha ▸ hb ▸ hf

/-- Use a lemma about the first computation. -/
theorem bind_of {m : Leak α} {m' : Leak β} {f : α → Leak γ} {f' : β → Leak δ}
    {R : α → β → Prop} {S : γ → δ → Prop}
    (h : Rel m m' R) (hf : ∀ a b, R a b → Rel (f a) (f' b) S) :
    Rel (Leak.bind m f) (Leak.bind m' f') S := bind h hf

end Rel

/-! ## Public outputs (declassification)

Signing publishes values derived from secrets (the signature; through it the hypertree roots and
the WOTS digits, which decide chain lengths). Its trace depends on them, so `Rel` (which
quantifies over all pairs of returning runs) is false for it. Following ct-verif, the statement
is restricted to pairs of runs whose *outputs* agree on what is published:

`RelIf m m' Φ R`: if both runs return with results satisfying `Φ`, their traces are equal and
the results are related by `R`.

The bind rule needs the published output of the whole computation to determine the public part
`Ψ` of the intermediate result; this is a functional fact about the erased programs (e.g. the
verifier recomputes the hypertree roots from the signature), supplied as `hΨ`. -/

/-- Trace equivalence for runs whose results satisfy `Φ`. -/
def RelIf {α : Type u} {β : Type v} (m : Leak α) (m' : Leak β) (Φ R : α → β → Prop) : Prop :=
  ∀ a t b t', m.run = .ok (a, t) → m'.run = .ok (b, t') → Φ a b → t = t' ∧ R a b

namespace RelIf

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

theorem of_rel {m : Leak α} {m' : Leak β} {Φ R} (h : Rel m m' R) : RelIf m m' Φ R :=
  fun a t b t' h1 h2 _ => h a t b t' h1 h2

theorem to_rel {m : Leak α} {m' : Leak β} {R} (h : RelIf m m' (fun _ _ => True) R) :
    Rel m m' R := fun a t b t' h1 h2 => h a t b t' h1 h2 trivial

theorem mono {m : Leak α} {m' : Leak β} {Φ Φ' R S : α → β → Prop} (h : RelIf m m' Φ R)
    (hΦ : ∀ a b, Φ' a b → Φ a b) (hRS : ∀ a b, R a b → S a b) : RelIf m m' Φ' S :=
  fun a t b t' h1 h2 hp => let ⟨ht, hR⟩ := h a t b t' h1 h2 (hΦ a b hp); ⟨ht, hRS a b hR⟩

/-- Sequencing under a public-output assumption. -/
theorem bind {m : Leak α} {m' : Leak β} {f : α → Leak γ} {f' : β → Leak δ}
    {Ψ R : α → β → Prop} {Φ S : γ → δ → Prop}
    (h : RelIf m m' Ψ R) (hf : ∀ a b, R a b → RelIf (f a) (f' b) Φ S)
    (hΨ : ∀ a b c d, m.erase = .ok a → m'.erase = .ok b → (f a).erase = .ok c →
      (f' b).erase = .ok d → Φ c d → Ψ a b) :
    RelIf (Leak.bind m f) (Leak.bind m' f') Φ S := by
  intro c t d t' h1 h2 hΦ
  obtain ⟨a, t₁, t₂, ha, hc, rfl⟩ := Leak.bind_eq_ok.mp h1
  obtain ⟨b, t₁', t₂', hb, hd, rfl⟩ := Leak.bind_eq_ok.mp h2
  have hp := hΨ a b c d (Leak.erase_eq_ok.mpr ⟨_, ha⟩) (Leak.erase_eq_ok.mpr ⟨_, hb⟩)
    (Leak.erase_eq_ok.mpr ⟨_, hc⟩) (Leak.erase_eq_ok.mpr ⟨_, hd⟩) hΦ
  obtain ⟨rfl, hR⟩ := h a t₁ b t₁' ha hb hp
  obtain ⟨rfl, hS⟩ := hf a b hR c t₂ d t₂' hc hd hΦ
  exact ⟨rfl, hS⟩

end RelIf

end Ct
