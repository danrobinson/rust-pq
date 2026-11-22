import Aeneas
import Ct.Attr

/-!
# The leakage monad

`Leak α` is a writer monad over Aeneas's `Result`: a computation either fails, diverges, or
returns a value together with the trace of the leakage events it emitted.

* `Leak.erase` forgets the trace; every instrumented definition is proved to erase to the
  verified one (`Ct/Erase.lean`).
* Binding appends traces. Lifting a `Result` computation (`Leak.lift`) emits nothing.
* `Leak.prim t r` runs the `Result` computation `r` and emits `t`: this is how every
  leaking primitive is instrumented (`Ct/Model.lean`).
* `Leak.cond c a b` emits `branch (decide c)` and then runs the chosen branch.
* `Leak.loop` is Aeneas's `loop` combinator, in `Leak`, defined by `partial_fixpoint`.

The leakage model (which primitive emits what) is in `Ct/Model.lean`.
-/

open Aeneas Aeneas.Std Lean.Order

namespace Ct

/-- One observation of the side-channel adversary.

* `branch b`: the outcome of a conditional.
* `index i len`: an element access at index `i` of a container of length `len`
  (array, slice or vector; read, write, or mutable borrow).
* `range start stop len`: a sub-slice `[start, stop)` of a container of length `len`.
* `copy dst src`: `copy_from_slice` with destination and source lengths.
* `extend len add`: growing a vector of length `len` by `add` elements (`push`,
  `extend_from_slice`); this covers the size of any reallocation.
* `div a b`, `rem a b`: the operands of a division or remainder (variable-time on most CPUs).
* `cmp pre len`: an element-wise (short-circuiting) comparison of two containers of length
  `len` whose first `pre` elements are equal (`pre = len` if all are).

All quantities are the actual values (`.val` of the machine integers). -/
inductive Event where
  | branch (b : Bool)
  | index (i len : Nat)
  | range (start stop len : Nat)
  | copy (dst src : Nat)
  | extend (len add : Nat)
  | div (a b : Nat)
  | rem (a b : Nat)
  | cmp (pre len : Nat)
deriving DecidableEq, Repr

abbrev Trace := List Event

/-- The length of the longest common prefix of two lists. -/
def commonPrefix {α : Type u} [DecidableEq α] : List α → List α → Nat
  | x :: xs, y :: ys => if x = y then commonPrefix xs ys + 1 else 0
  | _, _ => 0

/-- The leakage monad. Irreducible so that it is never confused with `Result` (Aeneas's `do`
elaborator and instance search look through reducible definitions). -/
@[irreducible] def Leak (α : Type u) : Type u := Result (α × Trace)

namespace Leak

section Basic
attribute [local semireducible] Leak

/-- The underlying `Result` computation, returning the value and the trace. -/
def run {α : Type u} (m : Leak α) : Result (α × Trace) := m
/-- Build a `Leak` computation from a `Result` returning a value and a trace. -/
def mk {α : Type u} (r : Result (α × Trace)) : Leak α := r

@[simp] theorem run_mk {α : Type u} (r : Result (α × Trace)) : (mk r).run = r := rfl
@[simp] theorem mk_run {α : Type u} (m : Leak α) : mk m.run = m := rfl

theorem ext {α : Type u} {m m' : Leak α} (h : m.run = m'.run) : m = m' := h

noncomputable instance instCCPO {α : Type u} : CCPO (Leak α) :=
  inferInstanceAs (CCPO (Result (α × Trace)))

theorem le_iff {α : Type u} (m m' : Leak α) : (m ⊑ m') ↔ (m.run ⊑ m'.run) := Iff.rfl

theorem monotone_run {γ : Sort w} [PartialOrder γ] {α : Type u} (f : γ → Leak α) :
    monotone (fun x => (f x).run) ↔ monotone f := Iff.rfl

theorem monotone_mk {γ : Sort w} [PartialOrder γ] {α : Type u} (f : γ → Result (α × Trace)) :
    monotone (fun x => mk (f x)) ↔ monotone f := Iff.rfl

theorem admissible_run {α : Type u} (P : Result (α × Trace) → Prop) (h : admissible P) :
    admissible (fun m : Leak α => P m.run) := h

end Basic

/-- Return a value, emitting nothing. -/
def pure {α : Type u} (a : α) : Leak α := mk (.ok (a, []))

/-- Sequencing: run `m`, then `f`, appending their traces. -/
def bind {α : Type u} {β : Type v} (m : Leak α) (f : α → Leak β) : Leak β :=
  mk (Aeneas.Std.bind m.run fun p =>
        Aeneas.Std.bind (f p.1).run fun q => .ok (q.1, p.2 ++ q.2))

/-- Emit a trace. -/
def emit (t : Trace) : Leak Unit := mk (.ok ((), t))

/-- A primitive: run the `Result` computation `r` and, if it returns, emit `t`. -/
def prim {α : Type u} (t : Trace) (r : Result α) : Leak α :=
  mk (Aeneas.Std.bind r fun a => .ok (a, t))

/-- Lift a `Result` computation, emitting nothing. Only used for operations that do not leak
(plain arithmetic, bit operations, casts, pure functions); see `Ct/Check.lean`. -/
def lift {α : Type u} (r : Result α) : Leak α := prim [] r

/-- The instrumented conditional: emit the outcome, then run the chosen branch. -/
def cond {α : Type u} (c : Prop) [Decidable c] (a b : Leak α) : Leak α :=
  bind (emit [.branch (decide c)]) fun _ => if c then a else b

/-- Forget the trace. -/
def erase {α : Type u} (m : Leak α) : Result α :=
  Aeneas.Std.bind m.run fun p => .ok p.1

instance : Monad Leak where
  pure := Leak.pure
  bind := Leak.bind

instance : MonadLift Result Leak where
  monadLift := Leak.lift

/-! ## Order and monotonicity (for `partial_fixpoint`) -/

@[partial_fixpoint_monotone]
theorem bind_mono {γ : Sort w} [PartialOrder γ] {α : Type u} {β : Type v}
    (f : γ → Leak α) (g : γ → α → Leak β)
    (hf : monotone f) (hg : monotone g) :
    monotone (fun x => bind (f x) (g x)) := by
  unfold bind
  rw [monotone_mk]
  apply Aeneas.Std.bind_mono
  · exact (monotone_run f).mpr hf
  · apply monotone_of_monotone_apply
    intro p
    apply Aeneas.Std.bind_mono
    · exact (monotone_run (fun x => g x p.1)).mpr (monotone_apply p.1 g hg)
    · exact monotone_const _

@[partial_fixpoint_monotone]
theorem cond_mono {γ : Sort w} [PartialOrder γ] {α : Type u} (c : Prop) [Decidable c]
    (f g : γ → Leak α) (hf : monotone f) (hg : monotone g) :
    monotone (fun x => cond c (f x) (g x)) := by
  unfold cond
  apply bind_mono
  · exact monotone_const _
  · apply monotone_of_monotone_apply
    intro _
    exact monotone_ite c _ _ hf hg

/-- Aeneas's `loop`, in the leakage monad. The loop itself emits nothing: every exit decision
in the translated code is made by an instrumented `if` in the body. -/
def loop {α : Type u} {β : Type v} (body : α → Leak (ControlFlow α β)) (x : α) : Leak β :=
  bind (body x) fun r =>
    match r with
    | .cont y => loop body y
    | .done b => pure b
partial_fixpoint

/-! ## Basic facts about `Result` -/

theorem _root_.Aeneas.Std.Result.cases_flat {α : Type u} (r : Result α) :
    (∃ a, r = .ok a) ∨ (∃ e, r = .fail e) ∨ r = .div := by
  cases r with
  | ret a => exact Or.inl ⟨a, rfl⟩
  | vis i k =>
    cases i with
    | fail e =>
      refine Or.inr (Or.inl ⟨e, ?_⟩)
      rw [Result.fail_eq_vis]
      congr
      funext x; exact x.elim
  | div => exact Or.inr (Or.inr rfl)

theorem _root_.Aeneas.Std.bind_eq_ok {α : Type u} {β : Type v} {m : Result α}
    {f : α → Result β} {b : β} :
    Aeneas.Std.bind m f = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  constructor
  · intro h
    rcases Result.cases_flat m with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl
    · exact ⟨a, rfl, by simpa using h⟩
    · simp at h
    · simp at h
  · rintro ⟨a, rfl, h⟩; simpa using h

theorem _root_.Aeneas.Std.bind_eq_fail {α : Type u} {β : Type v} {m : Result α}
    {f : α → Result β} {e : Error} :
    Aeneas.Std.bind m f = .fail e ↔ (m = .fail e ∨ ∃ a, m = .ok a ∧ f a = .fail e) := by
  constructor
  · intro h
    rcases Result.cases_flat m with ⟨a, rfl⟩ | ⟨e', rfl⟩ | rfl
    · exact Or.inr ⟨a, rfl, by simpa using h⟩
    · simp at h; exact Or.inl (by rw [h])
    · simp at h
  · rintro (rfl | ⟨a, rfl, h⟩)
    · simp
    · simpa using h

/-- `Result` is a flat domain: two computations that agree on returning and failing are
equal. -/
theorem _root_.Aeneas.Std.Result.ext_flat {α : Type u} {x y : Result α}
    (hok : ∀ a, x = .ok a ↔ y = .ok a) (hfail : ∀ e, x = .fail e ↔ y = .fail e) : x = y := by
  rcases Result.cases_flat x with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl
  · exact ((hok a).mp rfl).symm
  · exact ((hfail e).mp rfl).symm
  · rcases Result.cases_flat y with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl
    · exact absurd ((hok a).mpr rfl) (by simp)
    · exact absurd ((hfail e).mpr rfl) (by simp)
    · rfl

section Admissible
unseal Result

/-- "If it returns, the result satisfies `P`" is admissible. -/
theorem admissible_ok {α : Type u} (P : α → Prop) :
    admissible (fun x : Result α => ∀ v, x = .ok v → P v) := by
  intro c hc h v heq
  exact h _ (Aeneas.Data.Coinductive.ITree.csup_ret_mem hc heq) v rfl

/-- "If it fails, then `P`" is admissible. -/
theorem admissible_fail {α : Type u} (P : Error → Prop) :
    admissible (fun x : Result α => ∀ e, x = .fail e → P e) := by
  intro c hc h e heq
  rw [Result.fail_eq_vis] at heq
  obtain ⟨k', hk'⟩ := Aeneas.Data.Coinductive.ITree.csup_vis_mem hc heq
  have : k' = PEmpty.elim := by funext x; exact x.elim
  subst this
  exact h _ hk' e (Result.fail_eq_vis e).symm

end Admissible

theorem admissible_leak_ok {α : Type u} (P : α → Trace → Prop) :
    admissible (fun m : Leak α => ∀ a t, m.run = .ok (a, t) → P a t) := by
  have := admissible_run (α := α) _ (admissible_ok (fun (v : α × Trace) => P v.1 v.2))
  refine (funext fun m => ?_ : (fun m : Leak α => ∀ a t, m.run = .ok (a, t) → P a t) = _) ▸ this
  apply propext
  constructor
  · intro h v hv; exact h v.1 v.2 hv
  · intro h a t hv; exact h (a, t) hv

theorem admissible_leak_fail {α : Type u} (P : Error → Prop) :
    admissible (fun m : Leak α => ∀ e, m.run = .fail e → P e) :=
  admissible_run _ (admissible_fail P)

/-! ## Running instrumented computations -/

@[simp] theorem run_pure {α : Type u} (a : α) : (pure a).run = .ok (a, []) := rfl
@[simp] theorem run_emit (t : Trace) : (emit t).run = .ok ((), t) := rfl

theorem run_bind {α : Type u} {β : Type v} (m : Leak α) (f : α → Leak β) :
    (bind m f).run = Aeneas.Std.bind m.run fun p =>
        Aeneas.Std.bind (f p.1).run fun q => .ok (q.1, p.2 ++ q.2) := rfl

theorem run_prim {α : Type u} (t : Trace) (r : Result α) :
    (prim t r).run = Aeneas.Std.bind r fun a => .ok (a, t) := rfl

theorem bind_eq_ok {α : Type u} {β : Type v} {m : Leak α} {f : α → Leak β} {b : β} {t : Trace} :
    (bind m f).run = .ok (b, t) ↔
      ∃ a t₁ t₂, m.run = .ok (a, t₁) ∧ (f a).run = .ok (b, t₂) ∧ t = t₁ ++ t₂ := by
  rw [run_bind, Aeneas.Std.bind_eq_ok]
  constructor
  · rintro ⟨⟨a, t₁⟩, h1, h2⟩
    rw [Aeneas.Std.bind_eq_ok] at h2
    obtain ⟨⟨b', t₂⟩, h3, h4⟩ := h2
    simp only [Result.ok.injEq, Prod.mk.injEq] at h4
    obtain ⟨rfl, rfl⟩ := h4
    exact ⟨a, t₁, t₂, h1, h3, rfl⟩
  · rintro ⟨a, t₁, t₂, h1, h2, rfl⟩
    exact ⟨(a, t₁), h1, by rw [h2]; simp⟩

theorem bind_eq_fail {α : Type u} {β : Type v} {m : Leak α} {f : α → Leak β} {e : Error} :
    (bind m f).run = .fail e ↔
      (m.run = .fail e ∨ ∃ a t₁, m.run = .ok (a, t₁) ∧ (f a).run = .fail e) := by
  rw [run_bind, Aeneas.Std.bind_eq_fail]
  constructor
  · rintro (h | ⟨⟨a, t₁⟩, h1, h2⟩)
    · exact Or.inl h
    · rw [Aeneas.Std.bind_eq_fail] at h2
      rcases h2 with h2 | ⟨_, _, h3⟩
      · exact Or.inr ⟨a, t₁, h1, h2⟩
      · simp at h3
  · rintro (h | ⟨a, t₁, h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(a, t₁), h1, by rw [Aeneas.Std.bind_eq_fail]; exact Or.inl h2⟩

theorem prim_eq_ok {α : Type u} {t : Trace} {r : Result α} {a : α} {t' : Trace} :
    (prim t r).run = .ok (a, t') ↔ r = .ok a ∧ t' = t := by
  rw [run_prim, Aeneas.Std.bind_eq_ok]
  constructor
  · rintro ⟨a', h1, h2⟩
    simp only [Result.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨h1, rfl⟩
  · rintro ⟨h, rfl⟩; exact ⟨a, h, rfl⟩

theorem cond_eq {α : Type u} (c : Prop) [Decidable c] (a b : Leak α) :
    cond c a b = bind (emit [.branch (decide c)]) (fun _ => if c then a else b) := rfl

theorem loop_unfold {α : Type u} {β : Type v} (body : α → Leak (ControlFlow α β)) (x : α) :
    loop body x = bind (body x) (fun r => match r with
      | .cont y => loop body y
      | .done b => pure b) := by
  rw [loop]

/-! ## Erasure -/

@[simp, ct_erase] theorem erase_pure {α : Type u} (a : α) : (pure a).erase = .ok a := by
  simp [erase]

theorem erase_eq {α : Type u} (m : Leak α) : m.erase = Aeneas.Std.bind m.run fun p => .ok p.1 :=
  rfl

@[simp, ct_erase] theorem erase_bind {α : Type u} {β : Type v} (m : Leak α) (f : α → Leak β) :
    (bind m f).erase = Aeneas.Std.bind m.erase (fun a => (f a).erase) := by
  simp only [erase, run_bind, Aeneas.Std.bind_assoc, bind_ok]

@[simp, ct_erase] theorem erase_prim {α : Type u} (t : Trace) (r : Result α) : (prim t r).erase = r := by
  simp only [erase, run_prim, Aeneas.Std.bind_assoc, bind_ok]
  exact Aeneas.Std.bind_pure r

@[simp, ct_erase] theorem erase_lift {α : Type u} (r : Result α) : (lift r).erase = r := erase_prim _ _

@[simp, ct_erase] theorem erase_monadLift {α : Type u} (r : Result α) :
    (MonadLiftT.monadLift r : Leak α).erase = r := erase_lift r

@[simp, ct_erase] theorem erase_emit (t : Trace) : (emit t).erase = .ok () := by simp [erase]

@[simp, ct_erase] theorem erase_cond {α : Type u} (c : Prop) [Decidable c] (a b : Leak α) :
    (cond c a b).erase = if c then a.erase else b.erase := by
  rw [cond_eq, erase_bind, erase_emit, bind_ok]
  split <;> rfl

@[simp, ct_erase] theorem erase_ite {α : Type u} (c : Prop) [Decidable c] (a b : Leak α) :
    (if c then a else b).erase = if c then a.erase else b.erase := by
  split <;> rfl

@[simp, ct_erase] theorem erase_uncurry {α : Type u} {β : Type v} {γ : Type w}
    (f : α → β → Leak γ) (p : α × β) :
    (Aeneas.Std.uncurry f p).erase = Aeneas.Std.uncurry (fun a b => (f a b).erase) p := by
  cases p; rfl

theorem erase_eq_ok {α : Type u} {m : Leak α} {a : α} :
    m.erase = .ok a ↔ ∃ t, m.run = .ok (a, t) := by
  rw [erase, Aeneas.Std.bind_eq_ok]
  constructor
  · rintro ⟨⟨a', t⟩, h1, h2⟩
    simp only [Result.ok.injEq] at h2
    subst h2; exact ⟨t, h1⟩
  · rintro ⟨t, h⟩; exact ⟨(a, t), h, rfl⟩

theorem erase_eq_fail {α : Type u} {m : Leak α} {e : Error} :
    m.erase = .fail e ↔ m.run = .fail e := by
  rw [erase, Aeneas.Std.bind_eq_fail]
  constructor
  · rintro (h | ⟨_, _, h⟩)
    · exact h
    · simp at h
  · intro h; exact Or.inl h

/-- Erasure commutes with `loop`. -/
@[ct_erase] theorem erase_loop {α : Type u} {β : Type v} (body : α → Leak (ControlFlow α β)) (x : α) :
    (loop body x).erase = Aeneas.Std.loop (fun y => (body y).erase) x := by
  -- `Result` is flat: compare the returning and the failing behaviours.
  -- (1) from the instrumented loop to the plain one
  have h1 : ∀ x b t, (loop body x).run = .ok (b, t) →
      Aeneas.Std.loop (fun y => (body y).erase) x = .ok b := by
    refine loop.fixpoint_induct body
      (fun F => ∀ x b t, (F x).run = .ok (b, t) →
        Aeneas.Std.loop (fun y => (body y).erase) x = .ok b) ?_ ?_
    · exact admissible_pi_apply _ fun x =>
        admissible_leak_ok (fun b _ => Aeneas.Std.loop (fun y => (body y).erase) x = .ok b)
    · intro F ih x b t h
      rw [bind_eq_ok] at h
      obtain ⟨r, t₁, t₂, hr, hk, -⟩ := h
      rw [Aeneas.Std.loop]
      have hr' : (body x).erase = .ok r := erase_eq_ok.mpr ⟨t₁, hr⟩
      rw [hr', bind_ok]
      cases r with
      | cont y => exact ih y b t₂ hk
      | done b' =>
        simp only [run_pure, Result.ok.injEq, Prod.mk.injEq] at hk
        rw [hk.1]
  have h2 : ∀ x e, (loop body x).run = .fail e →
      Aeneas.Std.loop (fun y => (body y).erase) x = .fail e := by
    refine loop.fixpoint_induct body
      (fun F => ∀ x e, (F x).run = .fail e →
        Aeneas.Std.loop (fun y => (body y).erase) x = .fail e) ?_ ?_
    · exact admissible_pi_apply _ fun x => by
        have := admissible_leak_fail (α := β) (fun e =>
          Aeneas.Std.loop (fun y => (body y).erase) x = .fail e)
        exact this
    · intro F ih x e h
      rw [bind_eq_fail] at h
      rw [Aeneas.Std.loop]
      rcases h with h | ⟨r, t₁, hr, hk⟩
      · have : (body x).erase = .fail e := erase_eq_fail.mpr h
        rw [this]; simp
      · have hr' : (body x).erase = .ok r := erase_eq_ok.mpr ⟨t₁, hr⟩
        rw [hr', bind_ok]
        cases r with
        | cont y => exact ih y e hk
        | done b' => simp at hk
  -- (2) from the plain loop to the instrumented one
  have h3 : ∀ x b, Aeneas.Std.loop (fun y => (body y).erase) x = .ok b →
      ∃ t, (loop body x).run = .ok (b, t) := by
    refine Aeneas.Std.loop.fixpoint_induct (fun y => (body y).erase)
      (fun F => ∀ x b, F x = .ok b → ∃ t, (loop body x).run = .ok (b, t)) ?_ ?_
    · exact admissible_pi_apply _ fun x => admissible_ok _
    · intro F ih x b h
      rw [Aeneas.Std.bind_eq_ok] at h
      obtain ⟨r, hr, hk⟩ := h
      obtain ⟨t₁, hr⟩ := erase_eq_ok.mp hr
      rw [loop_unfold]
      cases r with
      | cont y =>
        obtain ⟨t₂, ht⟩ := ih y b hk
        exact ⟨t₁ ++ t₂, bind_eq_ok.mpr ⟨_, t₁, t₂, hr, ht, rfl⟩⟩
      | done b' =>
        simp only [Result.ok.injEq] at hk
        subst hk
        exact ⟨t₁ ++ [], bind_eq_ok.mpr ⟨_, t₁, [], hr, rfl, rfl⟩⟩
  have h4 : ∀ x e, Aeneas.Std.loop (fun y => (body y).erase) x = .fail e →
      (loop body x).run = .fail e := by
    refine Aeneas.Std.loop.fixpoint_induct (fun y => (body y).erase)
      (fun F => ∀ x e, F x = .fail e → (loop body x).run = .fail e) ?_ ?_
    · exact admissible_pi_apply _ fun x => admissible_fail _
    · intro F ih x e h
      rw [Aeneas.Std.bind_eq_fail] at h
      rw [loop_unfold, bind_eq_fail]
      rcases h with h | ⟨r, hr, hk⟩
      · exact Or.inl (erase_eq_fail.mp h)
      · obtain ⟨t₁, hr⟩ := erase_eq_ok.mp hr
        refine Or.inr ⟨r, t₁, hr, ?_⟩
        cases r with
        | cont y => exact ih y e hk
        | done b' => simp at hk
  apply Result.ext_flat
  · intro b
    constructor
    · intro h
      obtain ⟨t, ht⟩ := erase_eq_ok.mp h
      exact h1 x b t ht
    · intro h
      obtain ⟨t, ht⟩ := h3 x b h
      exact erase_eq_ok.mpr ⟨t, ht⟩
  · intro e
    constructor
    · intro h; exact h2 x e (erase_eq_fail.mp h)
    · intro h; exact erase_eq_fail.mpr (h4 x e h)

end Leak

end Ct
