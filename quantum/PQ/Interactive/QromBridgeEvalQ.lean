import PQ.Interactive.QromBridgeEvalProg

/-!
# Evaluations of the port function inside open (non-closed) machines

`EvalCost` (`QromBridgeEval.lean`) is for classical computations in front of CLOSED machines.
Machines that still talk to a game (e.g. the ITSR adversary with its target oracle) need the
analogue over an arbitrary interface `spec` with weights `cnt`:

* `EvalCostQ cnt f n`: `liftQ (f H)` can be put in front of any `PUE cnt` family at price `n`;
  `.const` (from a `WCount`), `.eval`, `.bind`, `.mono`, `.map`;
* `PUE.wrap0E`: a stateless wrapper whose code DEPENDS on the port function, each answer of
  price `cnt t`, preserves `PUE`;
* `wCount_zero`, `WCount.bind`.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] {α β γ δ : Type} {ι : Type} {spec : OracleSpec ι}

theorem wCount_zero {κ : Type} {sp : OracleSpec κ} (P : OracleComp sp α) (n : ℕ) :
    WCount (fun _ ↦ 0) P n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => exact trivial
  | query_bind t k ih =>
    rw [wCount_query_bind]
    exact ⟨Nat.zero_le _, fun r ↦ by simpa using ih r n⟩

theorem WCount.bind {κ : Type} {sp : OracleSpec κ} {w : sp.Domain → ℕ} {oa : OracleComp sp α}
    {f : α → OracleComp sp β} {n m : ℕ} (h : WCount w oa n) (hf : ∀ a, WCount w (f a) m) :
    WCount w (oa >>= f) (n + m) := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact (hf a).mono (by omega)
  | query_bind t k ih =>
    rw [wCount_query_bind] at h
    rw [bind_assoc, wCount_query_bind]
    refine ⟨by omega, fun r ↦ ?_⟩
    have := ih r (h.2 r)
    have e : n + m - w t = n - w t + m := by omega
    rw [e]
    exact this

variable (E) in
/-- `liftQ (f H)` can be run in front of any `PUE cnt` family at the price of `n`. -/
def EvalCostQ (cnt : spec.Domain → ℕ) (f : (X → Y) → OracleComp spec γ) (n : ℕ) : Prop :=
  ∀ (β : Type) (B : γ → (X → Y) → QOC (WS X Y E) spec β) (q : ℕ),
    (∀ c, PUE cnt (B c) q) → PUE cnt (fun H ↦ liftQ (f H) >>= fun c ↦ B c H) (q + n)

namespace EvalCostQ

variable {cnt : spec.Domain → ℕ}

theorem mono {f : (X → Y) → OracleComp spec γ} {n n' : ℕ} (h : EvalCostQ E cnt f n)
    (hn : n ≤ n') : EvalCostQ E cnt f n' :=
  fun β B q hB ↦ (h β B q hB).mono (by omega)

theorem const (oa : OracleComp spec γ) {n : ℕ} (h : WCount cnt oa n) :
    EvalCostQ (X := X) (Y := Y) E cnt (fun _ ↦ oa) n :=
  fun _ _ _ hB ↦ PUE.liftQ_bind oa h hB

theorem eval (x : X) (d : Y → γ) :
    EvalCostQ E cnt (fun H : X → Y ↦ (pure (d (H x)) : OracleComp spec γ)) 1 := by
  intro β B q hB
  simp only [liftQ_pure, pure_bind]
  exact PUE.eval x (fun y H ↦ B (d y) H) q fun y ↦ hB (d y)

theorem bind {f : (X → Y) → OracleComp spec γ} {g : γ → (X → Y) → OracleComp spec δ} {n m : ℕ}
    (hf : EvalCostQ E cnt f n) (hg : ∀ c, EvalCostQ E cnt (g c) m) :
    EvalCostQ E cnt (fun H ↦ f H >>= fun c ↦ g c H) (n + m) := by
  intro β B q hB
  simp only [liftQ_bind, bind_assoc]
  have h := hf β (fun c H ↦ liftQ (g c H) >>= fun d ↦ B d H) (q + m) fun c ↦ hg c β B q hB
  have e : q + (n + m) = q + m + n := by omega
  rw [e]
  exact h

end EvalCostQ

variable {ι' : Type} {spec' : OracleSpec ι'}

/-- A stateless wrapper whose code depends on the port function, each answer to `t` of price
`cnt t`, preserves `PUE`. -/
theorem PUE.wrap0E (h : (X → Y) → QueryImpl spec (OracleComp (unifSpec + spec')))
    {cnt : spec.Domain → ℕ} {cnt' : (unifSpec + spec').Domain → ℕ}
    (hc : ∀ t, EvalCostQ E cnt' (fun H ↦ h H t) (cnt t))
    {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (hA : PUE cnt A q) :
    PUE cnt' (fun H ↦ PQ.Interactive.wrap0 (h H) (A H)) q := by
  induction hA with
  | pure a q =>
    simp only [wrap0_pure]
    exact PUE.pure _ _
  | instr j k q _ ih =>
    simp only [wrap0_instr_bind]
    exact PUE.instr j (fun i H ↦ PQ.Interactive.wrap0 (h H) (k i H)) _ ih
  | port k q _ ih =>
    simp only [wrap0_instr_bind]
    exact PUE.port (fun H ↦ PQ.Interactive.wrap0 (h H) (k H)) _ ih
  | query u k q _ ih =>
    simp only [wrap0_query_bind]
    exact hc u _ (fun x H ↦ PQ.Interactive.wrap0 (h H) (k x H)) q ih
  | eval x k q _ ih =>
    exact PUE.eval x (fun y H ↦ PQ.Interactive.wrap0 (h H) (k y H)) _ ih

end PQ.Interactive

open PQ.Interactive in
#print axioms PUE.wrap0E
open PQ.Interactive in
#print axioms WCount.bind
