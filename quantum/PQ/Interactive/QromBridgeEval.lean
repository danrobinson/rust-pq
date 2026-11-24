import PQ.Interactive.QromBridgeCall
import PQ.QROM.Fidelity
import PQ.QROM.Hybrid

/-!
# Port-uniform machines with classical evaluations of the port function

`PUE cnt Mach q`: as `PU` (`QromBridgeUnif.lean`), with one more kind of node — a CLASSICAL
EVALUATION of the port function at a point `x`, whose value steers the rest of the machine
(`fun H ↦ k (H x) H`) — and a weight `cnt t` charged for every classical query `t` of the
interface (the budget reserved for the evaluations its implementation will make).  `q` bounds, on
every path, the number of port calls plus evaluations plus weights.

* closure: `PUE.bind`, `PUE.liftQ_bind` (weighted count `WCount`), `PUE.map`, `PUE.wrap`,
  `PUE.wrap0`;
* `EvalCost f n`: the family of classical computations `f : (X → Y) → ProbComp γ` can be run in
  front of any machine at the price of `n` evaluations; `EvalCost.const`, `.eval`, `.bind`,
  `.simulateQ`;
* `PUE.close`: closing with an implementation that DEPENDS on the port function, each answer of
  cost `cnt t`, gives a closed `PUE` machine with the same bound;

`PUE.compileQ`, `PUE.exists_prog(_qprob)` (an evaluation node as VCVio's `QComp.callBasis` on
the program register, by `run₂_callBasis_branch`) and `PUE.exists_model` are in
`PQ/Interactive/QromBridgeEvalProg.lean`.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] {α β γ : Type} {ι : Type} {spec : OracleSpec ι}

/-! ## Weighted query counts of classical programs -/

/-- Every path of `P` has total weight at most `n`, a query `t` weighing `w t`. -/
def WCount {κ : Type} {sp : OracleSpec κ} (w : sp.Domain → ℕ) (P : OracleComp sp α) : ℕ → Prop :=
  OracleComp.construct (C := fun _ ↦ ℕ → Prop)
    (fun _ _ ↦ True)
    (fun t _ ih n ↦ w t ≤ n ∧ ∀ r, ih r (n - w t)) P

lemma wCount_pure {κ : Type} {sp : OracleSpec κ} (w : sp.Domain → ℕ) (a : α) (n : ℕ) :
    WCount w (pure a : OracleComp sp α) n := trivial

lemma wCount_query_bind {κ : Type} {sp : OracleSpec κ} (w : sp.Domain → ℕ) (t : sp.Domain)
    (k : sp.Range t → OracleComp sp α) (n : ℕ) :
    WCount w (liftM (sp.query t) >>= k) n = (w t ≤ n ∧ ∀ r, WCount w (k r) (n - w t)) := rfl

lemma WCount.mono {κ : Type} {sp : OracleSpec κ} {w : sp.Domain → ℕ} {P : OracleComp sp α}
    {n : ℕ} (h : WCount w P n) : ∀ {n' : ℕ}, n ≤ n' → WCount w P n' := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a => exact fun _ ↦ trivial
  | query_bind t k ih =>
    intro n' hn
    rw [wCount_query_bind] at h ⊢
    exact ⟨h.1.trans hn, fun r ↦ ih r (h.2 r) (by omega)⟩

/-! ## The predicate -/

/-- Port-uniform families of machines with classical evaluations of the port function; the
classical query `t` weighs `cnt t`. -/
inductive PUE (cnt : spec.Domain → ℕ) {α : Type} :
    ((X → Y) → QOC (WS X Y E) spec α) → ℕ → Prop
  | pure (a : α) (q : ℕ) : PUE cnt (fun _ ↦ Pure.pure a) q
  | instr (j : InstrIdx ((X × Y) × E)) (k : Fin (j.1 + 1) → (X → Y) → QOC (WS X Y E) spec α)
      (q : ℕ) (h : ∀ i, PUE cnt (k i) q) :
      PUE cnt (fun H ↦ liftM ((instrSpec (WS X Y E) + spec).query (Sum.inl (framedIdx j))) >>=
        fun i ↦ k i H) q
  | port (k : (X → Y) → QOC (WS X Y E) spec α) (q : ℕ) (h : PUE cnt k q) :
      PUE cnt (fun H ↦ liftM ((instrSpec (WS X Y E) + spec).query (Sum.inl (portIdx H))) >>=
        fun _ ↦ k H) (q + 1)
  | query (t : spec.Domain) (k : spec.Range t → (X → Y) → QOC (WS X Y E) spec α) (q : ℕ)
      (h : ∀ r, PUE cnt (k r) q) :
      PUE cnt (fun H ↦ liftM ((instrSpec (WS X Y E) + spec).query (Sum.inr t)) >>=
        fun r ↦ k r H) (q + cnt t)
  | eval (x : X) (k : Y → (X → Y) → QOC (WS X Y E) spec α) (q : ℕ)
      (h : ∀ y, PUE cnt (k y) q) : PUE cnt (fun H ↦ k (H x) H) (q + 1)

/-- A port-uniform machine is also a machine with a budget for classical port evaluations. -/
theorem PU.toPUE {α : Type} {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (h : PU A q) :
    PUE (fun _ => 0) A q := by
  induction h with
  | pure a q => exact PUE.pure a q
  | instr j k q _ ih => exact PUE.instr j k q ih
  | port k q _ ih => exact PUE.port k q ih
  | query t k q _ ih => exact PUE.query t k q ih

namespace PUE

variable {cnt : spec.Domain → ℕ}

theorem mono {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (h : PUE cnt A q) :
    ∀ {q' : ℕ}, q ≤ q' → PUE cnt A q' := by
  induction h with
  | pure a q => exact fun _ ↦ PUE.pure a _
  | instr j k q _ ih => exact fun hq ↦ PUE.instr j k _ fun i ↦ ih i hq
  | port k q _ ih =>
    intro q' hq
    obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
    exact PUE.port k q'' (ih (by omega))
  | query t k q _ ih =>
    intro q' hq
    obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + cnt t := ⟨q' - cnt t, by omega⟩
    exact PUE.query t k q'' fun r ↦ ih r (by omega)
  | eval x k q _ ih =>
    intro q' hq
    obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
    exact PUE.eval x k q'' fun y ↦ ih y (by omega)

theorem bind {A : (X → Y) → QOC (WS X Y E) spec α}
    {B : α → (X → Y) → QOC (WS X Y E) spec β} {q₁ q₂ : ℕ} (hA : PUE cnt A q₁)
    (hB : ∀ a, PUE cnt (B a) q₂) : PUE cnt (fun H ↦ A H >>= fun a ↦ B a H) (q₁ + q₂) := by
  induction hA with
  | pure a q =>
    simp only [pure_bind]
    exact (hB a).mono (by omega)
  | instr j k q _ ih =>
    simp only [bind_assoc]
    exact PUE.instr j (fun i H ↦ k i H >>= fun a ↦ B a H) _ ih
  | port k q _ ih =>
    simp only [bind_assoc]
    rw [Nat.add_right_comm]
    exact PUE.port (fun H ↦ k H >>= fun a ↦ B a H) _ ih
  | query t k q _ ih =>
    simp only [bind_assoc]
    rw [Nat.add_right_comm]
    exact PUE.query t (fun r H ↦ k r H >>= fun a ↦ B a H) _ ih
  | eval x k q _ ih =>
    rw [Nat.add_right_comm]
    exact PUE.eval x (fun y H ↦ k y H >>= fun a ↦ B a H) _ ih

theorem liftQ_bind (ob : OracleComp spec γ) {B : γ → (X → Y) → QOC (WS X Y E) spec β} {q n : ℕ}
    (hn : WCount cnt ob n) (hB : ∀ c, PUE cnt (B c) q) :
    PUE cnt (fun H ↦ liftQ ob >>= fun c ↦ B c H) (q + n) := by
  induction ob using OracleComp.inductionOn generalizing n with
  | pure a =>
    simp only [liftQ_pure, pure_bind]
    exact (hB a).mono (by omega)
  | query_bind t k ih =>
    rw [wCount_query_bind] at hn
    simp only [liftQ_query_bind, bind_assoc]
    have e : q + n = (q + (n - cnt t)) + cnt t := by omega
    rw [e]
    exact PUE.query t (fun r H ↦ liftQ (k r) >>= fun c ↦ B c H) _ fun r ↦ ih r (hn.2 r)

theorem map (f : α → β) {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (hA : PUE cnt A q) :
    PUE cnt (fun H ↦ f <$> A H) q := by
  have h := bind hA (B := fun a _ ↦ Pure.pure (f a)) (q₂ := 0) fun a ↦ PUE.pure (f a) 0
  simpa [map_eq_bind_pure_comp] using h

variable {ι' : Type} {spec' : OracleSpec ι'} {σ τ : Type}

theorem wrap (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec'))))
    {cnt' : (unifSpec + spec').Domain → ℕ}
    (hc : ∀ t s, WCount cnt' ((implB t).run s) (cnt t))
    {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (hA : PUE cnt A q) :
    ∀ t : τ, PUE cnt' (fun H ↦ PQ.Interactive.wrap implB (A H) t) q := by
  induction hA with
  | pure a q =>
    intro t
    simp only [wrap_pure]
    exact PUE.pure _ _
  | instr j k q _ ih =>
    intro t
    simp only [wrap_instr_bind]
    exact PUE.instr j (fun i H ↦ PQ.Interactive.wrap implB (k i H) t) _ fun i ↦ ih i t
  | port k q _ ih =>
    intro t
    simp only [wrap_instr_bind]
    exact PUE.port (fun H ↦ PQ.Interactive.wrap implB (k H) t) _ (ih t)
  | query u k q _ ih =>
    intro t
    simp only [wrap_query_bind]
    exact liftQ_bind _ (hc u t) fun x ↦ ih x.1 x.2
  | eval x k q _ ih =>
    intro t
    exact PUE.eval x (fun y H ↦ PQ.Interactive.wrap implB (k y H) t) _ fun y ↦ ih y t

theorem wrap0 (h : QueryImpl spec (OracleComp (unifSpec + spec')))
    {cnt' : (unifSpec + spec').Domain → ℕ} (hc : ∀ t, WCount cnt' (h t) (cnt t))
    {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (hA : PUE cnt A q) :
    PUE cnt' (fun H ↦ PQ.Interactive.wrap0 h (A H)) q := by
  induction hA with
  | pure a q =>
    simp only [wrap0_pure]
    exact PUE.pure _ _
  | instr j k q _ ih =>
    simp only [wrap0_instr_bind]
    exact PUE.instr j (fun i H ↦ PQ.Interactive.wrap0 h (k i H)) _ ih
  | port k q _ ih =>
    simp only [wrap0_instr_bind]
    exact PUE.port (fun H ↦ PQ.Interactive.wrap0 h (k H)) _ ih
  | query u k q _ ih =>
    simp only [wrap0_query_bind]
    exact liftQ_bind _ (hc u) ih
  | eval x k q _ ih =>
    exact PUE.eval x (fun y H ↦ PQ.Interactive.wrap0 h (k y H)) _ ih

end PUE

/-! ## Classical computations that depend on the port function -/

/-- The closed-machine weight: sampling is free. -/
abbrev cnt0 : unifSpec.Domain → ℕ := fun _ ↦ 0

/-- `f H`, a classical computation depending on the port function, can be run in front of any
closed port-uniform machine at the price of `n` evaluations. -/
def EvalCost (f : (X → Y) → ProbComp γ) (n : ℕ) : Prop :=
  ∀ (E : Type) [Fintype E] [DecidableEq E] (β : Type)
    (B : γ → (X → Y) → Closed (WS X Y E) β) (q : ℕ),
    (∀ c, PUE (spec := unifSpec) cnt0 (B c) q) →
      PUE (spec := unifSpec) cnt0 (fun H ↦ liftU (f H) >>= fun c ↦ B c H) (q + n)

namespace EvalCost

theorem mono {f : (X → Y) → ProbComp γ} {n n' : ℕ} (h : EvalCost f n) (hn : n ≤ n') :
    EvalCost f n' := fun E _ _ β B q hB ↦ (h E β B q hB).mono (by omega)

/-- A computation that does not depend on the port function is free. -/
theorem const (oa : ProbComp γ) : EvalCost (X := X) (Y := Y) (fun _ ↦ oa) 0 := by
  intro E _ _ β B q hB
  have h := PUE.liftQ_bind (cnt := cnt0) (X := X) (Y := Y) (E := E) oa (B := B) (q := q) (n := 0)
    (by
      induction oa using OracleComp.inductionOn with
      | pure a => exact trivial
      | query_bind t k ih =>
        rw [wCount_query_bind]
        exact ⟨le_rfl, fun r ↦ ih r⟩) hB
  exact h

/-- One evaluation. -/
theorem eval (x : X) (d : Y → γ) : EvalCost (fun H : X → Y ↦ (pure (d (H x)) : ProbComp γ)) 1 := by
  intro E _ _ β B q hB
  simp only [liftU_pure, pure_bind]
  exact PUE.eval x (fun y H ↦ B (d y) H) q fun y ↦ hB (d y)

/-- Sequencing adds the costs. -/
theorem bind {δ : Type} {f : (X → Y) → ProbComp γ} {g : γ → (X → Y) → ProbComp δ} {n m : ℕ}
    (hf : EvalCost f n) (hg : ∀ c, EvalCost (g c) m) :
    EvalCost (fun H ↦ f H >>= fun c ↦ g c H) (n + m) := by
  intro E _ _ β B q hB
  simp only [liftU_bind, bind_assoc]
  have h := hf E β (fun c H ↦ liftU (g c H) >>= fun d ↦ B d H) (q + m)
    fun c ↦ hg c E β B q hB
  have e : q + (n + m) = q + m + n := by omega
  rw [e]
  exact h

theorem map {δ : Type} {f : (X → Y) → ProbComp γ} {n : ℕ} (hf : EvalCost f n) (φ : γ → δ) :
    EvalCost (fun H ↦ φ <$> f H) n := by
  have h := bind hf (g := fun c _ ↦ (pure (φ c) : ProbComp δ)) (m := 0)
    fun c ↦ const (pure (φ c))
  simpa [map_eq_bind_pure_comp] using h

/-- Interpreting an open program: every query `t` of the program is answered by a computation of
cost `w t`; a program of weighted count `n` costs `n`. -/
theorem simulateQ {κ : Type} {sp : OracleSpec κ} (impl : (X → Y) → QueryImpl sp ProbComp)
    (w : sp.Domain → ℕ) (hw : ∀ t, EvalCost (fun H ↦ impl H t) (w t))
    (P : OracleComp sp γ) (n : ℕ) (hP : WCount w P n) :
    EvalCost (fun H ↦ simulateQ (impl H) P) n := by
  induction P using OracleComp.inductionOn generalizing n with
  | pure a =>
    simp only [simulateQ_pure]
    exact (const (pure a)).mono (Nat.zero_le _)
  | query_bind t k ih =>
    rw [wCount_query_bind] at hP
    simp only [simulateQ_bind, simulateQ_spec_query]
    have h := bind (hw t) (g := fun r H ↦ _root_.simulateQ (impl H) (k r)) fun r ↦ ih r _ (hP.2 r)
    have e : w t + (n - w t) = n := by omega
    rw [e] at h
    exact h

end EvalCost

/-! ## Closing with an implementation that depends on the port function -/

/-- Closing a port-uniform machine with a stateful probabilistic implementation that depends on
the port function, each answer to `t` costing at most `cnt t` evaluations. -/
theorem PUE.close {σ : Type} {cnt : spec.Domain → ℕ}
    (impl : (X → Y) → QueryImpl spec (StateT σ ProbComp))
    (hc : ∀ t s, EvalCost (fun H ↦ (impl H t).run s) (cnt t))
    {A : (X → Y) → QOC (WS X Y E) spec α} {q : ℕ} (hA : PUE cnt A q) :
    ∀ s : σ, PUE (spec := unifSpec) cnt0 (fun H ↦ PQ.Interactive.close (impl H) (A H) s) q := by
  induction hA with
  | pure a q =>
    intro s
    simp only [close_pure]
    exact PUE.pure _ _
  | instr j k q _ ih =>
    intro s
    simp only [close_instr_bind]
    exact PUE.instr j (fun i H ↦ PQ.Interactive.close (impl H) (k i H) s) _ fun i ↦ ih i s
  | port k q _ ih =>
    intro s
    simp only [close_instr_bind]
    exact PUE.port (fun H ↦ PQ.Interactive.close (impl H) (k H) s) _ (ih s)
  | query u k q _ ih =>
    intro s
    simp only [close_query_bind]
    exact hc u s E _ (fun x H ↦ PQ.Interactive.close (impl H) (k x.1 H) x.2) q
      fun x ↦ ih x.1 x.2
  | eval x k q _ ih =>
    intro s
    exact PUE.eval x (fun y H ↦ PQ.Interactive.close (impl H) (k y H) s) _ fun y ↦ ih y s

/-- A classical computation depending on the port function, in front of a closed machine. -/
theorem PUE.liftU_bind {f : (X → Y) → ProbComp γ} {n : ℕ} (hf : EvalCost f n)
    {B : γ → (X → Y) → Closed (WS X Y E) β} {q : ℕ}
    (hB : ∀ c, PUE (spec := unifSpec) cnt0 (B c) q) :
    PUE (spec := unifSpec) cnt0 (fun H ↦ liftU (f H) >>= fun c ↦ B c H) (q + n) :=
  hf E β B q hB

end PQ.Interactive

open PQ.Interactive in
#print axioms PUE.bind
open PQ.Interactive in
#print axioms PUE.wrap
open PQ.Interactive in
#print axioms PUE.wrap0
open PQ.Interactive in
#print axioms EvalCost.simulateQ
open PQ.Interactive in
#print axioms PUE.close
