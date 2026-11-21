import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.SimSemantics.Append.Core
import VCVio.OracleComp.ProbComp.Basic
import QuantumFoundations.SubInstrument

/-!
# Quantum adversaries with a classical oracle interface

A quantum machine with workspace basis `W` and classical oracle interface `spec` is a classical
control tree `QOC W spec α = OracleComp (instrSpec W + spec) α`.  Its nodes are

* oracle queries to `spec` (classical question, classical answer), and
* *instrument nodes*: apply an arbitrary lossless quantum instrument
  `I : SubInstrument W W (Fin (n+1))` to the workspace and branch on its classical outcome.

Unitaries are one-outcome instruments, measurements are many-outcome instruments, ancillas live
inside `W`, and the classical control may depend on all earlier outcomes and oracle answers.

`qWeight p X ρ` is the Born-rule semantics of a *closed* machine `X` (only instrument nodes and
uniform sampling left) started in the unnormalised state `ρ`: the total trace of the unnormalised
post-states of all leaves whose output satisfies `p`.

`close impl Q s` closes an open machine by substituting the classical stateful probabilistic code
`impl : QueryImpl spec (StateT σ ProbComp)` for its oracle queries.
-/

open OracleComp OracleSpec ENNReal Quantum
open scoped ComplexOrder

namespace PQ.Interactive

/-! ## Syntax -/

/-- Index of an instrument node: a lossless instrument on the workspace with `n + 1` outcomes. -/
abbrev InstrIdx (W : Type) [Fintype W] : Type :=
  Σ n : ℕ, {I : SubInstrument W W (Fin (n + 1)) // I.Lossless}

/-- The oracle family "apply a lossless quantum instrument to the workspace, return its outcome". -/
@[reducible] def instrSpec (W : Type) [Fintype W] : OracleSpec (InstrIdx W) := fun j ↦ Fin (j.1 + 1)

/-- Quantum-classical oracle computations: classical control trees over instrument nodes on the
workspace `W` and classical queries to `spec`. -/
abbrev QOC (W : Type) [Fintype W] {ι : Type} (spec : OracleSpec ι) (α : Type) : Type :=
  OracleComp (instrSpec W + spec) α

/-- A closed machine: only instrument nodes and uniform sampling. -/
abbrev Closed (W : Type) [Fintype W] (α : Type) : Type := OracleComp (instrSpec W + unifSpec) α

variable {W : Type} [Fintype W] {α β : Type}

instance (j : InstrIdx W) : Fintype ((instrSpec W).Range j) :=
  inferInstanceAs (Fintype (Fin (j.1 + 1)))

/-- The instrument node `I` as a machine over any classical interface. -/
def instr {ι : Type} {spec : OracleSpec ι} {n : ℕ} (I : SubInstrument W W (Fin (n + 1)))
    (hI : I.Lossless) : QOC W spec (Fin (n + 1)) :=
  liftM ((instrSpec W + spec).query (Sum.inl ⟨n, I, hI⟩))

/-- Embed classical probabilistic code into closed machines. -/
def liftU (oa : ProbComp α) : Closed W α :=
  simulateQ (fun n ↦ liftM ((instrSpec W + unifSpec).query (Sum.inr n))) oa

@[simp] lemma liftU_pure (a : α) : (liftU (pure a) : Closed W α) = pure a := by
  simp [liftU]

@[simp] lemma liftU_bind (oa : ProbComp α) (f : α → ProbComp β) :
    (liftU (oa >>= f) : Closed W β) = liftU oa >>= fun a ↦ liftU (f a) := by
  simp [liftU]

@[simp] lemma liftU_map (oa : ProbComp α) (f : α → β) :
    (liftU (f <$> oa) : Closed W β) = f <$> liftU oa := by
  simp [liftU]

lemma liftU_query (n : ℕ) :
    (liftU (liftM (unifSpec.query n)) : Closed W _) =
      liftM ((instrSpec W + unifSpec).query (Sum.inr n)) := by
  simp [liftU]

lemma liftU_query_bind (n : ℕ) (k : Fin (n + 1) → ProbComp α) :
    (liftU (liftM (unifSpec.query n) >>= k) : Closed W α) =
      liftM ((instrSpec W + unifSpec).query (Sum.inr n)) >>= fun i ↦ liftU (k i) := by
  rw [liftU_bind, liftU_query]
  rfl

/-! ## Born-rule semantics of closed machines -/

/-- Born weight of the event `p` for the closed machine `X` started in the unnormalised state `ρ`.

* leaf `a`: the trace of the state if `p a`, else `0`;
* instrument node `I`, continuation `k`: `∑ i, weight (k i) (I.branch i ρ)` (unnormalised
  post-measurement states, so the factor "probability of outcome `i`" is carried by the trace);
* uniform node `n`: the average over the `n + 1` answers. -/
noncomputable def qWeight (p : α → Prop) [DecidablePred p] (X : Closed W α) :
    Matrix W W ℂ → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ ↦ Matrix W W ℂ → ℝ≥0∞)
    (fun a ρ ↦ if p a then ENNReal.ofReal ρ.trace.re else 0)
    (fun t _ ih ρ ↦
      match t, ih with
      | .inl j, ih => ∑ i, ih i (j.2.1.branch i ρ)
      | .inr n, ih => ((n : ℝ≥0∞) + 1)⁻¹ * ∑ i : Fin (n + 1), ih i ρ) X

section qWeight

variable (p : α → Prop) [DecidablePred p]

@[simp] lemma qWeight_pure (a : α) (ρ : Matrix W W ℂ) :
    qWeight p (pure a : Closed W α) ρ = if p a then ENNReal.ofReal ρ.trace.re else 0 := rfl

lemma qWeight_instr_bind (j : InstrIdx W) (k : Fin (j.1 + 1) → Closed W α) (ρ : Matrix W W ℂ) :
    qWeight p (liftM ((instrSpec W + unifSpec).query (Sum.inl j)) >>= k) ρ =
      ∑ i, qWeight p (k i) (j.2.1.branch i ρ) := rfl

lemma qWeight_unif_bind (n : ℕ) (k : Fin (n + 1) → Closed W α) (ρ : Matrix W W ℂ) :
    qWeight p (liftM ((instrSpec W + unifSpec).query (Sum.inr n)) >>= k) ρ =
      ((n : ℝ≥0∞) + 1)⁻¹ * ∑ i, qWeight p (k i) ρ := rfl

end qWeight

/-! ### Sanity of the semantics -/

lemma posSemidef_branch (j : InstrIdx W) (i : Fin (j.1 + 1)) {ρ : Matrix W W ℂ}
    (hρ : ρ.PosSemidef) : (j.2.1.branch i ρ).PosSemidef :=
  (j.2.1.isCP_branch i).posSemidef hρ

/-- Losslessness: the outcome weights of an instrument node add up to the weight of the state. -/
lemma sum_ofReal_trace_branch (j : InstrIdx W) {ρ : Matrix W W ℂ} (hρ : ρ.PosSemidef) :
    ∑ i, ENNReal.ofReal (j.2.1.branch i ρ).trace.re = ENNReal.ofReal ρ.trace.re := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ (posSemidef_branch j i hρ).trace_re_nonneg,
    ← Complex.re_sum]
  congr 2
  exact j.2.2.sum_trace_eq (s := Finset.univ) (by simp) ρ

lemma unif_avg_const (n : ℕ) (c : ℝ≥0∞) :
    ((n : ℝ≥0∞) + 1)⁻¹ * ∑ _i : Fin (n + 1), c = c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    Nat.cast_add, Nat.cast_one, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

/-- Monotonicity in the event. -/
lemma qWeight_mono {p q : α → Prop} [DecidablePred p] [DecidablePred q] (h : ∀ a, p a → q a)
    (X : Closed W α) (ρ : Matrix W W ℂ) : qWeight p X ρ ≤ qWeight q X ρ := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a =>
    simp only [qWeight_pure]
    by_cases hp : p a
    · simp [hp, h a hp]
    · simp [hp]
  | query_bind t k ih =>
    rcases t with j | n
    · rw [qWeight_instr_bind, qWeight_instr_bind]
      exact Finset.sum_le_sum fun i _ ↦ ih i _
    · rw [qWeight_unif_bind, qWeight_unif_bind]
      gcongr with i _
      exact ih i _

/-- Additivity over disjoint events. -/
lemma qWeight_or {p q : α → Prop} [DecidablePred p] [DecidablePred q] (h : ∀ a, p a → ¬ q a)
    (X : Closed W α) (ρ : Matrix W W ℂ) :
    qWeight (fun a ↦ p a ∨ q a) X ρ = qWeight p X ρ + qWeight q X ρ := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a =>
    simp only [qWeight_pure]
    by_cases hp : p a
    · simp [hp, h a hp]
    · simp [hp]
  | query_bind t k ih =>
    rcases t with j | n
    · simp only [qWeight_instr_bind, ih, Finset.sum_add_distrib]
    · simp only [qWeight_unif_bind, ih, Finset.sum_add_distrib, mul_add]

/-- The trivial event has the full weight of the state: instruments are lossless and classical
sampling is a probability distribution.  In particular the weight is `1` on a normalised state. -/
lemma qWeight_true (X : Closed W α) {ρ : Matrix W W ℂ} (hρ : ρ.PosSemidef) :
    qWeight (fun _ ↦ True) X ρ = ENNReal.ofReal ρ.trace.re := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | n
    · rw [qWeight_instr_bind]
      simp only [ih _ (posSemidef_branch j _ hρ)]
      exact sum_ofReal_trace_branch j hρ
    · rw [qWeight_unif_bind]
      simp only [ih _ hρ]
      exact unif_avg_const n _

/-- Every event has weight at most the trace of the state. -/
lemma qWeight_le_trace (p : α → Prop) [DecidablePred p] (X : Closed W α) {ρ : Matrix W W ℂ}
    (hρ : ρ.PosSemidef) : qWeight p X ρ ≤ ENNReal.ofReal ρ.trace.re :=
  (qWeight_mono (fun _ _ ↦ trivial) X ρ).trans_eq (qWeight_true X hρ)

/-- On a density matrix the trivial event has probability one. -/
lemma qWeight_true_eq_one (X : Closed W α) {ρ : Matrix W W ℂ} (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) : qWeight (fun _ ↦ True) X ρ = 1 := by
  simp [qWeight_true X hρ, h1]

lemma qWeight_le_one (p : α → Prop) [DecidablePred p] (X : Closed W α) {ρ : Matrix W W ℂ}
    (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) : qWeight p X ρ ≤ 1 := by
  simpa [h1] using qWeight_le_trace p X hρ

/-- The event and its complement share the weight of the state. -/
lemma qWeight_add_not (p : α → Prop) [DecidablePred p] (X : Closed W α) {ρ : Matrix W W ℂ}
    (hρ : ρ.PosSemidef) :
    qWeight p X ρ + qWeight (fun a ↦ ¬ p a) X ρ = ENNReal.ofReal ρ.trace.re := by
  rw [← qWeight_or (fun a hp hn ↦ hn hp), ← qWeight_true X hρ]
  exact le_antisymm (qWeight_mono (fun _ _ ↦ trivial) X ρ)
    (qWeight_mono (fun a _ ↦ Classical.em (p a)) X ρ)

/-- If no continuation can produce the event, neither can the composite. -/
lemma qWeight_bind_eq_zero {γ : Type} (p : α → Prop) [DecidablePred p] (X : Closed W γ)
    (F : γ → Closed W α) (h : ∀ x ρ, qWeight p (F x) ρ = 0) (ρ : Matrix W W ℂ) :
    qWeight p (X >>= F) ρ = 0 := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => simpa using h a ρ
  | query_bind t k ih =>
    rcases t with j | n
    · rw [bind_assoc, qWeight_instr_bind]
      simp [ih]
    · rw [bind_assoc, qWeight_unif_bind]
      simp [ih]

/-- Relabelling the output. -/
lemma qWeight_map {γ : Type} (f : γ → α) (p : α → Prop) [DecidablePred p] (X : Closed W γ)
    (ρ : Matrix W W ℂ) : qWeight p (f <$> X) ρ = qWeight (fun x ↦ p (f x)) X ρ := by
  induction X using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | n
    · rw [map_bind, qWeight_instr_bind, qWeight_instr_bind]
      simp only [ih]
    · rw [map_bind, qWeight_unif_bind, qWeight_unif_bind]
      simp only [ih]

/-! ## Closing an open machine -/

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- The handler that closes a machine: instrument nodes are kept, classical queries are answered
by the stateful probabilistic code `impl`. -/
def closeImpl (W : Type) [Fintype W] (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl (instrSpec W + spec) (StateT σ (Closed W))
  | .inl j => fun s ↦ (fun i ↦ (i, s)) <$>
      (liftM ((instrSpec W + unifSpec).query (Sum.inl j)) : Closed W _)
  | .inr t => fun s ↦ liftU ((impl t).run s)

/-- The closed machine obtained from `Q` by answering its classical queries with `impl`, started
from the oracle state `s`; it returns the output of `Q` and the final oracle state. -/
def close (impl : QueryImpl spec (StateT σ ProbComp)) (Q : QOC W spec α) (s : σ) :
    Closed W (α × σ) :=
  (simulateQ (closeImpl W impl) Q).run s

@[simp] lemma close_pure (impl : QueryImpl spec (StateT σ ProbComp)) (a : α) (s : σ) :
    close (W := W) impl (pure a) s = pure (a, s) := by
  simp [close]

lemma close_bind (impl : QueryImpl spec (StateT σ ProbComp)) (Q : QOC W spec α)
    (f : α → QOC W spec β) (s : σ) :
    close impl (Q >>= f) s = close impl Q s >>= fun x ↦ close impl (f x.1) x.2 := by
  simp [close]

lemma close_instr_bind (impl : QueryImpl spec (StateT σ ProbComp)) (j : InstrIdx W)
    (k : Fin (j.1 + 1) → QOC W spec α) (s : σ) :
    close impl (liftM ((instrSpec W + spec).query (Sum.inl j)) >>= k) s =
      liftM ((instrSpec W + unifSpec).query (Sum.inl j)) >>= fun i ↦ close impl (k i) s := by
  unfold close
  rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  change ((fun i ↦ (i, s)) <$> _) >>= _ = _
  simp

lemma close_query_bind (impl : QueryImpl spec (StateT σ ProbComp)) (t : spec.Domain)
    (k : spec.Range t → QOC W spec α) (s : σ) :
    close impl (liftM ((instrSpec W + spec).query (Sum.inr t)) >>= k) s =
      liftU ((impl t).run s) >>= fun x ↦ close impl (k x.1) x.2 := by
  unfold close
  rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  rfl

end PQ.Interactive

open PQ.Interactive in
#print axioms qWeight_true
open PQ.Interactive in
#print axioms qWeight_add_not
open PQ.Interactive in
#print axioms close_query_bind
