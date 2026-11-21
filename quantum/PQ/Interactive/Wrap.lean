import PQ.Interactive.Collapse

/-!
# Black-box wrappers lift to quantum adversaries

A straight-line black-box reduction runs the adversary once, answering its oracle queries by
classical code `implB` that uses uniform sampling and the oracles `spec'` of the reduction's own
game, possibly after classical pre-processing and followed by classical post-processing.

`wrap implB Q t` is the quantum machine obtained by putting this classical code around the quantum
adversary `Q` (instrument nodes untouched).  The theorems:

* `toProbComp_wrap`: classicalising the wrapped quantum machine *is* the wrapper applied to the
  classical strategy of `Q` (equality of programs);
* `rationalBorn_wrap`: wrapping preserves rationality of the Born probabilities;
* `qWeight_close_wrap`: hence in any game `implG` for the reduction, the Born probability of the
  wrapped quantum machine is the classical probability of the reduction applied to the classical
  strategy;
* `qReduction` and its lemmas: the same with classical pre- and post-processing;
* `runForgerG`: the `runForger`-shaped harness (forward uniform sampling, answer signing queries
  by a signing procedure, record the messages) is an instance.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] {α β γ : Type}
variable {ι : Type} {spec : OracleSpec ι} {ι' : Type} {spec' : OracleSpec ι'} {σ τ : Type}

/-! ## Classical code inside a quantum machine -/

/-- Embed classical oracle code into quantum machines over the same interface. -/
def liftQ (ob : OracleComp spec α) : QOC W spec α :=
  simulateQ (fun t ↦ liftM ((instrSpec W + spec).query (Sum.inr t))) ob

@[simp] lemma liftQ_pure (a : α) : (liftQ (pure a : OracleComp spec α) : QOC W spec α) = pure a := by
  simp [liftQ]

@[simp] lemma liftQ_bind (ob : OracleComp spec α) (f : α → OracleComp spec β) :
    (liftQ (ob >>= f) : QOC W spec β) = liftQ ob >>= fun a ↦ liftQ (f a) := by
  simp [liftQ]

lemma liftQ_query_bind (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    (liftQ (liftM (spec.query t) >>= k) : QOC W spec α) =
      liftM ((instrSpec W + spec).query (Sum.inr t)) >>= fun u ↦ liftQ (k u) := by
  rw [liftQ_bind]
  congr 1

/-- Classical pre-processing commutes with classicalisation. -/
lemma toProbComp_liftQ_bind (ob : OracleComp (unifSpec + spec') γ)
    (F : γ → QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbComp (liftQ ob >>= F) ρ = ob >>= fun x ↦ toProbComp (F x) ρ := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftQ_query_bind, bind_assoc, toProbComp_query_bind, bind_assoc]
    simp only [ih]

@[simp] lemma toProbComp_liftQ (ob : OracleComp (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbComp (liftQ ob : QOC W (unifSpec + spec') α) ρ = ob := by
  simpa using toProbComp_liftQ_bind ob (pure : α → QOC W (unifSpec + spec') α) ρ

/-- Classical post-processing commutes with classicalisation. -/
lemma toProbComp_bind_liftQ (Q : QOC W (unifSpec + spec') α)
    (post : α → OracleComp (unifSpec + spec') β) (ρ : Matrix W W ℂ) :
    toProbComp (Q >>= fun a ↦ liftQ (post a)) ρ = toProbComp Q ρ >>= post := by
  induction Q using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | t
    · rw [bind_assoc, toProbComp_instr_bind, toProbComp_instr_bind, bind_assoc]
      simp only [ih]
    · rw [bind_assoc, toProbComp_query_bind, toProbComp_query_bind, bind_assoc]
      simp only [ih]

lemma rationalBorn_liftQ_bind (ob : OracleComp spec γ) (F : γ → QOC W spec α)
    (ρ : Matrix W W ℂ) (h : ∀ x, RationalBorn (F x) ρ) : RationalBorn (liftQ ob >>= F) ρ := by
  induction ob using OracleComp.inductionOn with
  | pure a => simpa using h a
  | query_bind t k ih =>
    rw [liftQ_query_bind, bind_assoc, rationalBorn_query_bind]
    exact ih

lemma rationalBorn_liftQ (ob : OracleComp spec α) (ρ : Matrix W W ℂ) :
    RationalBorn (liftQ ob : QOC W spec α) ρ := by
  simpa using rationalBorn_liftQ_bind ob (pure : α → QOC W spec α) ρ (by simp)

lemma rationalBorn_bind_liftQ (Q : QOC W spec α) (post : α → OracleComp spec β)
    (ρ : Matrix W W ℂ) (h : RationalBorn Q ρ) :
    RationalBorn (Q >>= fun a ↦ liftQ (post a)) ρ := by
  induction Q using OracleComp.inductionOn generalizing ρ with
  | pure a => simpa using rationalBorn_liftQ (post a) ρ
  | query_bind t k ih =>
    rcases t with j | t
    · rw [rationalBorn_instr_bind] at h
      rw [bind_assoc, rationalBorn_instr_bind]
      exact ⟨h.1, fun i ↦ ih i _ (h.2 i)⟩
    · rw [rationalBorn_query_bind] at h
      rw [bind_assoc, rationalBorn_query_bind]
      exact fun u ↦ ih u _ (h u)

/-! ## Wrapping a quantum machine in classical simulation code -/

/-- The handler that wraps a machine: instrument nodes are kept, the classical queries of the
machine are answered by the classical code `implB`, which runs over the interface
`unifSpec + spec'`. -/
def wrapImpl (W : Type) [Fintype W]
    (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec')))) :
    QueryImpl (instrSpec W + spec) (StateT τ (QOC W (unifSpec + spec')))
  | .inl j => fun t ↦ (fun i ↦ (i, t)) <$>
      (liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inl j)) : QOC W (unifSpec + spec') _)
  | .inr q => fun t ↦ liftQ ((implB q).run t)

/-- The quantum machine "`implB`'s code around `Q`", started from the wrapper state `t`. -/
def wrap (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec')))) (Q : QOC W spec α)
    (t : τ) : QOC W (unifSpec + spec') (α × τ) :=
  (simulateQ (wrapImpl W implB) Q).run t

@[simp] lemma wrap_pure (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec'))))
    (a : α) (t : τ) : wrap (W := W) implB (pure a) t = pure (a, t) := by
  simp [wrap]

lemma wrap_instr_bind (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec'))))
    (j : InstrIdx W) (k : Fin (j.1 + 1) → QOC W spec α) (t : τ) :
    wrap implB (liftM ((instrSpec W + spec).query (Sum.inl j)) >>= k) t =
      liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inl j)) >>=
        fun i ↦ wrap implB (k i) t := by
  unfold wrap
  rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  change ((fun i ↦ (i, t)) <$> _) >>= _ = _
  simp

lemma wrap_query_bind (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec'))))
    (q : spec.Domain) (k : spec.Range q → QOC W spec α) (t : τ) :
    wrap implB (liftM ((instrSpec W + spec).query (Sum.inr q)) >>= k) t =
      liftQ ((implB q).run t) >>= fun x ↦ wrap implB (k x.1) x.2 := by
  unfold wrap
  rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
  rfl

/-- The wrapper answers the adversary's uniform-sampling queries by sampling, without touching
its state. -/
def ForwardsUnifB
    (implB : QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec')))) : Prop :=
  ∀ (n : ℕ) (t : τ), (implB (Sum.inl n)).run t =
    (fun u ↦ (u, t)) <$> (liftM ((unifSpec + spec').query (Sum.inl n)) : OracleComp _ _)

lemma ForwardsUnifB.run_simulateQ_liftL_bind
    {implB : QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec')))}
    (h : ForwardsUnifB implB) (oa : ProbComp γ) (K : γ → OracleComp (unifSpec + spec) α) (t : τ) :
    (simulateQ implB (liftL oa >>= K)).run t =
      liftL oa >>= fun u ↦ (simulateQ implB (K u)).run t := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [liftL]
  | query_bind n k ih =>
    have e1 : (liftL (liftM (unifSpec.query n) >>= k) : OracleComp (unifSpec + spec) γ) =
        liftM ((unifSpec + spec).query (Sum.inl n)) >>= fun i ↦ liftL (k i) := by
      simp [liftL]
    have e2 : (liftL (liftM (unifSpec.query n) >>= k) : OracleComp (unifSpec + spec') γ) =
        liftM ((unifSpec + spec').query (Sum.inl n)) >>= fun i ↦ liftL (k i) := by
      simp [liftL]
    rw [e1, e2, bind_assoc, bind_assoc, simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
      h n t, bind_map_left]
    simp only [ih]

/-- **Wrapping commutes with classicalisation (T2, program form).**  The classical strategy of
the quantum machine "`implB` around `Q`" is `implB` run on the classical strategy of `Q`. -/
theorem toProbComp_wrap
    (implB : QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (hB : ForwardsUnifB implB) (Q : QOC W (unifSpec + spec) α) (t : τ) (ρ : Matrix W W ℂ) :
    toProbComp (wrap implB Q t) ρ = (simulateQ implB (toProbComp Q ρ)).run t := by
  induction Q using OracleComp.inductionOn generalizing t ρ with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [wrap_instr_bind, toProbComp_instr_bind, toProbComp_instr_bind,
        hB.run_simulateQ_liftL_bind]
      simp only [ih]
    · rw [wrap_query_bind, toProbComp_liftQ_bind, toProbComp_query_bind, simulateQ_bind,
        StateT.run_bind, simulateQ_spec_query]
      simp only [ih]

/-- Wrapping preserves rationality of the Born probabilities. -/
theorem rationalBorn_wrap (implB : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec'))))
    (Q : QOC W spec α) (t : τ) (ρ : Matrix W W ℂ) (h : RationalBorn Q ρ) :
    RationalBorn (wrap implB Q t) ρ := by
  induction Q using OracleComp.inductionOn generalizing t ρ with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [rationalBorn_instr_bind] at h
      rw [wrap_instr_bind, rationalBorn_instr_bind]
      exact ⟨h.1, fun i ↦ ih i _ _ (h.2 i)⟩
    · rw [rationalBorn_query_bind] at h
      rw [wrap_query_bind]
      exact rationalBorn_liftQ_bind _ _ _ fun x ↦ ih _ _ _ (h _)

/-- **Black-box wrappers lift (T2).**  In every game `implG` for the reduction, the Born
probability of an event of the quantum machine "`implB` around `Q`" equals the classical
probability of the same event for the reduction `implB` applied to the classical strategy of
`Q`. -/
theorem qWeight_close_wrap
    (implG : QueryImpl (unifSpec + spec') (StateT σ ProbComp)) (hG : ForwardsUnif implG)
    (implB : QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (hB : ForwardsUnifB implB) (p : (α × τ) × σ → Prop) [DecidablePred p]
    (Q : QOC W (unifSpec + spec) α) (t : τ) (s : σ) (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) (hQ : RationalBorn Q ρ) :
    qWeight p (close implG (wrap implB Q t) s) ρ =
      Pr{let y ← (simulateQ implG ((simulateQ implB (toProbComp Q ρ)).run t)).run s}[p y] := by
  rw [qWeight_close_eq implG hG p _ s ρ hρ h1 (rationalBorn_wrap implB Q t ρ hQ),
    toProbComp_wrap implB hB]

/-! ## Reductions with classical pre- and post-processing -/

/-- The quantum machine of a straight-line black-box reduction: classical pre-processing `pre`,
then the quantum adversary `Q a` run once inside the classical simulation `implB a` from the
wrapper state `t₀ a`, then classical post-processing `post a`. -/
def qReduction (pre : OracleComp (unifSpec + spec') γ)
    (implB : γ → QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (t₀ : γ → τ) (post : γ → α × τ → OracleComp (unifSpec + spec') β)
    (Q : γ → QOC W (unifSpec + spec) α) : QOC W (unifSpec + spec') β :=
  liftQ pre >>= fun a ↦ wrap (implB a) (Q a) (t₀ a) >>= fun r ↦ liftQ (post a r)

/-- The classical reduction of the same shape applied to a classical adversary `A`. -/
def cReduction (pre : OracleComp (unifSpec + spec') γ)
    (implB : γ → QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (t₀ : γ → τ) (post : γ → α × τ → OracleComp (unifSpec + spec') β)
    (A : γ → OracleComp (unifSpec + spec) α) : OracleComp (unifSpec + spec') β :=
  pre >>= fun a ↦ (simulateQ (implB a) (A a)).run (t₀ a) >>= post a

/-- **The reduction commutes with classicalisation.**  The classical strategy of the quantum
machine "reduction around `Q`" is the classical reduction applied to the classical strategy of
`Q`. -/
theorem toProbComp_qReduction (pre : OracleComp (unifSpec + spec') γ)
    (implB : γ → QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (hB : ∀ a, ForwardsUnifB (implB a)) (t₀ : γ → τ)
    (post : γ → α × τ → OracleComp (unifSpec + spec') β)
    (Q : γ → QOC W (unifSpec + spec) α) (ρ : Matrix W W ℂ) :
    toProbComp (qReduction pre implB t₀ post Q) ρ =
      cReduction pre implB t₀ post fun a ↦ toProbComp (Q a) ρ := by
  unfold qReduction cReduction
  rw [toProbComp_liftQ_bind]
  refine bind_congr fun a ↦ ?_
  rw [toProbComp_bind_liftQ, toProbComp_wrap _ (hB a)]

theorem rationalBorn_qReduction (pre : OracleComp (unifSpec + spec') γ)
    (implB : γ → QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (t₀ : γ → τ) (post : γ → α × τ → OracleComp (unifSpec + spec') β)
    (Q : γ → QOC W (unifSpec + spec) α) (ρ : Matrix W W ℂ) (hQ : ∀ a, RationalBorn (Q a) ρ) :
    RationalBorn (qReduction pre implB t₀ post Q) ρ :=
  rationalBorn_liftQ_bind _ _ _ fun a ↦
    rationalBorn_bind_liftQ _ _ _ (rationalBorn_wrap _ _ _ _ (hQ a))

/-- **Reductions lift (T2 with pre/post-processing).**  In every game `implG`, the quantum
machine "reduction around `Q`" succeeds with exactly the probability of the classical reduction
applied to the classical strategy of `Q`. -/
theorem qWeight_close_qReduction
    (implG : QueryImpl (unifSpec + spec') (StateT σ ProbComp)) (hG : ForwardsUnif implG)
    (pre : OracleComp (unifSpec + spec') γ)
    (implB : γ → QueryImpl (unifSpec + spec) (StateT τ (OracleComp (unifSpec + spec'))))
    (hB : ∀ a, ForwardsUnifB (implB a)) (t₀ : γ → τ)
    (post : γ → α × τ → OracleComp (unifSpec + spec') β)
    (Q : γ → QOC W (unifSpec + spec) α) (p : β × σ → Prop) [DecidablePred p] (s : σ)
    (ρ : Matrix W W ℂ) (hρ : ρ.PosSemidef) (h1 : ρ.trace = 1) (hQ : ∀ a, RationalBorn (Q a) ρ) :
    qWeight p (close implG (qReduction pre implB t₀ post Q) s) ρ =
      Pr{let y ← (simulateQ implG
        (cReduction pre implB t₀ post fun a ↦ toProbComp (Q a) ρ)).run s}[p y] := by
  rw [qWeight_close_eq implG hG p _ s ρ hρ h1 (rationalBorn_qReduction pre implB t₀ post Q ρ hQ),
    toProbComp_qReduction pre implB hB]

/-- Any wrapper of the form "forward uniform sampling + `impl'`" (the shape of every harness in
the reductions) forwards uniform sampling. -/
lemma forwardsUnifB_ofLift_add (impl' : QueryImpl spec (StateT τ (OracleComp (unifSpec + spec')))) :
    ForwardsUnifB ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec'))).liftTarget
      (StateT τ (OracleComp (unifSpec + spec'))) + impl') := by
  intro n t
  simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply]
  change (liftM (liftM (unifSpec.query n) : OracleComp (unifSpec + spec') _) :
    StateT τ (OracleComp (unifSpec + spec')) _).run t = _
  rw [OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query]
  simp

/-! ## Stateless wrappers and output maps -/

/-- The handler of a stateless wrapper `h` (a translation of the adversary's oracle interface
into another one): instrument nodes are kept. -/
def wrap0Impl (W : Type) [Fintype W] (h : QueryImpl spec (OracleComp (unifSpec + spec'))) :
    QueryImpl (instrSpec W + spec) (QOC W (unifSpec + spec'))
  | .inl j => liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inl j))
  | .inr q => liftQ (h q)

/-- The quantum machine "`h`'s code around `Q`" for a stateless wrapper `h`. -/
def wrap0 (h : QueryImpl spec (OracleComp (unifSpec + spec'))) (Q : QOC W spec α) :
    QOC W (unifSpec + spec') α :=
  simulateQ (wrap0Impl W h) Q

@[simp] lemma wrap0_pure (h : QueryImpl spec (OracleComp (unifSpec + spec'))) (a : α) :
    wrap0 (W := W) h (pure a) = pure a := by
  simp [wrap0]

lemma wrap0_instr_bind (h : QueryImpl spec (OracleComp (unifSpec + spec')))
    (j : InstrIdx W) (k : Fin (j.1 + 1) → QOC W spec α) :
    wrap0 h (liftM ((instrSpec W + spec).query (Sum.inl j)) >>= k) =
      liftM ((instrSpec W + (unifSpec + spec')).query (Sum.inl j)) >>=
        fun i ↦ wrap0 h (k i) := by
  unfold wrap0
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

lemma wrap0_query_bind (h : QueryImpl spec (OracleComp (unifSpec + spec')))
    (q : spec.Domain) (k : spec.Range q → QOC W spec α) :
    wrap0 h (liftM ((instrSpec W + spec).query (Sum.inr q)) >>= k) =
      liftQ (h q) >>= fun x ↦ wrap0 h (k x) := by
  unfold wrap0
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

/-- The stateless wrapper answers the adversary's uniform-sampling queries by sampling. -/
def ForwardsUnif0 (h : QueryImpl (unifSpec + spec) (OracleComp (unifSpec + spec'))) : Prop :=
  ∀ n : ℕ, h (Sum.inl n) = liftM ((unifSpec + spec').query (Sum.inl n))

lemma ForwardsUnif0.simulateQ_liftL_bind
    {h : QueryImpl (unifSpec + spec) (OracleComp (unifSpec + spec'))}
    (hh : ForwardsUnif0 h) (oa : ProbComp γ) (K : γ → OracleComp (unifSpec + spec) α) :
    simulateQ h (liftL oa >>= K) = liftL oa >>= fun u ↦ simulateQ h (K u) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [liftL]
  | query_bind n k ih =>
    have e1 : (liftL (liftM (unifSpec.query n) >>= k) : OracleComp (unifSpec + spec) γ) =
        liftM ((unifSpec + spec).query (Sum.inl n)) >>= fun i ↦ liftL (k i) := by
      simp [liftL]
    have e2 : (liftL (liftM (unifSpec.query n) >>= k) : OracleComp (unifSpec + spec') γ) =
        liftM ((unifSpec + spec').query (Sum.inl n)) >>= fun i ↦ liftL (k i) := by
      simp [liftL]
    rw [e1, e2, bind_assoc, bind_assoc, simulateQ_bind, simulateQ_spec_query, hh n]
    simp only [ih]
    rfl

/-- **Stateless wrappers commute with classicalisation.** -/
theorem toProbComp_wrap0 (h : QueryImpl (unifSpec + spec) (OracleComp (unifSpec + spec')))
    (hh : ForwardsUnif0 h) (Q : QOC W (unifSpec + spec) α) (ρ : Matrix W W ℂ) :
    toProbComp (wrap0 h Q) ρ = simulateQ h (toProbComp Q ρ) := by
  induction Q using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [wrap0_instr_bind, toProbComp_instr_bind, toProbComp_instr_bind,
        hh.simulateQ_liftL_bind]
      simp only [ih]
    · rw [wrap0_query_bind, toProbComp_liftQ_bind, toProbComp_query_bind, simulateQ_bind,
        simulateQ_spec_query]
      simp only [ih]

theorem rationalBorn_wrap0 (h : QueryImpl spec (OracleComp (unifSpec + spec')))
    (Q : QOC W spec α) (ρ : Matrix W W ℂ) (hQ : RationalBorn Q ρ) :
    RationalBorn (wrap0 h Q) ρ := by
  induction Q using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind q k ih =>
    rcases q with j | q
    · rw [rationalBorn_instr_bind] at hQ
      rw [wrap0_instr_bind, rationalBorn_instr_bind]
      exact ⟨hQ.1, fun i ↦ ih i _ (hQ.2 i)⟩
    · rw [rationalBorn_query_bind] at hQ
      rw [wrap0_query_bind]
      exact rationalBorn_liftQ_bind _ _ _ fun x ↦ ih _ _ (hQ _)

/-- Classicalisation commutes with relabelling the output. -/
theorem toProbComp_map (f : α → β) (Q : QOC W (unifSpec + spec') α) (ρ : Matrix W W ℂ) :
    toProbComp (f <$> Q) ρ = f <$> toProbComp Q ρ := by
  have e : f <$> Q = Q >>= fun a ↦ liftQ (pure (f a) : OracleComp (unifSpec + spec') β) := by
    simp only [liftQ_pure]; exact map_eq_pure_bind f Q
  rw [e, toProbComp_bind_liftQ]
  exact (map_eq_pure_bind f _).symm

theorem rationalBorn_map (f : α → β) (Q : QOC W spec α) (ρ : Matrix W W ℂ)
    (hQ : RationalBorn Q ρ) : RationalBorn (f <$> Q) ρ := by
  have e : f <$> Q = Q >>= fun a ↦ liftQ (pure (f a) : OracleComp spec β) := by
    simp only [liftQ_pure]; exact map_eq_pure_bind f Q
  rw [e]
  exact rationalBorn_bind_liftQ Q _ ρ hQ

/-! ## The `runForger` harness is an instance -/

section harness

variable {Msg Sig : Type}

/-- The signing oracle of a reduction: answer by `sign`, record the message. -/
def harnessSignOracle {κ : Type} {specR : OracleSpec κ} (sign : Msg → OracleComp specR Sig) :
    QueryImpl (Msg →ₒ Sig) (StateT (List Msg) (OracleComp specR)) :=
  fun msg ↦ do
    let sig ← (monadLift (sign msg) : StateT (List Msg) (OracleComp specR) Sig)
    modify (· ++ [msg])
    return sig

/-- The handler of the harness: forward uniform sampling, answer signing queries by `sign`. -/
def harnessImpl (sign : Msg → OracleComp (unifSpec + spec') Sig) :
    QueryImpl (unifSpec + (Msg →ₒ Sig)) (StateT (List Msg) (OracleComp (unifSpec + spec'))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec'))).liftTarget
      (StateT (List Msg) (OracleComp (unifSpec + spec'))) +
    harnessSignOracle sign

/-- Run a classical forger once inside a reduction whose oracle interface is `unifSpec + spec'`
(the shape of `Reduction.runForger`). -/
def runForgerG (A : OracleComp (unifSpec + (Msg →ₒ Sig)) α)
    (sign : Msg → OracleComp (unifSpec + spec') Sig) :
    OracleComp (unifSpec + spec') (α × List Msg) :=
  (simulateQ (harnessImpl sign) A).run []

/-- Run a quantum forger once inside the same harness. -/
def qRunForger (Q : QOC W (unifSpec + (Msg →ₒ Sig)) α)
    (sign : Msg → OracleComp (unifSpec + spec') Sig) :
    QOC W (unifSpec + spec') (α × List Msg) :=
  wrap (harnessImpl sign) Q []

lemma forwardsUnifB_harnessImpl (sign : Msg → OracleComp (unifSpec + spec') Sig) :
    ForwardsUnifB (harnessImpl sign) :=
  forwardsUnifB_ofLift_add _

/-- The harness around the quantum forger classicalises to the harness around its classical
strategy. -/
theorem toProbComp_qRunForger (Q : QOC W (unifSpec + (Msg →ₒ Sig)) α)
    (sign : Msg → OracleComp (unifSpec + spec') Sig) (ρ : Matrix W W ℂ) :
    toProbComp (qRunForger Q sign) ρ = runForgerG (toProbComp Q ρ) sign :=
  toProbComp_wrap _ (forwardsUnifB_harnessImpl sign) Q [] ρ

theorem rationalBorn_qRunForger (Q : QOC W (unifSpec + (Msg →ₒ Sig)) α)
    (sign : Msg → OracleComp (unifSpec + spec') Sig) (ρ : Matrix W W ℂ)
    (h : RationalBorn Q ρ) : RationalBorn (qRunForger Q sign) ρ :=
  rationalBorn_wrap _ Q [] ρ h

end harness

end PQ.Interactive

open PQ.Interactive in
#print axioms toProbComp_wrap
open PQ.Interactive in
#print axioms qWeight_close_wrap
open PQ.Interactive in
#print axioms qWeight_close_qReduction
open PQ.Interactive in
#print axioms toProbComp_qRunForger
open PQ.Interactive in
#print axioms toProbComp_wrap0
