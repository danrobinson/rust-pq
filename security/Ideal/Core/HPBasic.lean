import Ideal.Core.Defs
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityBounds

/-!
# Generic lemmas for the hidden-prefix hop

* `prT`: the probability that a Boolean experiment returns `true`, with a small calculus.
* `ansImpl a`: answer every oracle query from the answer function `a`, forward uniform sampling.
* `stImpl a u`: the same, threading a state updated by `u` at every oracle query;
  `trImpl a = stImpl a (fun t l => l ++ [t])` records the trace of oracle queries.
* `prT_simulateQ_le_add_trace`: identical-until-bad for answer functions.
* `trace_countP_le`, `trace_forall`: pathwise query bounds for the trace.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal.HP

/-! ## `prT` -/

/-- Probability that a Boolean experiment returns `true`. -/
noncomputable def prT (g : ProbComp Bool) : ℝ≥0∞ := Pr{let b ← g}[b = true]

theorem prT_eq (g : ProbComp Bool) : prT g = 𝒟[g] {true} := by
  unfold prT
  rw [prEvent_eq_evalDist_of_discrete]
  congr 1

theorem prT_congr {g₁ g₂ : ProbComp Bool} (h : 𝒟[g₁] = 𝒟[g₂]) : prT g₁ = prT g₂ := by
  rw [prT_eq, prT_eq, h]

theorem prT_le_one (g : ProbComp Bool) : prT g ≤ 1 := prEvent_le_one _

theorem prT_pure (b : Bool) : prT (pure b) = if b then 1 else 0 := by
  unfold prT
  rw [prEvent_pure]

variable {α β : Type}

theorem prT_bind_mono (mx : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ x ∈ support mx, prT (f x) ≤ prT (g x)) : prT (mx >>= f) ≤ prT (mx >>= g) :=
  prEvent_bind_mono_of_forall_le_of_support mx f g _ _ h

theorem prT_bind_congr (mx : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ x ∈ support mx, prT (f x) = prT (g x)) : prT (mx >>= f) = prT (mx >>= g) :=
  le_antisymm (prT_bind_mono mx f g fun x hx => (h x hx).le)
    (prT_bind_mono mx g f fun x hx => (h x hx).ge)

theorem prT_bind_le_add (mx : ProbComp α) (f g k : α → ProbComp Bool)
    (h : ∀ x, prT (f x) ≤ prT (g x) + prT (k x)) :
    prT (mx >>= f) ≤ prT (mx >>= g) + prT (mx >>= k) :=
  prEvent_bind_le_add_of_forall_le mx f g k _ _ _ h

theorem prT_bind_le_of_forall_le (mx : ProbComp α) (f : α → ProbComp Bool) {ε : ℝ≥0∞}
    (h : ∀ x ∈ support mx, prT (f x) ≤ ε) : prT (mx >>= f) ≤ ε :=
  prEvent_bind_le_of_forall_le_of_support mx f _ h

/-- A bound `c` outside an event `p` of the prefix gives `Pr[p] + c`. -/
theorem prT_bind_le_prEvent_add (mx : ProbComp α) (f : α → ProbComp Bool) (p : α → Prop)
    {ε : ℝ≥0∞} (h : ∀ x ∈ support mx, ¬ p x → prT (f x) ≤ ε) :
    prT (mx >>= f) ≤ Pr{let x ← mx}[p x] + ε :=
  prEvent_bind_le_prEvent_add_of_support mx f p _ h

theorem prT_bind_pure (mx : ProbComp α) (p : α → Bool) :
    prT (mx >>= fun x => pure (p x)) = Pr{let x ← mx}[p x = true] := by
  unfold prT
  simp only [bind_pure_comp, Functor.map_map]

theorem prT_eq_one_of_support (g : ProbComp Bool) (h : ∀ x ∈ support g, x = true) :
    prT g = 1 :=
  (OracleComp.prEvent_eq_one_iff g _).mpr h

theorem prT_swap (mx : ProbComp α) (my : ProbComp β) (f : α → β → ProbComp Bool) :
    prT (mx >>= fun a => my >>= fun b => f a b) = prT (my >>= fun b => mx >>= fun a => f a b) := by
  unfold prT
  simp only [map_bind]
  exact OracleComp.prEvent_bind_bind_swap mx my fun a b => (fun b => b = true) <$> f a b

theorem prT_bind_const (mx : ProbComp α) (g : ProbComp Bool) : prT (mx >>= fun _ => g) = prT g :=
  prT_congr (OracleComp.evalDist_bind_const mx g)

theorem prT_map_or_le (k : ProbComp Bool) (c : Bool) :
    prT ((fun b => b || c) <$> k) ≤ prT k + (if c then 1 else 0) := by
  cases c
  · simp
  · simp only [Bool.or_true, ite_true]
    exact (prT_le_one _).trans le_add_self

/-! ## Answer-function handlers -/

variable {ι : Type} {spec : OracleSpec ι} {τ : Type}

/-- Answer oracle queries from `a`, forward uniform sampling. -/
abbrev ansImpl (a : (t : ι) → spec.Range t) : QueryImpl (unifSpec + spec) ProbComp :=
  unifFwdAnswerImpl (QueryImpl.ofFn a)

theorem simulateQ_ansImpl_inl_bind (a : (t : ι) → spec.Range t) (n : ℕ)
    (k : (unifSpec + spec).Range (.inl n) → OracleComp (unifSpec + spec) α) :
    simulateQ (ansImpl a) (liftM ((unifSpec + spec).query (.inl n)) >>= k) =
      (unifSpec.query n : ProbComp _) >>= fun u => simulateQ (ansImpl a) (k u) := by
  simp [unifFwdAnswerImpl]

theorem simulateQ_ansImpl_inr_bind (a : (t : ι) → spec.Range t) (t : ι)
    (k : (unifSpec + spec).Range (.inr t) → OracleComp (unifSpec + spec) α) :
    simulateQ (ansImpl a) (liftM ((unifSpec + spec).query (.inr t)) >>= k) =
      simulateQ (ansImpl a) (k (a t)) := by
  rw [simulateQ_bind, simulateQ_spec_query]
  exact pure_bind _ _

/-- Answer oracle queries from `a` and update the state by `u`; forward uniform sampling. -/
def stImpl (a : (t : ι) → spec.Range t) (u : ι → τ → τ) :
    QueryImpl (unifSpec + spec) (StateT τ ProbComp) := fun
  | .inl n => StateT.mk fun s => (fun x => (x, s)) <$> (unifSpec.query n : ProbComp _)
  | .inr t => StateT.mk fun s => pure (a t, u t s)

theorem run_stImpl_inl_bind (a : (t : ι) → spec.Range t) (u : ι → τ → τ) (n : ℕ)
    (k : (unifSpec + spec).Range (.inl n) → OracleComp (unifSpec + spec) α) (s : τ) :
    (simulateQ (stImpl a u) (liftM ((unifSpec + spec).query (.inl n)) >>= k)).run s =
      (unifSpec.query n : ProbComp _) >>= fun x => (simulateQ (stImpl a u) (k x)).run s := by
  rw [run_simulateQ_query_bind]
  simp [stImpl]

theorem run_stImpl_inr_bind (a : (t : ι) → spec.Range t) (u : ι → τ → τ) (t : ι)
    (k : (unifSpec + spec).Range (.inr t) → OracleComp (unifSpec + spec) α) (s : τ) :
    (simulateQ (stImpl a u) (liftM ((unifSpec + spec).query (.inr t)) >>= k)).run s =
      (simulateQ (stImpl a u) (k (a t))).run (u t s) := by
  rw [run_simulateQ_query_bind]
  simp [stImpl]

/-- Forgetting the state gives the plain answer-function run. -/
theorem fst_map_run_stImpl (a : (t : ι) → spec.Range t) (u : ι → τ → τ)
    (oa : OracleComp (unifSpec + spec) α) (s : τ) :
    Prod.fst <$> (simulateQ (stImpl a u) oa).run s = simulateQ (ansImpl a) oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    rcases t with n | t
    · rw [run_stImpl_inl_bind, simulateQ_ansImpl_inl_bind, map_bind]
      exact bind_congr fun x => ih x s
    · rw [run_stImpl_inr_bind, simulateQ_ansImpl_inr_bind]
      exact ih _ _

/-- A state predicate preserved by every update holds at the end of the run. -/
theorem run_stImpl_inv (a : (t : ι) → spec.Range t) (u : ι → τ → τ) (P : τ → Prop)
    (hP : ∀ t s, P s → P (u t s)) (oa : OracleComp (unifSpec + spec) α) (s : τ) (hs : P s) :
    ∀ z ∈ support ((simulateQ (stImpl a u) oa).run s), P z.2 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs
  | query_bind t k ih =>
    intro z hz
    rcases t with n | t
    · rw [run_stImpl_inl_bind, mem_support_bind_iff] at hz
      obtain ⟨x, -, hz⟩ := hz
      exact ih x s hs z hz
    · rw [run_stImpl_inr_bind] at hz
      exact ih _ _ (hP t s hs) z hz

/-- The trace handler: record the oracle queries in order. -/
abbrev trImpl (a : (t : ι) → spec.Range t) :
    QueryImpl (unifSpec + spec) (StateT (List ι) ProbComp) :=
  stImpl a fun t l => l ++ [t]

/-- Every state run is a fold of the trace. -/
theorem run_stImpl_eq_trace (a : (t : ι) → spec.Range t) (u : ι → τ → τ)
    (oa : OracleComp (unifSpec + spec) α) (s₀ : τ) (l : List ι) :
    (simulateQ (stImpl a u) oa).run (l.foldl (fun s t => u t s) s₀) =
      (fun z => (z.1, z.2.foldl (fun s t => u t s) s₀)) <$> (simulateQ (trImpl a) oa).run l := by
  induction oa using OracleComp.inductionOn generalizing l with
  | pure x => simp
  | query_bind t k ih =>
    rcases t with n | t
    · rw [run_stImpl_inl_bind, run_stImpl_inl_bind, map_bind]
      exact bind_congr fun x => ih x l
    · rw [run_stImpl_inr_bind, run_stImpl_inr_bind, ← ih]
      simp

/-- **Identical until bad** for answer functions: if `a₁` and `a₂` agree at every query that is
not `bad`, running with `a₁` wins at most as often as running with `a₂`, plus the probability
that the `a₂`-run issues a bad query. -/
theorem prT_simulateQ_le_add_trace (a₁ a₂ : (t : ι) → spec.Range t) (bad : ι → Bool)
    (hag : ∀ t, bad t = false → a₁ t = a₂ t) (oa : OracleComp (unifSpec + spec) α)
    (k : α → ProbComp Bool) (l : List ι) :
    prT (simulateQ (ansImpl a₁) oa >>= k) ≤
      prT (simulateQ (ansImpl a₂) oa >>= k) +
        prT ((simulateQ (trImpl a₂) oa).run l >>= fun z => pure (z.2.any bad)) := by
  induction oa using OracleComp.inductionOn generalizing l with
  | pure x =>
    simp only [simulateQ_pure, pure_bind]
    exact le_self_add
  | query_bind t f ih =>
    rcases t with n | t
    · rw [simulateQ_ansImpl_inl_bind, simulateQ_ansImpl_inl_bind, run_stImpl_inl_bind]
      simp only [bind_assoc]
      exact prT_bind_le_add _ _ _ _ fun x => ih x l
    · rw [simulateQ_ansImpl_inr_bind, simulateQ_ansImpl_inr_bind, run_stImpl_inr_bind]
      cases hb : bad t
      · rw [hag t hb]
        exact ih _ _
      · have h1 : prT ((simulateQ (trImpl a₂) (f (a₂ t))).run (l ++ [t]) >>=
            fun z => pure (z.2.any bad)) = 1 := by
          refine prT_eq_one_of_support _ fun b hbm => ?_
          rw [mem_support_bind_iff] at hbm
          obtain ⟨z, hz, hbm⟩ := hbm
          simp only [support_pure, Set.mem_singleton_iff] at hbm
          have := run_stImpl_inv a₂ (fun t l => l ++ [t]) (fun l => l.any bad = true)
            (fun t s hs => by simp [hs]) (f (a₂ t)) (l ++ [t]) (by simp [hb]) z hz
          rw [hbm, this]
        rw [h1]
        exact (prT_le_one _).trans le_add_self

/-! ## Pathwise bounds on the trace -/

theorem trace_countP_le (a : (t : ι) → spec.Range t) (p : ℕ ⊕ ι → Prop) [DecidablePred p]
    (oa : OracleComp (unifSpec + spec) α) (n : ℕ) (hn : IsQueryBoundP oa p n) (l : List ι) :
    ∀ z ∈ support ((simulateQ (trImpl a) oa).run l),
      z.2.countP (fun t => decide (p (.inr t))) ≤ l.countP (fun t => decide (p (.inr t))) + n := by
  induction oa using OracleComp.inductionOn generalizing l n with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Nat.le_add_right _ _
  | query_bind t k ih =>
    intro z hz
    rw [isQueryBoundP_query_bind_iff] at hn
    rcases t with m | t
    · rw [run_stImpl_inl_bind, mem_support_bind_iff] at hz
      obtain ⟨x, -, hz⟩ := hz
      refine (ih x _ (hn.2 x) l z hz).trans ?_
      split_ifs <;> omega
    · rw [run_stImpl_inr_bind] at hz
      have := ih _ _ (hn.2 _) _ z hz
      rw [List.countP_append] at this
      by_cases hp : p (.inr t)
      · have h0 : 0 < n := hn.1.resolve_left (not_not.mpr hp)
        simp only [hp, ite_true, List.countP_singleton, decide_true] at this
        omega
      · simp only [hp, ite_false, List.countP_singleton, decide_false] at this
        simpa using this

theorem trace_forall (a : (t : ι) → spec.Range t) (P : ℕ ⊕ ι → Prop)
    (oa : OracleComp (unifSpec + spec) α) (hP : AllQueriesSatisfy oa P) (l : List ι)
    (hl : ∀ t ∈ l, P (.inr t)) :
    ∀ z ∈ support ((simulateQ (trImpl a) oa).run l), ∀ t ∈ z.2, P (.inr t) := by
  induction oa using OracleComp.inductionOn generalizing l with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hl
  | query_bind t k ih =>
    intro z hz
    rw [allQueriesSatisfy_query_bind_iff] at hP
    rcases t with m | t
    · rw [run_stImpl_inl_bind, mem_support_bind_iff] at hz
      obtain ⟨x, -, hz⟩ := hz
      exact ih x (hP.2 x) l hl z hz
    · rw [run_stImpl_inr_bind] at hz
      refine ih _ (hP.2 _) _ (fun t' ht' => ?_) z hz
      rcases List.mem_append.mp ht' with h | h
      · exact hl t' h
      · rw [List.mem_singleton.mp h]
        exact hP.1

end Ideal.HP

#print axioms Ideal.HP.prT_simulateQ_le_add_trace
#print axioms Ideal.HP.trace_countP_le
