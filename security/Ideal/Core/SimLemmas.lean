import Ideal.Core.Defs

/-!
# General simulation lemmas for the game bridges

* `simulateQ_run_simulateQ_eq_of_step`: fusion of an instantiation followed by a stateful game
  handler with a stateful "monadic game" handler followed by an answering handler, from a
  per-query equation.
* `IsQueryBoundP.simulateQ_run_of_step_or`: additive transfer of two predicate budgets through a
  stateful handler.
* Evaluation lemmas for `instImpl₀`, `ans₁` on single queries and Merkle–Damgård folds.
-/

open OracleComp OracleSpec

namespace Ideal

section Fusion

variable {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {σ α : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Fusion.  `inst` rewrites a `spec`-program into a `spec₁`-program which is then run by the
stateful handler `O` into `m`; alternatively the stateful handler `G` runs the `spec`-program into
`OracleComp spec₂`, whose queries are then answered by `f` in `m`.  If the two agree on every
single query from every state, they agree on every program from every state. -/
theorem simulateQ_run_simulateQ_eq_of_step
    (inst : QueryImpl spec (OracleComp spec₁)) (O : QueryImpl spec₁ (StateT σ m))
    (G : QueryImpl spec (StateT σ (OracleComp spec₂))) (f : QueryImpl spec₂ m)
    (hstep : ∀ t s, (simulateQ O (inst t)).run s = simulateQ f ((G t).run s))
    (oa : OracleComp spec α) (s : σ) :
    (simulateQ O (simulateQ inst oa)).run s = simulateQ f ((simulateQ G oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep, ih]

/-- Stateless-outer variant: a stateful handler `G` into `OracleComp spec₂` followed by an
answering handler `f` is the stateful handler `fun t => StateT.mk fun s => simulateQ f ((G t).run s)`. -/
theorem simulateQ_run_eq_of_step
    (O : QueryImpl spec (StateT σ m))
    (G : QueryImpl spec (StateT σ (OracleComp spec₂))) (f : QueryImpl spec₂ m)
    (hstep : ∀ t s, (O t).run s = simulateQ f ((G t).run s))
    (oa : OracleComp spec α) (s : σ) :
    (simulateQ O oa).run s = simulateQ f ((simulateQ G oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep, ih]

end Fusion

section Bounds

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {σ α : Type}

/-- Additive budget transfer through a stateful handler: if `oa` makes at most `a` queries
satisfying `p₁` and at most `b` satisfying `p₂`, every handler step at a `p₁`- or `p₂`-query
issues at most one `q`-query from any state and every other step issues none, then the run issues
at most `a + b` `q`-queries. -/
theorem IsQueryBoundP.simulateQ_run_of_step_or
    {p₁ p₂ : ι → Prop} [DecidablePred p₁] [DecidablePred p₂] {q : ι' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OracleComp spec'))} {oa : OracleComp spec α} {a b : ℕ}
    (h₁ : IsQueryBoundP oa p₁ a) (h₂ : IsQueryBoundP oa p₂ b)
    (hstep_p : ∀ t, p₁ t ∨ p₂ t → ∀ s, IsQueryBoundP ((impl t).run s) q 1)
    (hstep_np : ∀ t, ¬ (p₁ t ∨ p₂ t) → ∀ s, IsQueryBoundP ((impl t).run s) q 0) (s : σ) :
    IsQueryBoundP ((simulateQ impl oa).run s) q (a + b) :=
  IsQueryBoundP.simulateQ_run_of_step (h₁.or h₂) hstep_p hstep_np s

end Bounds

section Eval

variable {St Blk : Type}

@[simp] theorem instImpl₀_inl (g : CF St Blk) (n : ℕ) :
    instImpl₀ g (.inl n) = unifSpec.query n := rfl

@[simp] theorem instImpl₀_inr (g : CF St Blk) (q : St × Blk) :
    instImpl₀ g (.inr q) = pure (g q) := rfl

@[simp] theorem ans₁_inl (pub : CF St Blk) (chain : Blk × List Blk → St) (n : ℕ) :
    ans₁ pub chain (.inl n) = unifSpec.query n := rfl

@[simp] theorem ans₁_pub (pub : CF St Blk) (chain : Blk × List Blk → St) (q : St × Blk) :
    ans₁ pub chain (.inr (.inl q)) = pure (pub q) := rfl

@[simp] theorem ans₁_chain (pub : CF St Blk) (chain : Blk × List Blk → St) (q : Blk × List Blk) :
    ans₁ pub chain (.inr (.inr q)) = pure (chain q) := rfl

/-- A Merkle–Damgård fold issued as public compression queries evaluates to `mdFold`. -/
theorem simulateQ_instImpl₀_foldlM (g : CF St Blk) (bs : List Blk) (c : St) :
    simulateQ (instImpl₀ g)
        (bs.foldlM (fun c b => (unifSpec + hS St Blk).query (.inr (c, b))) c) =
      pure (mdFold g c bs) := by
  induction bs generalizing c with
  | nil => simp [mdFold]
  | cons b bs ih =>
    simp only [List.foldlM_cons, simulateQ_bind, simulateQ_spec_query, instImpl₀_inr, pure_bind,
      ih, mdFold, List.foldl_cons]

/-- The keyed chain issued as public compression queries evaluates to `keyedChain`. -/
theorem simulateQ_instImpl₀_keyedChain {PkSeed : Type} (g : CF St Blk) (IV : St)
    (sb : PkSeed → Blk) (pk : PkSeed) (bs : Blk × List Blk) :
    simulateQ (instImpl₀ g) (do
        let cv ← (unifSpec + hS St Blk).query (.inr (IV, sb pk))
        let c ← (unifSpec + hS St Blk).query (.inr (cv, bs.1))
        bs.2.foldlM (fun c b => (unifSpec + hS St Blk).query (.inr (c, b))) c) =
      pure (keyedChain IV sb g pk bs) := by
  simp only [simulateQ_bind, simulateQ_spec_query, instImpl₀_inr, pure_bind,
    simulateQ_instImpl₀_foldlM, keyedChain]

end Eval

end Ideal

#print axioms Ideal.simulateQ_run_simulateQ_eq_of_step
#print axioms Ideal.simulateQ_run_eq_of_step
#print axioms Ideal.IsQueryBoundP.simulateQ_run_of_step_or
#print axioms Ideal.simulateQ_instImpl₀_keyedChain
