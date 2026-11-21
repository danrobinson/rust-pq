import Integration.SlhDsaComposedEnc
import Reduction.Open.Phase1Tcr

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

namespace Reduction

attribute [local irreducible] arityTargets tcrTargets

elab "qtcr_kernel_rfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← Lean.instantiateMVars (← g.getType)
  let some (_, a, _) := t.eq? | throwError "qtcr_kernel_rfl: not an equality"
  let pf ← Lean.Meta.mkEqRefl a
  g.assign pf
  Lean.Elab.Tactic.replaceMainGoal []

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

abbrev FinFns.withThash {p : Params} {c : Caps} (ω : FinFns p c)
    (T : Bytes p.n → Bytes 22 → BList (Bytes p.n) c.tl → Bytes p.n) : FinFns p c :=
  { ω with thash := T }

abbrev TcrLeaf (n : ℕ) : Type := ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = n}

def TcrModelHyp (n q' : ℕ) : Prop :=
  ∀ (ω₀ : Ω128 c) (st : Open.TcrP1State Link.vp (primsΩ ω₀)) (pk : Bytes Link.vp.params.n),
    ∃ Mo : HybridModel (EncX c) EncY (TcrLeaf n) q',
      ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
          Bytes Link.vp.params.n) (Ev : TcrLeaf n → Prop) [DecidablePred Ev],
        Mo.prob (encΩ (ω₀.withThash T)) Ev =
          qWeight Ev ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F (ω₀.withThash T))).forge
            st pk) F.ρ₀

example (n : ℕ) (ω : Ω128 c) : True := by
  have h1 := (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)).choose
  trivial

example (n : ℕ) (ω : Ω128 c) : True := by
  have h2 := Open.bTcrArM_choose_eq n (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).toClassical
  trivial

example (n : ℕ) (ω : Ω128 c) : True := by
  have h3 : ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)).choose :
      OracleComp (Open.TcrP1Spec (primsΩ ω) n) (Open.TcrP1State Link.vp (primsΩ ω))) =
      Open.tcrPhase1 Link.vp (primsΩ ω) n := by
    have h2 := Open.bTcrArM_choose_eq n (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).toClassical
    unfold qbTcrArM qTcrOfClassical
    dsimp only
    exact h2
  trivial

set_option maxRecDepth 100000 in
example (n : ℕ) (ω : Ω128 c) (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl → Bytes Link.vp.params.n) :
    (Open.tcrPhase1 Link.vp (primsΩ (ω.withThash T)) n : OracleComp (Open.TcrP1Spec (primsΩ ω) n) _) =
      Open.tcrPhase1 Link.vp (primsΩ ω) n := by qtcr_kernel_rfl

example (n : ℕ) (ω : Ω128 c) : (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)).ρ₀ = F.ρ₀ := rfl

end Reduction
