import Ideal.Core.HPBad

/-!
# The hidden-prefix hop

`Ideal.hiddenPrefix`: the real game (uniform compression table `g`, keyed chain through
`g (IV, sb seed)`) is bounded by the ideal game (phase one reads a private row table instead of
row `cv = g (IV, sb seed)`; the seed and `cv` are drawn after phase one) plus the probability
that a public query of phase one hits the hidden cells.

Proof (files `HPBasic`, `HPTable`, `HPHop`, `HPFlag`, `HPBad`): with eagerly sampled tables, the
public table with the cell `(IV, sb seed)` set to a fresh `cv` and row `cv` replaced by the
private row table is again uniform (`HP.evalDist_gstar`); the two phase-one answer functions
agree except at queries touching the hidden cells (`HP.prT_realGame_le`, identical until bad);
since the eager ideal phase one does not depend on the seed and `cv`, the bad event is bounded
by a union bound over its trace (`HP.prT_badGame_le`), the event that a chaining value equals
`IV` being bounded in the lazy random oracle (`HP.prEvent_trace_hasIV_le`); finally the eager
ideal game is the lazy one (`HP.evalDist_idealGame`).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

variable {St Blk PkSeed σ : Type}

theorem hiddenPrefix [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [Finite Blk] [SampleableType (CF St Blk)]
    (IV : St) (sb : PkSeed → Blk) (hsb : Function.Injective sb) (seedGen : ProbComp PkSeed)
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← seedGen}[s' = s] ≤ γ)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) (q₁ C L : ℕ)
    (hq : IsQueryBoundP prog₁ (fun i => isPub i = true) q₁)
    (hC : IsQueryBoundP prog₁ (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy prog₁ (chainLenLe L)) :
    𝒟[realGame IV sb seedGen prog₁ P₂] {true} ≤
      𝒟[idealGame IV sb seedGen prog₁ P₂] {true} + q₁ * γ +
        (2 * q₁ + C * (1 + 2 * L) + 1 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  let : Fintype Blk := Fintype.ofFinite Blk
  rw [← HP.prT_eq, ← HP.prT_eq, add_assoc,
    HP.prT_congr (HP.evalDist_idealGame IV sb seedGen prog₁ P₂)]
  exact (HP.prT_realGame_le IV sb seedGen prog₁ P₂).trans
    (add_le_add le_rfl (HP.prT_badGame_le IV sb hsb seedGen γ hγ prog₁ q₁ C L hq hC hL))

end Ideal

#print axioms Ideal.hiddenPrefix
