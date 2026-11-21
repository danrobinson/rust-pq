import Reduction.Gen.Sem
import Reduction.Linear

/-!
# Wrapper game: PRF distinguishing with adversaries over a general sampling spec

VCVio's `PRFScheme.prfRealExperiment` / `prfIdealExperiment` with the distinguisher over
`(ds + unifSpec) + (D →ₒ R)` instead of `unifSpec + (D →ₒ R)`.

* `PRFAdversaryG`, `prfRealExperimentG`, `prfIdealExperimentG`, `prfRealPrG`, `prfIdealPrG`,
  `prfAdvantageG` (`= |real − ideal|`, as VCVio's `prfAdvantage`);
* `prfRealPrG_embed`, `prfIdealPrG_embed`, `prfAdvantageG_embed`: on classical distinguishers
  (`embed ds B`) the wrapper game is VCVio's.
-/

open OracleComp OracleSpec ENNReal

namespace Reduction.Gen

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {K D R : Type}

/-- A PRF distinguisher that may sample from `ds` as well as uniformly. -/
abbrev PRFAdversaryG (D R : Type) : Type := OracleComp ((ds + unifSpec) + (D →ₒ R)) Bool

/-- A stateless classical handler as a stateful one with trivial state. -/
def stOf {ιx : Type} {X : OracleSpec ιx} (h : QueryImpl (unifSpec + X) ProbComp) :
    QueryImpl (unifSpec + X) (StateT Unit ProbComp) :=
  fun t s ↦ (fun u ↦ (u, s)) <$> h t

omit [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)] in
lemma run_simulateQ_stOf {ιx : Type} {X : OracleSpec ιx} {α : Type}
    (h : QueryImpl (unifSpec + X) ProbComp) (t : OracleComp (unifSpec + X) α) (s : Unit) :
    (simulateQ (stOf h) t).run s = (fun a ↦ (a, s)) <$> simulateQ h t := by
  induction t using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
      simulateQ_spec_query, map_bind]
    change ((fun u ↦ (u, s)) <$> h q) >>= _ = _
    rw [bind_map_left]
    exact bind_congr fun u ↦ ih u

/-- Real PRF experiment for a distinguisher over the general sampling interface. -/
def prfRealExperimentG (prf : PRFScheme K D R) (B : PRFAdversaryG ds D R) :
    OracleComp (gSpec ds) Bool :=
  liftR ds prf.keygen >>= fun k ↦
    Prod.fst <$> runG ds (stOf (prf.prfRealQueryImpl k)) B ()

/-- Ideal PRF experiment (lazy random function) for a distinguisher over the general sampling
interface. -/
def prfIdealExperimentG [DecidableEq D] [SampleableType R] (B : PRFAdversaryG ds D R) :
    OracleComp (gSpec ds) Bool :=
  Prod.fst <$> runG ds (PRFScheme.prfIdealQueryImpl (D := D) (R := R)) B ∅

/-- `Pr[B outputs 1]` in the real world. -/
noncomputable def prfRealPrG (prf : PRFScheme K D R) (B : PRFAdversaryG ds D R) : ℝ≥0∞ :=
  prG ds (prfRealExperimentG ds prf B)

/-- `Pr[B outputs 1]` in the ideal world. -/
noncomputable def prfIdealPrG [DecidableEq D] [SampleableType R] (B : PRFAdversaryG ds D R) :
    ℝ≥0∞ :=
  prG ds (prfIdealExperimentG ds B)

/-- The PRF advantage `|real − ideal|` of a distinguisher over the general interface. -/
noncomputable def prfAdvantageG [DecidableEq D] [SampleableType R] (prf : PRFScheme K D R)
    (B : PRFAdversaryG ds D R) : ℝ≥0∞ :=
  ENNReal.absDiff (prfRealPrG ds prf B) (prfIdealPrG ds B)

/-- **Coincidence, real world (program level).** -/
theorem prfRealExperimentG_embed (prf : PRFScheme K D R) (B : PRFScheme.PRFAdversary D R) :
    prfRealExperimentG ds prf (embed ds B) = liftR ds (prf.prfRealExperiment B) := by
  simp only [prfRealExperimentG, PRFScheme.prfRealExperiment, runG_embed, run_simulateQ_stOf,
    liftR_bind, liftR_map, Functor.map_map]
  refine bind_congr fun k ↦ ?_
  simp

/-- **Coincidence, ideal world (program level).** -/
theorem prfIdealExperimentG_embed [DecidableEq D] [SampleableType R]
    (B : PRFScheme.PRFAdversary D R) :
    prfIdealExperimentG ds (embed ds B) = liftR ds (PRFScheme.prfIdealExperiment B) := by
  simp only [prfIdealExperimentG, PRFScheme.prfIdealExperiment, runG_embed]
  exact (liftR_map ds _ Prod.fst).symm

theorem prfRealPrG_embed (prf : PRFScheme K D R) (B : PRFScheme.PRFAdversary D R) :
    prfRealPrG ds prf (embed ds B) = 𝒟[prf.prfRealExperiment B] {true} := by
  rw [prfRealPrG, prfRealExperimentG_embed, prG_liftR]; rfl

theorem prfIdealPrG_embed [DecidableEq D] [SampleableType R] (B : PRFScheme.PRFAdversary D R) :
    prfIdealPrG ds (embed ds B) = 𝒟[PRFScheme.prfIdealExperiment B] {true} := by
  rw [prfIdealPrG, prfIdealExperimentG_embed, prG_liftR]; rfl

/-- **Coincidence.** On classical distinguishers the wrapper advantage is VCVio's. -/
theorem prfAdvantageG_embed [DecidableEq D] [SampleableType R] (prf : PRFScheme K D R)
    (B : PRFScheme.PRFAdversary D R) :
    prfAdvantageG ds prf (embed ds B) = prf.prfAdvantage B := by
  rw [prfAdvantageG, prfRealPrG_embed, prfIdealPrG_embed]; rfl

theorem prfRealPrG_le_one (prf : PRFScheme K D R) (B : PRFAdversaryG ds D R) :
    prfRealPrG ds prf B ≤ 1 := prG_le_one ds _

theorem prfIdealPrG_le_one [DecidableEq D] [SampleableType R] (B : PRFAdversaryG ds D R) :
    prfIdealPrG ds B ≤ 1 := prG_le_one ds _

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms prfAdvantageG_embed
end Axioms
