import Ideal.Realize.ForsProg

/-!
# The second phases of the ideal-model FORS adversaries (FORS-leaf realisers, part 2)

Over the reference bundle `P₀ = R₀ dT dH` (core `core₀`, no hash function in it):

* `liftCS` — a program of `CSpec = unifSpec + hS St Blk` read over `unifSpec + GP P₀`;
* `chainImplP tbl` — secrets from `tbl`, hash queries issued as compression chains (`hashC`),
  sampling / openings / port queries forwarded;
* `outerC tg` — the opening oracle of the game (`openOracle tg`, list lookups) run inside the
  adversary; port queries become compression queries;
* `phase2C post optRand mainP tbl tg ys pk` — the ideal-model second phase: the port program
  `forsFindOpenP` through `chainImplP tbl` and `outerC tg`, then the post-processing `post tg`;
* **correctness** (`phase2C_inst`): answering its compression queries by `g` gives
  `forsRun (implTH (thG g) (hmG g)) tbl tg (forsFindOpen optRand (port answered by g) pk ys)`
  followed by `post tg`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Fors

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize
open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity (findOracles openOracle)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 400000

/-- The reference bundle (no hash functions). -/
abbrev P₀ : Primitives Link.vp.params := R₀ dT dH

/-- A compression program read over `unifSpec + GP P₀`. -/
def liftCS : QueryImpl CSpec (OracleComp (unifSpec + GP P₀))
  | .inl n => (liftM ((unifSpec + GP P₀).query (.inl n)) : OracleComp (unifSpec + GP P₀) _)
  | .inr q => (liftM ((unifSpec + GP P₀).query (.inr (.inr q))) : OracleComp (unifSpec + GP P₀) _)

/-- Table interpretation with hash queries issued as compression chains. -/
def chainImplP (tbl : SecIdx → P₀.Y) :
    QueryImpl (OSpec P₀ (GP P₀)) (OracleComp (unifSpec + GP P₀))
  | .inl n => (liftM ((unifSpec + GP P₀).query (.inl n)) : OracleComp (unifSpec + GP P₀) _)
  | .inr (.inl t) => (liftM ((unifSpec + GP P₀).query (.inr t)) : OracleComp (unifSpec + GP P₀) _)
  | .inr (.inr (.inl d)) => pure (tbl d)
  | .inr (.inr (.inr q)) => simulateQ liftCS (hashC q)

/-- The opening oracle inside the adversary; port queries become compression queries. -/
noncomputable def outerC (tg : List (P₀.AdrsKey × P₀.Y)) :
    QueryImpl (unifSpec + GP P₀) (StateT (List ℕ) (OracleComp CSpec))
  | .inl n => (liftM (liftM (CSpec.query (.inl n)) : OracleComp CSpec _) :
      StateT (List ℕ) (OracleComp CSpec) _)
  | .inr (.inl i) => StateT.mk fun s =>
      (liftM ((openOracle tg i).run s) : OracleComp CSpec ((forsG P₀).Range i × List ℕ))
  | .inr (.inr q) => (liftM (cq q) : StateT (List ℕ) (OracleComp CSpec) St)

/-- **The ideal-model second phase**, for a post-processing `post`. -/
noncomputable def phase2C {β : Type}
    (post : List (P₀.AdrsKey × P₀.Y) → (ℕ × P₀.Y) × List ℕ → β)
    (optRand : PublicKeyCore P₀.core → ProbComp P₀.Y) (mainP : PortForgerProg Link.vp P₀)
    (tbl : SecIdx → P₀.Y) (tg : List (P₀.AdrsKey × P₀.Y)) (ys : List P₀.Y) (pk : P₀.PkSeed) :
    OracleComp CSpec β :=
  (simulateQ (outerC tg) (simulateQ (chainImplP tbl) (forsFindOpenP optRand mainP pk ys))).run [] >>=
    fun z => pure (post tg z)

section Correct

variable (g : CF St Blk)

theorem portAns_liftC {β : Type} (X : OracleComp CSpec β) :
    simulateQ (portAns (prims := P₀) g) (simulateQ liftCS X) =
      (liftM (simulateQ (instImpl₀ g) X) : OracleComp (unifSpec + forsG P₀) β) := by
  induction X using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih, liftM_bind]
    rcases t with n | q
    · simp [liftCS, portAns]
      rfl
    · simp [liftCS, portAns]

/-- **The chain interpretation is the table interpretation at `g`** (once the port is answered
by `g`). -/
theorem chainImplP_inst (tbl : SecIdx → P₀.Y) {β : Type} (P : OracleComp (OSpec P₀ (GP P₀)) β) :
    simulateQ (portAns g) (simulateQ (chainImplP tbl) P) =
      simulateQ (portAns g) (simulateQ (Lazy.tblImpl (implTH (thG g) (hmG g)) tbl) P) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with n | t | d | q
  · rfl
  · rfl
  · rfl
  · simp only [QueryImpl.apply_compose, chainImplP, Lazy.tblImpl, portAns_liftC]
    rw [hashC_inst]
    simp

theorem outerC_inst (tg : List (P₀.AdrsKey × P₀.Y)) {β : Type}
    (X : OracleComp (unifSpec + GP P₀) β) (s : List ℕ) :
    simulateQ (instImpl₀ g) ((simulateQ (outerC tg) X).run s) =
      (simulateQ (findOracles tg) (simulateQ (portAns g) X)).run s := by
  rw [← QueryImpl.simulateQ_compose]
  refine simulateQ_StateT_compose _ _ _ (fun t s => ?_) X s
  rcases t with n | i | q
  · simp [outerC, portAns, findOracles, instImpl₀_liftM]
  · simp [outerC, portAns, findOracles, instImpl₀_liftM]
  · simp [outerC, portAns, cq]

/-- **Correctness of the ideal-model second phase.** -/
theorem phase2C_inst {β : Type} (post : List (P₀.AdrsKey × P₀.Y) → (ℕ × P₀.Y) × List ℕ → β)
    (optRand : PublicKeyCore P₀.core → ProbComp P₀.Y) (mainP : PortForgerProg Link.vp P₀)
    (tbl : SecIdx → P₀.Y) (tg : List (P₀.AdrsKey × P₀.Y)) (ys : List P₀.Y) (pk : P₀.PkSeed) :
    simulateQ (instImpl₀ g) (phase2C post optRand mainP tbl tg ys pk) =
      forsRun (implTH (thG g) (hmG g)) tbl tg
          (forsFindOpen optRand (fun pk => simulateQ (instImpl g) (mainP pk)) pk ys) >>=
        fun z => pure (post tg z) := by
  unfold phase2C forsRun
  rw [simulateQ_bind, outerC_inst, chainImplP_inst, forsFindOpenP_fusion]
  simp

end Correct

end Ideal.Realize.Fors

#print axioms Ideal.Realize.Fors.chainImplP_inst
#print axioms Ideal.Realize.Fors.outerC_inst
#print axioms Ideal.Realize.Fors.phase2C_inst
