import Ideal.Realize.Port
import Reduction.Open.Fors

/-!
# The FORS open second phase with a compression port (FORS-leaf realisers, part 1)

`Reduction.Open.forsFindOpen optRand main pkSeed ys` is the open second-phase program of
`toDspr (Lazy.bOpenPreS A)` / `toTcr (Lazy.bOpenPreS A)` (game oracle: the opening oracle
`forsG prims`).  Here the forger's own compression queries are threaded through as game queries
of the extended game interface `GP prims = forsG prims + hS St Blk`:

* `liftG` — every query of an open program over `forsG` read as the same query over `GP`;
* `portImplF`, `portRunF`, `forsFindOpenP optRand mainP pkSeed ys` — key generation and answer
  extraction exactly those of `forsFindOpen` (lifted by `liftG`), the forger's run with port
  queries issued as `GP` game queries;
* `portAns g` — answer port queries by the table `g`, forward the rest;
* **fusion** (`forsFindOpenP_fusion`): for every hash evaluation `hI` and secret table `tbl`,
  answering the port by `g` after the table interpretation of `forsFindOpenP … mainP …` is the
  table interpretation of `forsFindOpen` at the forger program with its port answered by `g`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Realize.Fors

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000

/-! ## A generic fusion lemma with two outer interpretations -/

section Fusion2

variable {ι ι₀ ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₀ : OracleSpec ι₀}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {σ α : Type} {m : Type → Type} [Monad m]
  [LawfulMonad m]

/-- Two stateful runs of a program — through `hP` interpreted by `φ₁`, or through `h` after
rewriting each query by `inst`, interpreted by `φ₂` — agree, if they agree at every query. -/
theorem fusion2 (φ₁ : QueryImpl spec₁ m) (φ₂ : QueryImpl spec₂ m)
    (inst : QueryImpl spec (OracleComp spec₀)) (h : QueryImpl spec₀ (StateT σ (OracleComp spec₂)))
    (hP : QueryImpl spec (StateT σ (OracleComp spec₁)))
    (hstep : ∀ t s, simulateQ φ₁ ((hP t).run s) = simulateQ φ₂ ((simulateQ h (inst t)).run s))
    (oa : OracleComp spec α) (s : σ) :
    simulateQ φ₁ ((simulateQ hP oa).run s) =
      simulateQ φ₂ ((simulateQ h (simulateQ inst oa)).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hstep, ih]

end Fusion2

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-! ## The extended game interface -/

/-- Game interface of the port program: the opening oracle and the compression port. -/
abbrev GP (prims : Primitives vp.params) := forsG prims + hS St Blk

/-- Read a query of an open program over `forsG` as the same query over `GP`. -/
def liftIdx : ℕ ⊕ (ℕ ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y)) →
    ℕ ⊕ ((ℕ ⊕ (St × Blk)) ⊕ (SecIdx ⊕ PublicHashQuery prims.PkSeed prims.AdrsKey prims.Y))
  | .inl n => .inl n
  | .inr (.inl i) => .inr (.inl (.inl i))
  | .inr (.inr t) => .inr (.inr t)

/-- Every query of an open program over `forsG`, issued over `GP`. -/
def liftG : QueryImpl (OSpec prims (forsG prims)) (OracleComp (OSpec prims (GP prims)))
  | .inl n => (liftM ((OSpec prims (GP prims)).query (.inl n)) :
      OracleComp (OSpec prims (GP prims)) _)
  | .inr (.inl i) => (liftM ((OSpec prims (GP prims)).query (.inr (.inl (.inl i)))) :
      OracleComp (OSpec prims (GP prims)) _)
  | .inr (.inr t) => (liftM ((OSpec prims (GP prims)).query (.inr (.inr t))) :
      OracleComp (OSpec prims (GP prims)) _)

/-- The handler of the forger's run (as in `runProgLog`), over `GP`. -/
noncomputable def stdF (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pk : PublicKeyCore prims.core) (ys : List prims.Y) :
    QueryImpl (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (OSpec prims (GP prims)))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (OSpec prims (GP prims)))).liftTarget
      (StateT (G2Log prims) (OracleComp (OSpec prims (GP prims)))) +
    logSignOracle optRand pk lazyRandomizerLift
      (fun m R => simulateQ liftG (forsSignOpen pk ys m R))

/-- The handler by which the port program runs a forger with port: sampling and signing as in
`forsFindOpen` (signing lifted by `liftG`), a compression query becomes a `GP` game query. -/
noncomputable def portImplF (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pk : PublicKeyCore prims.core) (ys : List prims.Y) :
    QueryImpl (FSpecP (GeneralScheme.SignatureCore vp prims.core))
      (StateT (G2Log prims) (OracleComp (OSpec prims (GP prims))))
  | .inl n => stdF optRand pk ys (.inl n)
  | .inr (.inl q) => (liftM (Lazy.gameQ prims (GP prims) (.inr q)) :
      StateT (G2Log prims) (OracleComp (OSpec prims (GP prims))) St)
  | .inr (.inr m) => stdF optRand pk ys (.inr m)

/-- The run of a port forger inside the port program. -/
noncomputable def portRunF (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (mainP : PortForgerProg vp prims) (pk : PublicKeyCore prims.core) (ys : List prims.Y) :
    OracleComp (OSpec prims (GP prims))
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  (simulateQ (portImplF optRand pk ys) (mainP pk)).run []

/-- **The open second-phase program of the FORS adversaries for a forger with compression
port**: key generation and answer extraction of `forsFindOpen` (lifted), the run of the port
forger in between. -/
noncomputable def forsFindOpenP (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (mainP : PortForgerProg vp prims) (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    OracleComp (OSpec prims (GP prims)) (ℕ × prims.Y) := do
  let root ← simulateQ liftG (Lazy.openKeygen prims (forsG prims) pkSeed)
  let z ← portRunF optRand mainP ⟨pkSeed, root⟩ ys
  simulateQ liftG (findAnswerO ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2)

/-! ## Answering the port -/

/-- Answer port queries by the table `g`; forward sampling and openings. -/
def portAns (g : CF St Blk) : QueryImpl (unifSpec + GP prims) (OracleComp (unifSpec + forsG prims))
  | .inl n => (liftM ((unifSpec + forsG prims).query (.inl n)) :
      OracleComp (unifSpec + forsG prims) _)
  | .inr (.inl i) => (liftM ((unifSpec + forsG prims).query (.inr i)) :
      OracleComp (unifSpec + forsG prims) _)
  | .inr (.inr q) => pure (g q)

section Fusion

variable (hI : QueryImpl (publicHashSpec prims.core) Id) (tbl : SecIdx → prims.Y) (g : CF St Blk)

/-- The composite interpretation: table, then port answered by `g`. -/
abbrev Φ : QueryImpl (OSpec prims (GP prims)) (OracleComp (unifSpec + forsG prims)) :=
  portAns g ∘ₛ Lazy.tblImpl (gspec := GP prims) hI tbl

theorem Φ_liftG (t : (OSpec prims (forsG prims)).Domain) :
    simulateQ (Φ hI tbl g) (liftG t) = Lazy.tblImpl (gspec := forsG prims) hI tbl t := by
  rcases t with n | i | d | q
  · simp [liftG, Lazy.tblImpl, portAns]
  · simp [liftG, Lazy.tblImpl, portAns]
  · simp [liftG, Lazy.tblImpl]
  · simp [liftG, Lazy.tblImpl]

theorem Φ_simulateQ_liftG {β : Type} (oa : OracleComp (OSpec prims (forsG prims)) β) :
    simulateQ (Φ hI tbl g) (simulateQ liftG oa) =
      simulateQ (Lazy.tblImpl (gspec := forsG prims) hI tbl) oa :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (Φ_liftG hI tbl g) oa

theorem portAns_liftM {β : Type} (ob : ProbComp β) :
    simulateQ (portAns (prims := prims) g) (liftM ob : OracleComp (unifSpec + GP prims) β) =
      (liftM ob : OracleComp (unifSpec + forsG prims) β) := by
  induction ob using OracleComp.inductionOn with
  | pure a => simp
  | query_bind n k ih =>
    simp only [liftM_bind, simulateQ_bind, ih]
    congr 1

theorem two_liftM {β : Type} (ob : ProbComp β) :
    simulateQ (portAns g) (simulateQ (Lazy.tblImpl (gspec := GP prims) hI tbl)
      (liftM ob : OracleComp (OSpec prims (GP prims)) β)) =
      (liftM ob : OracleComp (unifSpec + forsG prims) β) := by
  rw [Lazy.simulateQ_tblImpl_liftM, portAns_liftM]

theorem two_unif (n : ℕ) :
    simulateQ (portAns g) (simulateQ (Lazy.tblImpl (gspec := GP prims) hI tbl)
      (liftM (unifSpec.query n) : OracleComp (OSpec prims (GP prims)) _)) =
      simulateQ (Lazy.tblImpl (gspec := forsG prims) hI tbl)
        (liftM (unifSpec.query n) : OracleComp (OSpec prims (forsG prims)) _) :=
  (two_liftM hI tbl g (liftM (unifSpec.query n))).trans
    (Lazy.simulateQ_tblImpl_liftM hI tbl (liftM (unifSpec.query n))).symm

theorem two_liftG {β : Type} (oa : OracleComp (OSpec prims (forsG prims)) β) :
    simulateQ (portAns g) (simulateQ (Lazy.tblImpl (gspec := GP prims) hI tbl)
      (simulateQ liftG oa)) = simulateQ (Lazy.tblImpl (gspec := forsG prims) hI tbl) oa := by
  rw [← QueryImpl.simulateQ_compose]
  exact Φ_simulateQ_liftG hI tbl g oa

/-- **Fusion for the forger's run.** -/
theorem portRunF_fusion (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (mainP : PortForgerProg vp prims) (pk : PublicKeyCore prims.core) (ys : List prims.Y) :
    simulateQ (Φ hI tbl g) (portRunF optRand mainP pk ys) =
      simulateQ (Lazy.tblImpl (gspec := forsG prims) hI tbl)
        (runProgLog optRand (fun pk => simulateQ (instImpl g) (mainP pk)) pk lazyRandomizerLift
          (forsSignOpen pk ys)) := by
  unfold portRunF runProgLog
  refine fusion2 _ _ (instImpl g) _ _ (fun t s => ?_) _ _
  rcases t with n | q | msg
  · simp [portImplF, stdF, instImpl, two_unif]
  · simp [portImplF, instImpl, Lazy.gameQ, Lazy.tblImpl, portAns]
  · simp [portImplF, stdF, instImpl, logSignOracle, lazyRandomizerLift, portAns_liftM,
      Lazy.simulateQ_tblImpl_liftM, two_liftG]

/-- **Fusion.**  Answering the port by `g` after the table interpretation of the port program is
the table interpretation of `forsFindOpen` at the forger program with its port answered by
`g`. -/
theorem forsFindOpenP_fusion (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (mainP : PortForgerProg vp prims) (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    simulateQ (portAns g) (simulateQ (Lazy.tblImpl (gspec := GP prims) hI tbl)
        (forsFindOpenP optRand mainP pkSeed ys)) =
      simulateQ (Lazy.tblImpl (gspec := forsG prims) hI tbl)
        (forsFindOpen optRand (fun pk => simulateQ (instImpl g) (mainP pk)) pkSeed ys) := by
  rw [← QueryImpl.simulateQ_compose]
  unfold forsFindOpenP forsFindOpen
  simp only [simulateQ_bind]
  rw [Φ_simulateQ_liftG]
  refine bind_congr fun root => ?_
  rw [portRunF_fusion]
  refine bind_congr fun z => ?_
  rw [Φ_simulateQ_liftG]

end Fusion

end Ideal.Realize.Fors

#print axioms Ideal.Realize.Fors.fusion2
#print axioms Ideal.Realize.Fors.portRunF_fusion
#print axioms Ideal.Realize.Fors.forsFindOpenP_fusion
