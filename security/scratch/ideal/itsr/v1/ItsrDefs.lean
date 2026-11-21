import Ideal.Games.ItsrTape
import Ideal.Core.SimLemmas
import Ideal.Core.HPTable
import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR

/-!
# ITSR in the ideal-compression model: definitions and the monadic game

The keyed hash is two nested Merkle–Damgård hashes over the compression function `g`:

`H_g(k, x) = od (mdFold g IV (ob (k, x) (mdFold g IV (ib (k, x)))))`

(`ib` the blocks of the inner hash input, `ob (k, x) s` the blocks of the outer hash input, which
contains the inner digest `s`; `od` the output truncation).

* `probI`: VCVio's `ITSRProblem` for `H_g` with uniform keys and index map `idx`.
* `ItsrAdvI`: ideal-model adversaries (uniform sampling, compression queries, target queries);
  `ItsrAdvI.inst A prob g`: the adversary at the table `g`.
* `gameProg`: the whole experiment (adversary, target oracle, and the final check computing the
  hashes of the targets and of the candidate) as one program over the compression oracle;
  `simulateQ_gameProg`: at every table `g` it is VCVio's `ITSRExperiment`.
-/

open OracleComp OracleSpec ENNReal KeyedHash

namespace Ideal.Itsr

open Ideal.HP

variable {St Blk K X Y Index : Type}

/-- The keyed hash `H_g(k, x) = od (MD_g (ob (k, x) (MD_g (ib (k, x)))))`. -/
def hashG (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (g : CF St Blk) (kx : K × X) : Y :=
  od (mdFold g IV (ob kx (mdFold g IV (ib kx))))

/-- The ITSR problem of `H_g` with uniform keys and index map `idx`. -/
def probI [SampleableType K] (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk)
    (od : St → Y) (idx : Y → List Index) (g : CF St Blk) : ITSRProblem K X Y Index where
  khf := { keygen := $ᵗ K, hash := fun k x => hashG IV ib ob od g (k, x) }
  indices := idx

/-- An ideal-model ITSR adversary: uniform sampling, compression queries, target queries. -/
abbrev ItsrAdvI (St Blk K X : Type) :=
  OracleComp (unifSpec + (hS St Blk + ITSRTargetSpec X K)) (K × X)

/-- The adversary at a fixed compression table: compression queries are answered by `g`. -/
def ItsrAdvI.inst (A : ItsrAdvI St Blk K X) (prob : ITSRProblem K X Y Index) (g : CF St Blk) :
    ITSRAdversary prob where
  main := simulateQ (instImpl g) A

/-! ## The experiment as one program over the compression oracle -/

/-- Merkle–Damgård iteration issued as compression queries. -/
def mdM (c : St) (bs : List Blk) : OracleComp (unifSpec + hS St Blk) St :=
  bs.foldlM (fun c b => (unifSpec + hS St Blk).query (.inr (c, b))) c

/-- The keyed hash issued as compression queries. -/
def hashM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (kx : K × X) : OracleComp (unifSpec + hS St Blk) Y := do
  let s ← mdM IV (ib kx)
  let o ← mdM IV (ob kx s)
  pure (od o)

/-- The keyed hashes of a list of inputs, issued as compression queries. -/
def hashAllM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y) :
    List (K × X) → OracleComp (unifSpec + hS St Blk) (List Y)
  | [] => pure []
  | kx :: l => do
      let d ← hashM IV ib ob od kx
      let ds ← hashAllM IV ib ob od l
      pure (d :: ds)

/-- The target oracle over the compression oracle: a target query draws a uniform key and
records the pair. -/
def tgtImpl [SampleableType K] :
    QueryImpl (unifSpec + (hS St Blk + ITSRTargetSpec X K))
      (StateT (List (K × X)) (OracleComp (unifSpec + hS St Blk))) := fun
  | .inl n => StateT.mk fun s =>
      (fun u => (u, s)) <$> (liftM ((unifSpec + hS St Blk).query (.inl n)) :
        OracleComp (unifSpec + hS St Blk) _)
  | .inr (.inl q) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (liftM ((unifSpec + hS St Blk).query (.inr q)) :
        OracleComp (unifSpec + hS St Blk) _)
  | .inr (.inr x) => StateT.mk fun s =>
      (fun k : K => (k, s ++ [(k, x)])) <$> (liftM ($ᵗ K : ProbComp K) :
        OracleComp (unifSpec + hS St Blk) K)

/-- The whole ITSR experiment as one program over the compression oracle: run the adversary
against the target oracle, then compute the hashes of the targets and of the candidate and
evaluate the winning condition. -/
def gameProg [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (A : ItsrAdvI St Blk K X) : OracleComp (unifSpec + hS St Blk) Bool := do
  let z ← (simulateQ tgtImpl A).run []
  let ds ← hashAllM IV ib ob od z.2
  let d ← hashM IV ib ob od z.1
  pure (decide (z.1 ∉ z.2 ∧ ∀ i ∈ idx d, i ∈ ds.flatMap idx))

/-! ## Evaluation at a table -/

theorem simulateQ_mdM (g : CF St Blk) (c : St) (bs : List Blk) :
    simulateQ (instImpl₀ g) (mdM c bs) = pure (mdFold g c bs) :=
  simulateQ_instImpl₀_foldlM g bs c

theorem simulateQ_hashM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk)
    (od : St → Y) (g : CF St Blk) (kx : K × X) :
    simulateQ (instImpl₀ g) (hashM IV ib ob od kx) = pure (hashG IV ib ob od g kx) := by
  simp only [hashM, simulateQ_bind, simulateQ_mdM, pure_bind, simulateQ_pure, hashG]

theorem simulateQ_hashAllM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk)
    (od : St → Y) (g : CF St Blk) (l : List (K × X)) :
    simulateQ (instImpl₀ g) (hashAllM IV ib ob od l) = pure (l.map (hashG IV ib ob od g)) := by
  induction l with
  | nil => simp [hashAllM]
  | cons kx l ih =>
    simp only [hashAllM, simulateQ_bind, simulateQ_hashM, pure_bind, ih, simulateQ_pure,
      List.map_cons]

/-- The adversary phase: instantiating at `g` and running VCVio's target oracle is the monadic
target oracle evaluated at `g`. -/
theorem run_tgt_eq [SampleableType K] (IV : St) (ib : K × X → List Blk)
    (ob : K × X → St → List Blk) (od : St → Y) (idx : Y → List Index) (g : CF St Blk)
    (A : ItsrAdvI St Blk K X) (s : List (K × X)) :
    (simulateQ (ITSROracles (probI IV ib ob od idx g)) (simulateQ (instImpl g) A)).run s =
      simulateQ (instImpl₀ g) ((simulateQ tgtImpl A).run s) := by
  refine simulateQ_run_simulateQ_eq_of_step _ _ _ _ (fun t s => ?_) A s
  rcases t with n | q | x
  · simp [instImpl, tgtImpl, ITSROracles]
  · simp [instImpl, tgtImpl, ITSROracles]
  · simp [instImpl, tgtImpl, ITSROracles]
    exact (simulateQ_ansImpl_liftM (fun q => g q) _).symm

/-- **The monadic game at a table is VCVio's ITSR experiment.** -/
theorem simulateQ_gameProg [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (A : ItsrAdvI St Blk K X) (g : CF St Blk) :
    simulateQ (instImpl₀ g) (gameProg IV ib ob od idx A) =
      ITSRExperiment (A.inst (probI IV ib ob od idx g) g) := by
  simp only [gameProg, simulateQ_bind, simulateQ_hashAllM, simulateQ_hashM, pure_bind,
    simulateQ_pure, ITSRExperiment, ITSRAdversary.run, ItsrAdvI.inst, run_tgt_eq]
  refine bind_congr fun z => ?_
  refine congrArg pure (decide_eq_decide.mpr ?_)
  simp only [ITSRProblem.Wins, ITSRProblem.indexSet, ITSRProblem.targetIndexSet, probI,
    List.flatMap_map]
  rfl

end Ideal.Itsr

#print axioms Ideal.Itsr.simulateQ_gameProg
