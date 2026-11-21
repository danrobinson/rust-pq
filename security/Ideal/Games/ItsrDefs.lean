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
  hashes of the targets and of the candidate) as one program over the *marked* compression oracle
  `mS`: every compression call carries a Boolean mark that does not affect its answer.  Marked
  (`true`) are the adversary's calls and, in each Merkle–Damgård iteration of the final check,
  the call at block position 1 (the second block).  `simulateQ_gameProg`: at every table `g` the
  program is VCVio's `ITSRExperiment`.
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

/-! ## The experiment as one program over the marked compression oracle -/

/-- The compression oracle with a Boolean mark on every query. -/
abbrev mS (St Blk : Type) : OracleSpec ((St × Blk) × Bool) := ((St × Blk) × Bool) →ₒ St

/-- Answer marked compression queries with the table `g` (the mark is ignored); forward uniform
sampling. -/
def markImpl (g : CF St Blk) : QueryImpl (unifSpec + mS St Blk) ProbComp :=
  ansImpl (spec := mS St Blk) fun t => g t.1

theorem markImpl_eq (g : CF St Blk) :
    markImpl g = ansImpl (spec := mS St Blk) fun t => g t.1 := rfl

@[simp] theorem markImpl_inl (g : CF St Blk) (n : ℕ) :
    markImpl g (.inl n) = unifSpec.query n := rfl

@[simp] theorem markImpl_inr (g : CF St Blk) (t : (St × Blk) × Bool) :
    markImpl g (.inr t) = pure (g t.1) := rfl

/-- A marked compression query. -/
def cq (c : St) (b : Blk) (m : Bool) : OracleComp (unifSpec + mS St Blk) St :=
  liftM ((unifSpec + mS St Blk).query (.inr ((c, b), m)))

/-- Merkle–Damgård iteration issued as unmarked compression queries. -/
def mdMF : St → List Blk → OracleComp (unifSpec + mS St Blk) St
  | c, [] => pure c
  | c, b :: bs => cq c b false >>= fun c' => mdMF c' bs

/-- Merkle–Damgård iteration issued as compression queries; the query at block position 1 is
marked. -/
def mdM (c : St) : List Blk → OracleComp (unifSpec + mS St Blk) St
  | [] => pure c
  | [b₀] => cq c b₀ false
  | b₀ :: b₁ :: bs => cq c b₀ false >>= fun c₁ => cq c₁ b₁ true >>= fun c₂ => mdMF c₂ bs

/-- The keyed hash issued as compression queries. -/
def hashM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (kx : K × X) : OracleComp (unifSpec + mS St Blk) Y := do
  let s ← mdM IV (ib kx)
  let o ← mdM IV (ob kx s)
  pure (od o)

/-- The keyed hashes of a list of inputs, issued as compression queries. -/
def hashAllM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y) :
    List (K × X) → OracleComp (unifSpec + mS St Blk) (List Y)
  | [] => pure []
  | kx :: l => do
      let d ← hashM IV ib ob od kx
      let ds ← hashAllM IV ib ob od l
      pure (d :: ds)

/-- The target oracle over the marked compression oracle: the adversary's compression queries
are marked; a target query draws a uniform key and records the pair. -/
def tgtImpl [SampleableType K] :
    QueryImpl (unifSpec + (hS St Blk + ITSRTargetSpec X K))
      (StateT (List (K × X)) (OracleComp (unifSpec + mS St Blk))) := fun
  | .inl n => StateT.mk fun s =>
      (fun u => (u, s)) <$> (liftM ((unifSpec + mS St Blk).query (.inl n)) :
        OracleComp (unifSpec + mS St Blk) _)
  | .inr (.inl q) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (liftM ((unifSpec + mS St Blk).query (.inr (q, true))) :
        OracleComp (unifSpec + mS St Blk) _)
  | .inr (.inr x) => StateT.mk fun s =>
      (fun k : K => (k, s ++ [(k, x)])) <$> (liftM ($ᵗ K : ProbComp K) :
        OracleComp (unifSpec + mS St Blk) K)

/-- The final check: compute the hashes of the targets and of the candidate and evaluate the
winning condition. -/
def finM [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (z : (K × X) × List (K × X)) :
    OracleComp (unifSpec + mS St Blk) Bool := do
  let ds ← hashAllM IV ib ob od z.2
  let d ← hashM IV ib ob od z.1
  pure (decide (z.1 ∉ z.2 ∧ ∀ i ∈ idx d, i ∈ ds.flatMap idx))

/-- The whole ITSR experiment as one program over the marked compression oracle: run the
adversary against the target oracle, then the final check. -/
def gameProg [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (A : ItsrAdvI St Blk K X) : OracleComp (unifSpec + mS St Blk) Bool :=
  (simulateQ tgtImpl A).run [] >>= finM IV ib ob od idx

/-! ## Evaluation at a table -/

theorem simulateQ_cq_bind {α : Type} (g : CF St Blk) (c : St) (b : Blk) (m : Bool)
    (k : St → OracleComp (unifSpec + mS St Blk) α) :
    simulateQ (markImpl g) (cq c b m >>= k) = simulateQ (markImpl g) (k (g (c, b))) :=
  simulateQ_ansImpl_inr_bind (spec := mS St Blk) (fun t => g t.1) ((c, b), m) k

theorem simulateQ_cq (g : CF St Blk) (c : St) (b : Blk) (m : Bool) :
    simulateQ (markImpl g) (cq c b m) = pure (g (c, b)) := by
  have h := simulateQ_cq_bind g c b m pure
  simpa using h

theorem simulateQ_mdMF (g : CF St Blk) (c : St) (bs : List Blk) :
    simulateQ (markImpl g) (mdMF c bs) = pure (mdFold g c bs) := by
  induction bs generalizing c with
  | nil => simp [mdMF, mdFold]
  | cons b bs ih => rw [mdMF, simulateQ_cq_bind, ih]; rfl

theorem simulateQ_mdM (g : CF St Blk) (c : St) (bs : List Blk) :
    simulateQ (markImpl g) (mdM c bs) = pure (mdFold g c bs) := by
  match bs with
  | [] => simp [mdM, mdFold]
  | [b₀] => rw [mdM, simulateQ_cq]; rfl
  | b₀ :: b₁ :: bs => rw [mdM, simulateQ_cq_bind, simulateQ_cq_bind, simulateQ_mdMF]; rfl

theorem simulateQ_hashM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk)
    (od : St → Y) (g : CF St Blk) (kx : K × X) :
    simulateQ (markImpl g) (hashM IV ib ob od kx) = pure (hashG IV ib ob od g kx) := by
  simp only [hashM, simulateQ_bind, simulateQ_mdM, pure_bind, simulateQ_pure, hashG]

theorem simulateQ_hashAllM (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk)
    (od : St → Y) (g : CF St Blk) (l : List (K × X)) :
    simulateQ (markImpl g) (hashAllM IV ib ob od l) = pure (l.map (hashG IV ib ob od g)) := by
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
      simulateQ (markImpl g) ((simulateQ tgtImpl A).run s) := by
  refine simulateQ_run_simulateQ_eq_of_step _ _ _ _ (fun t s => ?_) A s
  rcases t with n | q | x
  · simp [instImpl, tgtImpl, ITSROracles]
  · simp [instImpl, tgtImpl, ITSROracles]
  · simp [instImpl, tgtImpl, ITSROracles]
    exact (simulateQ_ansImpl_liftM (spec := mS St Blk) (fun t => g t.1) _).symm

/-- **The monadic game at a table is VCVio's ITSR experiment.** -/
theorem simulateQ_gameProg [SampleableType K] [DecidableEq K] [DecidableEq X] [DecidableEq Index]
    (IV : St) (ib : K × X → List Blk) (ob : K × X → St → List Blk) (od : St → Y)
    (idx : Y → List Index) (A : ItsrAdvI St Blk K X) (g : CF St Blk) :
    simulateQ (markImpl g) (gameProg IV ib ob od idx A) =
      ITSRExperiment (A.inst (probI IV ib ob od idx g) g) := by
  simp only [gameProg, finM, simulateQ_bind, simulateQ_hashAllM, simulateQ_hashM, pure_bind,
    simulateQ_pure, ITSRExperiment, ITSRAdversary.run, ItsrAdvI.inst, run_tgt_eq]
  refine bind_congr fun z => ?_
  refine congrArg pure (decide_eq_decide.mpr ?_)
  simp only [ITSRProblem.Wins, ITSRProblem.indexSet, ITSRProblem.targetIndexSet, probI,
    List.flatMap_map]
  rfl

end Ideal.Itsr

#print axioms Ideal.Itsr.simulateQ_gameProg
