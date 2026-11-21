import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR

/-!
# Ideal-compression-function model: core definitions

`St` is the chaining-value type and `Blk` the message-block type of a compression function
`g : St × Blk → St`.  In the ideal model `g` is a uniformly random table (`CF St Blk`) and the
adversary has oracle access to it (`hS St Blk`).

The scheme's tweakable hash has the shape (Merkle–Damgård, first block a function of the public
seed alone)

`Th_g(seed, x) = out (foldl g (g (g (IV, sb seed), B₁)) rest)`,  `(B₁, rest) = blocks x`

which is `keyedChain` below.  Everything in this file is generic in `St`, `Blk`.
-/

open OracleComp OracleSpec

namespace Ideal

variable (St Blk : Type)

/-- A compression-function table. -/
abbrev CF := St × Blk → St

/-- Oracle interface to the compression function. -/
abbrev hS : OracleSpec (St × Blk) := (St × Blk) →ₒ St

/-- Oracle interface "evaluate the keyed chain at these blocks" (first block, later blocks).
Used only by the challenger side of a game, never by an adversary. -/
abbrev chainS : OracleSpec (Blk × List Blk) := (Blk × List Blk) →ₒ St

/-- The private row table of the ideal game: `B ↦ ` chaining value after the first message block. -/
abbrev tS : OracleSpec Blk := Blk →ₒ St

variable {St Blk}

/-- Merkle–Damgård iteration from a chaining value. -/
def mdFold (g : CF St Blk) (c : St) (bs : List Blk) : St := bs.foldl (fun c b => g (c, b)) c

/-- The keyed chain: start from `IV`, absorb the seed block, then the given blocks. -/
def keyedChain {PkSeed : Type} (IV : St) (sb : PkSeed → Blk) (g : CF St Blk) (seed : PkSeed)
    (bs : Blk × List Blk) : St :=
  mdFold g (g (g (IV, sb seed), bs.1)) bs.2

/-! ## Instantiating oracle programs at a fixed table -/

/-- Answer compression queries with the table `g`; forward uniform sampling and the remaining
oracles `spec`. -/
def instImpl {ι : Type} {spec : OracleSpec ι} (g : CF St Blk) :
    QueryImpl (unifSpec + (hS St Blk + spec)) (OracleComp (unifSpec + spec)) := fun
  | .inl n => (unifSpec + spec).query (.inl n)
  | .inr (.inl q) => pure (g q)
  | .inr (.inr t) => (unifSpec + spec).query (.inr t)

/-- Answer compression queries with the table `g`; forward uniform sampling. -/
def instImpl₀ (g : CF St Blk) : QueryImpl (unifSpec + hS St Blk) ProbComp :=
  unifFwdAnswerImpl (QueryImpl.ofFn fun q => g q)

/-- Eager phase-one semantics: public compression queries are answered by `pub`, chain queries
by `chain`; uniform sampling is forwarded. -/
def ans₁ (pub : CF St Blk) (chain : Blk × List Blk → St) :
    QueryImpl (unifSpec + (hS St Blk + chainS St Blk)) ProbComp :=
  unifFwdAnswerImpl (QueryImpl.ofFn fun
    | .inl q => pub q
    | .inr q => chain q)

/-- A public (adversarial) compression query. -/
def isPub : ℕ ⊕ ((St × Blk) ⊕ (Blk × List Blk)) → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A chain query (challenger side). -/
def isChain : ℕ ⊕ ((St × Blk) ⊕ (Blk × List Blk)) → Bool
  | .inr (.inr _) => true
  | _ => false

/-- Every chain query has at most `L` continuation blocks. -/
def chainLenLe (L : ℕ) : ℕ ⊕ ((St × Blk) ⊕ (Blk × List Blk)) → Prop
  | .inr (.inr q) => q.2.length ≤ L
  | _ => True

/-! ## The ideal (hidden-prefix) game -/

/-- Phase one of the ideal game: a chain query reads the private row table at its first block
and continues through the public table. -/
def chainToT : QueryImpl (unifSpec + (hS St Blk + chainS St Blk))
    (OracleComp (unifSpec + (hS St Blk + tS St Blk))) := fun
  | .inl n => (unifSpec + (hS St Blk + tS St Blk)).query (.inl n)
  | .inr (.inl q) => (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl q))
  | .inr (.inr q) => do
      let c ← (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inr q.1))
      q.2.foldlM (fun c b => (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl (c, b)))) c

/-- Phase two of the ideal game: with the seed and the chaining value `cv` after the seed block
now fixed, a public query at `(IV, sb seed)` returns `cv`, a public query in row `cv` reads the
private row table, and every other public query reads the public table. -/
def route [DecidableEq St] [DecidableEq Blk] (IV : St) (sbSeed : Blk) (cv : St) :
    QueryImpl (unifSpec + hS St Blk) (OracleComp (unifSpec + (hS St Blk + tS St Blk))) := fun
  | .inl n => (unifSpec + (hS St Blk + tS St Blk)).query (.inl n)
  | .inr q =>
      if q = (IV, sbSeed) then pure cv
      else if q.1 = cv then (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inr q.2))
      else (unifSpec + (hS St Blk + tS St Blk)).query (.inr (.inl q))

/-- The ideal game as one program over the public table and the private row table.  The seed
and `cv` are drawn only after phase one, which does not depend on them. -/
def idealProg [DecidableEq St] [DecidableEq Blk] [SampleableType St] {PkSeed σ : Type}
    (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) :
    OracleComp (unifSpec + (hS St Blk + tS St Blk)) Bool := do
  let x ← simulateQ chainToT prog₁
  let seed ← (liftM seedGen : OracleComp (unifSpec + (hS St Blk + tS St Blk)) PkSeed)
  let cv ← (liftM ($ᵗ St : ProbComp St) : OracleComp (unifSpec + (hS St Blk + tS St Blk)) St)
  simulateQ (route IV (sb seed) cv) (P₂ seed x)

/-- The real game in eager form: sample the table, the seed, run phase one against the table
and the keyed chain, then phase two against the table. -/
def realGame [SampleableType (CF St Blk)] {PkSeed σ : Type}
    (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) : ProbComp Bool := do
  let g ← $ᵗ (CF St Blk)
  let seed ← seedGen
  let x ← simulateQ (ans₁ g (keyedChain IV sb g seed)) prog₁
  simulateQ (instImpl₀ g) (P₂ seed x)

/-- The ideal game in lazy form. -/
noncomputable def idealGame [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    {PkSeed σ : Type}
    (IV : St) (sb : PkSeed → Blk) (seedGen : ProbComp PkSeed)
    (prog₁ : OracleComp (unifSpec + (hS St Blk + chainS St Blk)) σ)
    (P₂ : PkSeed → σ → OracleComp (unifSpec + hS St Blk) Bool) : ProbComp Bool :=
  (simulateQ (hS St Blk + tS St Blk).romImpl (idealProg IV sb seedGen prog₁ P₂)).run' ∅

end Ideal
