import Ideal.Core.Defs

/-!
# SM-TCR in the ideal-compression model: definitions

`THFam` is a family, indexed by the compression table `g`, of tweakable hashes of
Merkle–Damgård shape (attacked member and collection).  `THFam.tcrProb F g` is VCVio's
`SM_DT_TCR_Problem` at the table `g`; an ideal-model adversary (`TcrAdv`) has, in addition to the
oracles of the VCVio game, oracle access to the compression function in both phases, and
`TcrAdv.inst A g` is the VCVio adversary it becomes once the table is fixed.  The ideal-model
advantage is the VCVio advantage averaged over a uniform table.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

/-- A family of Merkle–Damgård tweakable hashes over a compression function with chaining values
`St` and blocks `Blk`: the hash of `(seed, t, m)` is `out` of the keyed chain over the blocks
`tch t m`; the collection member `i` hashes `(seed, t, m)` to `cout i` of the keyed chain over
`cch i t m`. -/
structure THFam (St Blk PkSeed Tweak M Y ι : Type) where
  IV : St
  sb : PkSeed → Blk
  seedGen : ProbComp PkSeed
  tch : Tweak → M → Blk × List Blk
  out : St → Y
  Msg : ι → Type
  cch : (i : ι) → Tweak → Msg i → Blk × List Blk
  cout : ι → St → Y
  numTargets : ℕ

variable {St Blk PkSeed Tweak M Y ι : Type}

namespace THFam

variable (F : THFam St Blk PkSeed Tweak M Y ι)

/-- The attacked member at the table `g`. -/
def evalT (g : CF St Blk) (pk : PkSeed) (t : Tweak) (m : M) : Y :=
  F.out (keyedChain F.IV F.sb g pk (F.tch t m))

/-- The collection at the table `g`. -/
def evalC (g : CF St Blk) (i : ι) (pk : PkSeed) (t : Tweak) (m : F.Msg i) : Y :=
  F.cout i (keyedChain F.IV F.sb g pk (F.cch i t m))

/-- The collection at the table `g`, as a VCVio collection. -/
def coll (g : CF St Blk) : TweakableHashCollection ι PkSeed Tweak Y where
  Msg := F.Msg
  eval := F.evalC g

/-- VCVio's SM-TCR problem at the table `g`. -/
def tcrProb (g : CF St Blk) : SM_DT_TCR_Problem ι PkSeed Tweak M Y where
  th := { seedGen := F.seedGen, eval := F.evalT g }
  thColl := F.coll g
  numTargets := F.numTargets

/-- The collection oracle's interface (independent of the table). -/
abbrev collS : OracleSpec ((i : ι) × Tweak × F.Msg i) := _ →ₒ Option Y

/-- Oracle interface of an ideal-model adversary's first phase: uniform sampling, the compression
function, the challenge oracle, the collection oracle. -/
abbrev advS : OracleSpec (ℕ ⊕ ((St × Blk) ⊕ ((Tweak × M) ⊕ ((i : ι) × Tweak × F.Msg i)))) :=
  unifSpec + (hS St Blk + (SM_DT_TCR_challengeSpec Tweak M Y + F.collS))

/-- A compression query of the first phase. -/
def isH : F.advS.Domain → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A challenge query. -/
def isChal : F.advS.Domain → Bool
  | .inr (.inr (.inl _)) => true
  | _ => false

/-- A collection query. -/
def isColl : F.advS.Domain → Bool
  | .inr (.inr (.inr _)) => true
  | _ => false

end THFam

/-- An SM-TCR adversary in the ideal-compression model: VCVio's `SM_DT_TCR_Adversary` with
oracle access to the compression function in both phases. -/
structure TcrAdv (F : THFam St Blk PkSeed Tweak M Y ι) where
  State : Type
  choose : OracleComp F.advS State
  forge : State → PkSeed → OracleComp (unifSpec + hS St Blk) (ℕ × M)

namespace TcrAdv

variable {F : THFam St Blk PkSeed Tweak M Y ι}

/-- The VCVio adversary obtained by fixing the compression table. -/
def inst (A : TcrAdv F) (g : CF St Blk) : SM_DT_TCR_Adversary (F.tcrProb g) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  forge := fun st pk => simulateQ (instImpl₀ g) (A.forge st pk)

/-- The first phase makes at most `q` compression queries. -/
def ChooseBound (A : TcrAdv F) (q : ℕ) : Prop :=
  IsQueryBoundP A.choose (fun i => F.isH i = true) q

/-- The first phase makes at most `q` challenge queries. -/
def ChalBound (A : TcrAdv F) (q : ℕ) : Prop :=
  IsQueryBoundP A.choose (fun i => F.isChal i = true) q

/-- The first phase makes at most `q` collection queries. -/
def CollBound (A : TcrAdv F) (q : ℕ) : Prop :=
  IsQueryBoundP A.choose (fun i => F.isColl i = true) q

/-- Every collection query of the first phase has at most `L` blocks after the first. -/
def CollLen (A : TcrAdv F) (L : ℕ) : Prop :=
  AllQueriesSatisfy A.choose fun i => match i with
    | .inr (.inr (.inr q)) => (F.cch q.1 q.2.1 q.2.2).2.length ≤ L
    | _ => True

/-- The second phase makes at most `q` compression queries. -/
def ForgeBound (A : TcrAdv F) (q : ℕ) : Prop :=
  ∀ st pk, IsQueryBoundP (A.forge st pk) (fun i => i.isRight = true) q

end TcrAdv

/-- SM-TCR advantage in the ideal-compression model: VCVio's SM-TCR experiment for the hash
built from `g` and the adversary with its compression queries answered by `g`, with `g` a
uniformly random table. -/
noncomputable def tcrAdvantage [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y ι) (A : TcrAdv F) : ℝ≥0∞ :=
  𝒟[do
    let g ← $ᵗ (CF St Blk)
    SM_DT_TCR_Experiment (A.inst g)] {true}

/-! ## The game as a program over the keyed-chain oracle -/

section Monadic

variable (F : THFam St Blk PkSeed Tweak M Y ι)

/-- Target of the monadic game: uniform sampling, public compression queries, chain queries. -/
abbrev gS (St Blk : Type) := unifSpec + (hS St Blk + chainS St Blk)

/-- The oracles of the SM-TCR game with the hash evaluations issued as chain queries and the
adversary's compression queries forwarded.  State: VCVio's `SM_DT_TCR_State`. -/
def tcrGameM [DecidableEq Tweak] :
    QueryImpl F.advS (StateT (SM_DT_TCR_State Tweak M) (OracleComp (gS St Blk))) := fun
  | .inl n => liftM ((gS St Blk).query (.inl n))
  | .inr (.inl q) => liftM ((gS St Blk).query (.inr (.inl q)))
  | .inr (.inr (.inl tm)) => do
      let (qsChal, twsColl) ← get
      if F.numTargets ≤ qsChal.length ∨ ¬ TweakFresh Prod.fst qsChal twsColl tm.1 then
        return none
      else
        set (qsChal ++ [tm], twsColl)
        let c ← liftM ((gS St Blk).query (.inr (.inr (F.tch tm.1 tm.2))))
        return some (F.out c)
  | .inr (.inr (.inr q)) => do
      let (qsChal, twsColl) ← get
      if TweakReserved (Q := Tweak × M) Prod.fst qsChal q.2.1 then
        return none
      else
        set (qsChal, twsColl ++ [q.2.1])
        let c ← liftM ((gS St Blk).query (.inr (.inr (F.cch q.1 q.2.1 q.2.2))))
        return some (F.cout q.1 c)

/-- Evaluate the attacked member through public compression queries only. -/
def evalPub (pk : PkSeed) (t : Tweak) (m : M) : OracleComp (unifSpec + hS St Blk) Y := do
  let cv ← (unifSpec + hS St Blk).query (.inr (F.IV, F.sb pk))
  let c ← (unifSpec + hS St Blk).query (.inr (cv, (F.tch t m).1))
  let c' ← (F.tch t m).2.foldlM (fun c b => (unifSpec + hS St Blk).query (.inr (c, b))) c
  return F.out c'

variable {F}

/-- Phase one of the SM-TCR game as a program over the keyed-chain oracle. -/
def tcrProg₁ [DecidableEq Tweak] (A : TcrAdv F) :
    OracleComp (gS St Blk) (A.State × SM_DT_TCR_State Tweak M) :=
  (simulateQ (tcrGameM F) A.choose).run ([], [])

/-- Phase two of the SM-TCR game (the adversary's second phase and the winning condition) as a
program making public compression queries. -/
def tcrP₂ [DecidableEq M] [DecidableEq Y] (A : TcrAdv F) (pk : PkSeed)
    (x : A.State × SM_DT_TCR_State Tweak M) : OracleComp (unifSpec + hS St Blk) Bool := do
  let (j, m) ← A.forge x.1 pk
  match x.2.1[j]? with
  | none => return false
  | some (t, mj) => do
      let y ← evalPub F pk t m
      let y' ← evalPub F pk t mj
      return decide (m ≠ mj ∧ y = y')

end Monadic

end Ideal
