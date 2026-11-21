import Ideal.Games.TcrDefs
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE

/-!
# SM-PRE in the ideal-compression model: definitions

For a Merkle–Damgård tweakable-hash family `F : THFam …` (see `Games/TcrDefs.lean`) and an
injective `emb : M' → M`, `THFam.preProb F emb hemb g` is VCVio's `SM_DT_PRE_Problem` at the
compression table `g`.  An ideal-model adversary (`PreAdv F M'`) is VCVio's
`SM_DT_PRE_Adversary` with oracle access to the compression function in both phases, and
`PreAdv.inst A emb hemb g` is the VCVio adversary it becomes once the table is fixed.  The
ideal-model advantage `preAdvantage` is the VCVio advantage averaged over a uniform table.

`preGameM`, `preProg₁`, `preP₂`: the game as a two-phase program over the keyed-chain oracle
(the form consumed by `Ideal.realGame` / `Ideal.idealGame`).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M M' Y ι : Type}

namespace THFam

variable (F : THFam St Blk PkSeed Tweak M Y ι)

/-- VCVio's SM-PRE problem at the table `g`. -/
def preProb (emb : M' → M) (hemb : Function.Injective emb) (g : CF St Blk) :
    SM_DT_PRE_Problem ι PkSeed Tweak M M' Y where
  th := { seedGen := F.seedGen, eval := F.evalT g }
  emb := emb
  emb_injective := hemb
  thColl := F.coll g
  numTargets := F.numTargets

/-- Oracle interface of an ideal-model SM-PRE adversary's first phase: uniform sampling, the
compression function, the challenge oracle (queried at a tweak), the collection oracle. -/
abbrev padvS : OracleSpec (ℕ ⊕ ((St × Blk) ⊕ (Tweak ⊕ ((i : ι) × Tweak × F.Msg i)))) :=
  unifSpec + (hS St Blk + (SM_DT_PRE_challengeSpec Tweak Y + F.collS))

/-- A compression query of the first phase. -/
def pIsH : F.padvS.Domain → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A challenge query. -/
def pIsChal : F.padvS.Domain → Bool
  | .inr (.inr (.inl _)) => true
  | _ => false

/-- A collection query. -/
def pIsColl : F.padvS.Domain → Bool
  | .inr (.inr (.inr _)) => true
  | _ => false

end THFam

/-- An SM-PRE adversary in the ideal-compression model: VCVio's `SM_DT_PRE_Adversary` with
oracle access to the compression function in both phases.  `M'` is the subspace the challenge
oracle samples from and the adversary answers in. -/
structure PreAdv (F : THFam St Blk PkSeed Tweak M Y ι) (M' : Type) where
  State : Type
  choose : OracleComp F.padvS State
  invert : State → PkSeed → OracleComp (unifSpec + hS St Blk) (ℕ × M')

namespace PreAdv

variable {F : THFam St Blk PkSeed Tweak M Y ι}

/-- The VCVio adversary obtained by fixing the compression table. -/
def inst (A : PreAdv F M') (emb : M' → M) (hemb : Function.Injective emb) (g : CF St Blk) :
    SM_DT_PRE_Adversary (F.preProb emb hemb g) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  invert := fun st pk => simulateQ (instImpl₀ g) (A.invert st pk)

/-- The first phase makes at most `q` compression queries. -/
def ChooseBound (A : PreAdv F M') (q : ℕ) : Prop :=
  IsQueryBoundP A.choose (fun i => F.pIsH i = true) q

/-- The first phase makes at most `q` challenge queries. -/
def ChalBound (A : PreAdv F M') (q : ℕ) : Prop :=
  IsQueryBoundP A.choose (fun i => F.pIsChal i = true) q

/-- The first phase makes at most `q` collection queries. -/
def CollBound (A : PreAdv F M') (q : ℕ) : Prop :=
  IsQueryBoundP A.choose (fun i => F.pIsColl i = true) q

/-- Every collection query of the first phase has at most `L` blocks after the first. -/
def CollLen (A : PreAdv F M') (L : ℕ) : Prop :=
  AllQueriesSatisfy A.choose fun i => match i with
    | .inr (.inr (.inr q)) => (F.cch q.1 q.2.1 q.2.2).2.length ≤ L
    | _ => True

/-- The second phase makes at most `q` compression queries. -/
def InvertBound (A : PreAdv F M') (q : ℕ) : Prop :=
  ∀ st pk, IsQueryBoundP (A.invert st pk) (fun i => i.isRight = true) q

end PreAdv

/-- SM-PRE advantage in the ideal-compression model: VCVio's SM-PRE experiment for the hash
built from `g` and the adversary with its compression queries answered by `g`, with `g` a
uniformly random table. -/
noncomputable def preAdvantage [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M)
    (hemb : Function.Injective emb) (A : PreAdv F M') : ℝ≥0∞ :=
  𝒟[do
    let g ← $ᵗ (CF St Blk)
    SM_DT_PRE_Experiment (A.inst emb hemb g)] {true}

/-! ## The game as a program over the keyed-chain oracle -/

section Monadic

variable (F : THFam St Blk PkSeed Tweak M Y ι)

/-- The oracles of the SM-PRE game with the hash evaluations issued as chain queries and the
adversary's compression queries forwarded; the challenge oracle draws its message by lifting
`$ᵗ M'`.  State: VCVio's `SM_DT_PRE_State`. -/
def preGameM [DecidableEq Tweak] [SampleableType M'] (emb : M' → M) :
    QueryImpl F.padvS (StateT (SM_DT_PRE_State Tweak M') (OracleComp (gS St Blk))) := fun
  | .inl n => liftM ((gS St Blk).query (.inl n))
  | .inr (.inl q) => liftM ((gS St Blk).query (.inr (.inl q)))
  | .inr (.inr (.inl t)) => do
      let (qsChal, twsColl) ← get
      if F.numTargets ≤ qsChal.length ∨ ¬ TweakFresh Prod.fst qsChal twsColl t then
        return none
      else
        let x ← (liftM (liftM ($ᵗ M' : ProbComp M') : OracleComp (gS St Blk) M') :
          StateT (SM_DT_PRE_State Tweak M') (OracleComp (gS St Blk)) M')
        set (qsChal ++ [(t, x)], twsColl)
        let c ← liftM ((gS St Blk).query (.inr (.inr (F.tch t (emb x)))))
        return some (F.out c)
  | .inr (.inr (.inr q)) => do
      let (qsChal, twsColl) ← get
      if TweakReserved (Q := Tweak × M') Prod.fst qsChal q.2.1 then
        return none
      else
        set (qsChal, twsColl ++ [q.2.1])
        let c ← liftM ((gS St Blk).query (.inr (.inr (F.cch q.1 q.2.1 q.2.2))))
        return some (F.cout q.1 c)

variable {F}

/-- Phase one of the SM-PRE game as a program over the keyed-chain oracle. -/
def preProg₁ [DecidableEq Tweak] [SampleableType M'] (emb : M' → M) (A : PreAdv F M') :
    OracleComp (gS St Blk) (A.State × SM_DT_PRE_State Tweak M') :=
  (simulateQ (preGameM F emb) A.choose).run ([], [])

/-- Phase two of the SM-PRE game (the adversary's second phase and the winning condition) as a
program making public compression queries. -/
def preP₂ [DecidableEq Y] (emb : M' → M) (A : PreAdv F M') (pk : PkSeed)
    (x : A.State × SM_DT_PRE_State Tweak M') : OracleComp (unifSpec + hS St Blk) Bool := do
  let (j, m) ← A.invert x.1 pk
  match x.2.1[j]? with
  | none => return false
  | some (t, xj) => do
      let y ← evalPub F pk t (emb m)
      let y' ← evalPub F pk t (emb xj)
      return decide (y = y')

end Monadic

end Ideal
