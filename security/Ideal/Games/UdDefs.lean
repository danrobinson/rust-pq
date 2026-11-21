import Ideal.Games.PreDefs
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD

/-!
# SM-UD in the ideal-compression model: definitions

For a Merkle–Damgård tweakable-hash family `F : THFam …` (see `Games/TcrDefs.lean`) and an
injective `emb : M' → M`, `THFam.udProb F emb hemb g` is VCVio's `SM_DT_UD_Problem` at the
compression table `g`, with uniform hidden inputs (`inputGen = $ᵗ M'`) and uniform ideal
responses (`outputGen = $ᵗ Y`).  An ideal-model adversary (`UdAdv F`) is VCVio's
`SM_DT_UD_Adversary` with oracle access to the compression function in both phases (its first
phase has the oracle interface `F.padvS` of the SM-PRE game: the challenge oracles of the two
games have the same signature), and `UdAdv.inst A emb hemb g` is the VCVio adversary it becomes
once the table is fixed.  `udRealI`, `udIdealI` are VCVio's success probabilities
`SM_DT_UD_RealSuccess`, `SM_DT_UD_IdealSuccess` averaged over a uniform table.

`udGameM`, `udProg₁`, `udP₂`: each world of the game as a two-phase program over the
keyed-chain oracle (the form consumed by `Ideal.realGame` / `Ideal.idealGame`).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M M' Y ι : Type}

namespace THFam

variable (F : THFam St Blk PkSeed Tweak M Y ι)

/-- VCVio's SM-UD problem at the table `g`, with uniform hidden inputs and uniform ideal
responses. -/
def udProb [SampleableType M'] [SampleableType Y] (emb : M' → M)
    (hemb : Function.Injective emb) (g : CF St Blk) :
    SM_DT_UD_Problem ι PkSeed Tweak M M' Y where
  th := { seedGen := F.seedGen, eval := F.evalT g }
  emb := emb
  emb_injective := hemb
  inputGen := $ᵗ M'
  outputGen := $ᵗ Y
  thColl := F.coll g
  numTargets := F.numTargets

end THFam

/-- An SM-UD adversary in the ideal-compression model: VCVio's `SM_DT_UD_Adversary` with oracle
access to the compression function in both phases. -/
structure UdAdv (F : THFam St Blk PkSeed Tweak M Y ι) where
  State : Type
  pick : OracleComp F.padvS State
  distinguish : State → PkSeed → OracleComp (unifSpec + hS St Blk) Bool

namespace UdAdv

variable {F : THFam St Blk PkSeed Tweak M Y ι}

/-- The VCVio adversary obtained by fixing the compression table. -/
def inst [SampleableType M'] [SampleableType Y] (A : UdAdv F) (emb : M' → M)
    (hemb : Function.Injective emb) (g : CF St Blk) :
    SM_DT_UD_Adversary (F.udProb emb hemb g) where
  State := A.State
  pick := simulateQ (instImpl g) A.pick
  distinguish := fun st pk => simulateQ (instImpl₀ g) (A.distinguish st pk)

/-- The adversary with its output bit negated. -/
def neg (A : UdAdv F) : UdAdv F where
  State := A.State
  pick := A.pick
  distinguish := fun st pk => not <$> A.distinguish st pk

/-- The first phase makes at most `q` compression queries. -/
def PickBound (A : UdAdv F) (q : ℕ) : Prop :=
  IsQueryBoundP A.pick (fun i => F.pIsH i = true) q

/-- The first phase makes at most `q` challenge queries. -/
def ChalBound (A : UdAdv F) (q : ℕ) : Prop :=
  IsQueryBoundP A.pick (fun i => F.pIsChal i = true) q

/-- The first phase makes at most `q` collection queries. -/
def CollBound (A : UdAdv F) (q : ℕ) : Prop :=
  IsQueryBoundP A.pick (fun i => F.pIsColl i = true) q

/-- Every collection query of the first phase has at most `L` blocks after the first. -/
def CollLen (A : UdAdv F) (L : ℕ) : Prop :=
  AllQueriesSatisfy A.pick fun i => match i with
    | .inr (.inr (.inr q)) => (F.cch q.1 q.2.1 q.2.2).2.length ≤ L
    | _ => True

/-- The second phase makes at most `q` compression queries. -/
def DistBound (A : UdAdv F) (q : ℕ) : Prop :=
  ∀ st pk, IsQueryBoundP (A.distinguish st pk) (fun i => i.isRight = true) q

end UdAdv

/-- Real-world SM-UD success probability in the ideal-compression model: VCVio's real-world
SM-UD experiment for the hash built from `g` and the adversary with its compression queries
answered by `g`, with `g` a uniformly random table. -/
noncomputable def udRealI [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M)
    (hemb : Function.Injective emb) (A : UdAdv F) : ℝ≥0∞ :=
  𝒟[do
    let g ← $ᵗ (CF St Blk)
    SM_DT_UD_Experiment .real (A.inst emb hemb g)] {true}

/-- Ideal-world SM-UD success probability in the ideal-compression model (the collection oracle
still hashes through the uniformly random table `g`). -/
noncomputable def udIdealI [DecidableEq Tweak] [SampleableType M'] [SampleableType Y]
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y ι) (emb : M' → M)
    (hemb : Function.Injective emb) (A : UdAdv F) : ℝ≥0∞ :=
  𝒟[do
    let g ← $ᵗ (CF St Blk)
    SM_DT_UD_Experiment .ideal (A.inst emb hemb g)] {true}

/-! ## The game as a program over the keyed-chain oracle -/

section Monadic

variable (F : THFam St Blk PkSeed Tweak M Y ι)

/-- The oracles of the SM-UD game in the given world, with the hash evaluations issued as chain
queries and the adversary's compression queries forwarded; the challenge oracle draws its hidden
input (real world) or its response (ideal world) by lifting `$ᵗ M'` / `$ᵗ Y`.  State: VCVio's
`SM_DT_UD_State`. -/
def udGameM [DecidableEq Tweak] [SampleableType M'] [SampleableType Y] (world : SM_DT_UD_World)
    (emb : M' → M) :
    QueryImpl F.padvS (StateT (SM_DT_UD_State Tweak) (OracleComp (gS St Blk))) := fun
  | .inl n => liftM ((gS St Blk).query (.inl n))
  | .inr (.inl q) => liftM ((gS St Blk).query (.inr (.inl q)))
  | .inr (.inr (.inl t)) => do
      let (qsChal, twsColl) ← get
      if F.numTargets ≤ qsChal.length ∨ ¬ TweakFresh id qsChal twsColl t then
        return none
      else
        match world with
        | .real => do
            let x ← (liftM (liftM ($ᵗ M' : ProbComp M') : OracleComp (gS St Blk) M') :
              StateT (SM_DT_UD_State Tweak) (OracleComp (gS St Blk)) M')
            set (qsChal ++ [t], twsColl)
            let c ← liftM ((gS St Blk).query (.inr (.inr (F.tch t (emb x)))))
            return some (F.out c)
        | .ideal => do
            let y ← (liftM (liftM ($ᵗ Y : ProbComp Y) : OracleComp (gS St Blk) Y) :
              StateT (SM_DT_UD_State Tweak) (OracleComp (gS St Blk)) Y)
            set (qsChal ++ [t], twsColl)
            return some y
  | .inr (.inr (.inr q)) => do
      let (qsChal, twsColl) ← get
      if TweakReserved (Q := Tweak) id qsChal q.2.1 then
        return none
      else
        set (qsChal, twsColl ++ [q.2.1])
        let c ← liftM ((gS St Blk).query (.inr (.inr (F.cch q.1 q.2.1 q.2.2))))
        return some (F.cout q.1 c)

variable {F}

/-- Phase one of the SM-UD game in the given world as a program over the keyed-chain oracle. -/
def udProg₁ [DecidableEq Tweak] [SampleableType M'] [SampleableType Y] (world : SM_DT_UD_World)
    (emb : M' → M) (A : UdAdv F) :
    OracleComp (gS St Blk) (A.State × SM_DT_UD_State Tweak) :=
  (simulateQ (udGameM F world emb) A.pick).run ([], [])

/-- Phase two of the SM-UD game (the adversary's second phase; its bit is the outcome) as a
program making public compression queries. -/
def udP₂ (A : UdAdv F) (pk : PkSeed) (x : A.State × SM_DT_UD_State Tweak) :
    OracleComp (unifSpec + hS St Blk) Bool :=
  A.distinguish x.1 pk

end Monadic

end Ideal
