import Ideal.Games.TcrFVDefs
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPRFinalValidity

/-!
# Source-final-validity SM-DSPR (stand-alone) in the ideal-compression model: definitions

The game is VCVio's `TweakableHash.SM_DT_DSPR_SourceFinalValidity` at the *stand-alone* problem
(empty collection).  The adversary selects targets `(t, m)` (every query is answered and
recorded; cap and tweak distinctness are checked by the sticky bit `valid`), then, given the
public seed, names a recorded target `j` and a bit `b`.

* `experiment` (probability `Success`): accept iff valid and
  `b = [target j has a second preimage]`;
* `spExperiment` (probability `SPProbability`): accept iff valid and target `j` has a second
  preimage.

The hash family is a `THFam` with index type `Empty` (as in `TcrFVDefs.lean`).  An ideal-model
adversary (`DsprAdv`) has, in addition to the oracles of the VCVio game, oracle access to the
compression function in both phases; `DsprAdv.inst A g` is the VCVio adversary it becomes once
the table is fixed.  `dsprSuccessI`, `dsprSPI` are VCVio's two probabilities averaged over a
uniform table.

The first-phase interface, the monitor state and the phase-one game handler coincide with those
of the SM-TCR game (`THFam.fvAdvS`, `fvGameM`): both VCVio games use the challenge interface
`(Tweak × M) →ₒ Y` and the state `SourceFinalValidity.State (Tweak × M) Tweak`.

The winning conditions quantify over the whole message space.  In the phase-two program
`dsprP₂` the second-preimage bit is computed by `spPub`: evaluate the hash at the target and then
at every message of `Finset.univ.toList` through public compression queries (`spScan`).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y : Type}

namespace THFam

variable (F : THFam St Blk PkSeed Tweak M Y Empty)

/-- VCVio's stand-alone source-final-validity SM-DSPR problem at the table `g`. -/
def dsprProb (g : CF St Blk) : SM_DT_DSPR_SourceFinalValidity.Problem Empty PkSeed Tweak M Y :=
  .standalone (F.fvTh g) F.numTargets

end THFam

/-- A source-final-validity SM-DSPR adversary in the ideal-compression model: VCVio's
`SM_DT_DSPR_SourceFinalValidity.Adversary` (stand-alone problem) with oracle access to the
compression function in both phases. -/
structure DsprAdv (F : THFam St Blk PkSeed Tweak M Y Empty) where
  State : Type
  choose : OracleComp F.fvAdvS State
  guess : State → PkSeed → OracleComp (unifSpec + hS St Blk) (ℕ × Bool)

namespace DsprAdv

variable {F : THFam St Blk PkSeed Tweak M Y Empty}

/-- The VCVio adversary obtained by fixing the compression table. -/
def inst (A : DsprAdv F) (g : CF St Blk) :
    SM_DT_DSPR_SourceFinalValidity.Adversary (F.dsprProb g) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  guess := fun st pk => simulateQ (instImpl₀ g) (A.guess st pk)

/-- The first phase makes at most `q` compression queries. -/
def ChooseBound (A : DsprAdv F) (q : ℕ) : Prop :=
  IsQueryBoundP A.choose (fun i => F.fvIsH i = true) q

/-- The first phase makes at most `q` challenge queries. -/
def ChalBound (A : DsprAdv F) (q : ℕ) : Prop :=
  IsQueryBoundP A.choose (fun i => F.fvIsChal i = true) q

/-- The second phase makes at most `q` compression queries. -/
def GuessBound (A : DsprAdv F) (q : ℕ) : Prop :=
  ∀ st pk, IsQueryBoundP (A.guess st pk) (fun i => i.isRight = true) q

end DsprAdv

/-- Raw DSPR prediction success in the ideal-compression model: VCVio's `experiment` (whose
probability of `true` is `SM_DT_DSPR_SourceFinalValidity.Success`) for the hash built from `g`
and the adversary with its compression queries answered by `g`, with `g` a uniformly random
table. -/
noncomputable def dsprSuccessI [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y Empty) (A : DsprAdv F) :
    ℝ≥0∞ :=
  idealAdv St Blk fun g => SM_DT_DSPR_SourceFinalValidity.experiment (A.inst g)

/-- The `SPprob` baseline in the ideal-compression model: VCVio's `spExperiment` (whose
probability of `true` is `SM_DT_DSPR_SourceFinalValidity.SPProbability`), table-averaged. -/
noncomputable def dsprSPI [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y Empty) (A : DsprAdv F) :
    ℝ≥0∞ :=
  idealAdv St Blk fun g => SM_DT_DSPR_SourceFinalValidity.spExperiment (A.inst g)

theorem dsprSuccessI_def [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y Empty) (A : DsprAdv F) :
    dsprSuccessI F A = 𝒟[do
      let g ← $ᵗ (CF St Blk)
      SM_DT_DSPR_SourceFinalValidity.experiment (A.inst g)] {true} := rfl

theorem dsprSPI_def [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y Empty) (A : DsprAdv F) :
    dsprSPI F A = 𝒟[do
      let g ← $ᵗ (CF St Blk)
      SM_DT_DSPR_SourceFinalValidity.spExperiment (A.inst g)] {true} := rfl

/-- For every table, the fibre probabilities are VCVio's `Success` and `SPProbability`. -/
theorem dsprSuccess_fibre [Fintype M] [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {F : THFam St Blk PkSeed Tweak M Y Empty} (A : DsprAdv F) (g : CF St Blk) :
    SM_DT_DSPR_SourceFinalValidity.Success (A.inst g) =
        𝒟[SM_DT_DSPR_SourceFinalValidity.experiment (A.inst g)] {true} ∧
      SM_DT_DSPR_SourceFinalValidity.SPProbability (A.inst g) =
        𝒟[SM_DT_DSPR_SourceFinalValidity.spExperiment (A.inst g)] {true} := ⟨rfl, rfl⟩

/-! ## The game as a program over the keyed-chain oracle -/

section Monadic

variable (F : THFam St Blk PkSeed Tweak M Y Empty)

/-- Scan a list of messages for a second preimage of `m` with image `y`, evaluating the hash
through public compression queries: returns `true` iff some `a` in the list has `m ≠ a` and
image `y`.  Every message of the list is evaluated. -/
def spScan [DecidableEq M] [DecidableEq Y] (pk : PkSeed) (t : Tweak) (m : M) (y : Y) :
    List M → OracleComp (unifSpec + hS St Blk) Bool
  | [] => pure false
  | a :: l => do
      let y' ← evalPub F pk t a
      let r ← spScan pk t m y l
      return (decide (m ≠ a ∧ y = y') || r)

/-- Decide through public compression queries whether `m` has a second preimage under tweak `t`:
evaluate the hash at `m`, then at every message. -/
noncomputable def spPub [Fintype M] [DecidableEq M] [DecidableEq Y] (pk : PkSeed) (t : Tweak) (m : M) :
    OracleComp (unifSpec + hS St Blk) Bool := do
  let y ← evalPub F pk t m
  spScan F pk t m y (Finset.univ : Finset M).toList

variable {F}

/-- Phase one of the game as a program over the keyed-chain oracle (the handler is that of the
SM-TCR game). -/
def dsprProg₁ [DecidableEq Tweak] (A : DsprAdv F) :
    OracleComp (gS St Blk) (A.State × SM_DT_DSPR_SourceFinalValidity.State Tweak M) :=
  (simulateQ (fvGameM F) A.choose).run .initial

/-- Phase two of the game: the adversary's second phase and the winning condition `win sp b`
of the second-preimage bit `sp` of the selected target and the guessed bit `b` (including the
final validity bit), as a program making public compression queries. -/
noncomputable def dsprP₂ [Fintype M] [DecidableEq M] [DecidableEq Y] (win : Bool → Bool → Bool)
    (A : DsprAdv F) (pk : PkSeed)
    (x : A.State × SM_DT_DSPR_SourceFinalValidity.State Tweak M) :
    OracleComp (unifSpec + hS St Blk) Bool := do
  let (j, b) ← A.guess x.1 pk
  match x.2.challenges[j]? with
  | none => return false
  | some (t, m) =>
      if x.2.valid then do
        let sp ← spPub F pk t m
        return win sp b
      else return false

/-- Winning condition of `experiment`: the guess equals the second-preimage bit. -/
def winS (sp b : Bool) : Bool := decide (sp = true ↔ b = true)

/-- Winning condition of `spExperiment`: the target has a second preimage. -/
def winSP (sp _b : Bool) : Bool := sp

end Monadic

end Ideal
