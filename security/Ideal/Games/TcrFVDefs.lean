import Ideal.Games.TcrDefs
import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity

/-!
# Source-final-validity SM-TCR (stand-alone) in the ideal-compression model: definitions

The game is VCVio's `TweakableHash.SM_DT_TCR_SourceFinalValidity` at the *stand-alone* problem
(empty collection): every challenge query is answered and recorded, and the cap and the
distinctness of the target tweaks are checked by the sticky bit `valid` in the winning condition.

The hash family is a `THFam` with index type `Empty`; only its fields `IV`, `sb`, `seedGen`,
`tch`, `out`, `numTargets` are used (`Msg`, `cch`, `cout` are functions on `Empty`).
`THFam.fvProb F g` is VCVio's stand-alone problem at the table `g`; an ideal-model adversary
(`FvAdv`) has, in addition to the oracles of the VCVio game, oracle access to the compression
function in both phases, and `FvAdv.inst A g` is the VCVio adversary it becomes once the table is
fixed.  The ideal-model advantage `tcrFVAdvantage` is the VCVio advantage averaged over a uniform
table.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y : Type}

namespace THFam

variable (F : THFam St Blk PkSeed Tweak M Y Empty)

/-- The attacked member at the table `g`, as a VCVio tweakable hash. -/
def fvTh (g : CF St Blk) : TweakableHash PkSeed Tweak M Y where
  seedGen := F.seedGen
  eval := F.evalT g

/-- VCVio's stand-alone source-final-validity SM-TCR problem at the table `g`. -/
def fvProb (g : CF St Blk) : SM_DT_TCR_SourceFinalValidity.Problem Empty PkSeed Tweak M Y :=
  .standalone (F.fvTh g) F.numTargets

/-- The (uninhabited) collection-oracle interface of the stand-alone game. -/
abbrev fvCollS (PkSeed Tweak Y : Type) :
    OracleSpec ((i : Empty) × Tweak × (TweakableHashCollection.empty PkSeed Tweak Y).Msg i) :=
  SourceFinalValidity.collectionSpec (TweakableHashCollection.empty PkSeed Tweak Y)

/-- Oracle interface of an ideal-model adversary's first phase: uniform sampling, the compression
function, the challenge oracle, the (uninhabited) collection oracle. -/
abbrev fvAdvS (_F : THFam St Blk PkSeed Tweak M Y Empty) :=
  unifSpec + (hS St Blk +
    (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y + fvCollS PkSeed Tweak Y))

/-- A compression query of the first phase. -/
def fvIsH : F.fvAdvS.Domain → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A challenge query. -/
def fvIsChal : F.fvAdvS.Domain → Bool
  | .inr (.inr (.inl _)) => true
  | _ => false

end THFam

/-- A source-final-validity SM-TCR adversary in the ideal-compression model: VCVio's
`SM_DT_TCR_SourceFinalValidity.Adversary` (stand-alone problem) with oracle access to the
compression function in both phases. -/
structure FvAdv (F : THFam St Blk PkSeed Tweak M Y Empty) where
  State : Type
  choose : OracleComp F.fvAdvS State
  forge : State → PkSeed → OracleComp (unifSpec + hS St Blk) (ℕ × M)

namespace FvAdv

variable {F : THFam St Blk PkSeed Tweak M Y Empty}

/-- The VCVio adversary obtained by fixing the compression table. -/
def inst (A : FvAdv F) (g : CF St Blk) : SM_DT_TCR_SourceFinalValidity.Adversary (F.fvProb g) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  forge := fun st pk => simulateQ (instImpl₀ g) (A.forge st pk)

/-- The first phase makes at most `q` compression queries. -/
def ChooseBound (A : FvAdv F) (q : ℕ) : Prop :=
  IsQueryBoundP A.choose (fun i => F.fvIsH i = true) q

/-- The first phase makes at most `q` challenge queries. -/
def ChalBound (A : FvAdv F) (q : ℕ) : Prop :=
  IsQueryBoundP A.choose (fun i => F.fvIsChal i = true) q

/-- The second phase makes at most `q` compression queries. -/
def ForgeBound (A : FvAdv F) (q : ℕ) : Prop :=
  ∀ st pk, IsQueryBoundP (A.forge st pk) (fun i => i.isRight = true) q

end FvAdv

/-- The probability that a game parametrised by the compression table returns `true` when the
table is uniformly random.  (A named wrapper: at concrete finite types the kernel cannot cheaply
unfold a definition whose body is literally `𝒟[…] {true}`, whereas unfolding to `idealAdv …` is
immediate and `idealAdv_def` is generic.) -/
noncomputable def idealAdv (St Blk : Type) [SampleableType (CF St Blk)]
    (game : CF St Blk → ProbComp Bool) : ℝ≥0∞ :=
  𝒟[do
    let g ← $ᵗ (CF St Blk)
    game g] {true}

theorem idealAdv_def [SampleableType (CF St Blk)] (game : CF St Blk → ProbComp Bool) :
    idealAdv St Blk game = 𝒟[$ᵗ (CF St Blk) >>= game] {true} := rfl

/-- Source-final-validity SM-TCR advantage in the ideal-compression model: VCVio's experiment for
the hash built from `g` and the adversary with its compression queries answered by `g`, with `g`
a uniformly random table. -/
noncomputable def tcrFVAdvantage [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y Empty) (A : FvAdv F) :
    ℝ≥0∞ :=
  𝒟[do
    let g ← $ᵗ (CF St Blk)
    SM_DT_TCR_SourceFinalValidity.experiment (A.inst g)] {true}

theorem tcrFVAdvantage_eq_idealAdv [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    [SampleableType (CF St Blk)] (F : THFam St Blk PkSeed Tweak M Y Empty) (A : FvAdv F) :
    tcrFVAdvantage F A =
      idealAdv St Blk fun g => SM_DT_TCR_SourceFinalValidity.experiment (A.inst g) := rfl

/-! ## The game as a program over the keyed-chain oracle -/

section Monadic

variable (F : THFam St Blk PkSeed Tweak M Y Empty)

/-- The oracles of the source-final-validity SM-TCR game with the hash evaluations issued as
chain queries and the adversary's compression queries forwarded.  State: VCVio's monitor state
(all recorded targets, collection tweaks (always empty here), sticky validity bit). -/
def fvGameM [DecidableEq Tweak] :
    QueryImpl F.fvAdvS
      (StateT (SM_DT_TCR_SourceFinalValidity.State Tweak M) (OracleComp (gS St Blk))) := fun
  | .inl n => liftM ((gS St Blk).query (.inl n))
  | .inr (.inl q) => liftM ((gS St Blk).query (.inr (.inl q)))
  | .inr (.inr (.inl tm)) => do
      let st ← get
      set (st.recordTarget F.numTargets Prod.fst tm)
      let c ← liftM ((gS St Blk).query (.inr (.inr (F.tch tm.1 tm.2))))
      return F.out c
  | .inr (.inr (.inr q)) => q.1.elim

variable {F}

/-- Phase one of the game as a program over the keyed-chain oracle. -/
def fvProg₁ [DecidableEq Tweak] (A : FvAdv F) :
    OracleComp (gS St Blk) (A.State × SM_DT_TCR_SourceFinalValidity.State Tweak M) :=
  (simulateQ (fvGameM F) A.choose).run .initial

/-- Phase two of the game (the adversary's second phase and the winning condition, including the
final validity bit) as a program making public compression queries. -/
def fvP₂ [DecidableEq M] [DecidableEq Y] (A : FvAdv F) (pk : PkSeed)
    (x : A.State × SM_DT_TCR_SourceFinalValidity.State Tweak M) :
    OracleComp (unifSpec + hS St Blk) Bool := do
  let (j, m) ← A.forge x.1 pk
  match x.2.challenges[j]? with
  | none => return false
  | some (t, mj) =>
      if x.2.valid then do
        let y ← evalPub F pk t m
        let y' ← evalPub F pk t mj
        return decide (m ≠ mj ∧ y = y')
      else return false

end Monadic

end Ideal
