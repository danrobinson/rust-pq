import Ideal.Games.TcrMultiBasic
import VCVio.OracleComp.SimSemantics.StateT.UntilBad

/-!
# Multi-block SM-TCR in the ideal-compression model: the symbolic phase one (definitions)

* `fuse inner`: a game handler over the keyed-chain interface fused with `chainRO` into one
  handler on (game state, joint cache).
* `symD F`: the deferred symbolic game, phase one of the single-block family `F.single`
  (a target is answered by its private-row cell alone).
* `symE F L`: the eager symbolic game: `symD` which in addition draws, at every accepted
  challenge query, `L` hidden chaining values and appends them to a store it never reads.
* `fbuild F`: the state of the real phase one that a state of `symE` stands for.
* `fillS L`: draw the hidden values of all targets of a state of `symD`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y ι : Type}

section

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-- A game handler over the keyed-chain interface fused with `chainRO`. -/
noncomputable def fuse {ι₀ : Type} {spec₀ : OracleSpec ι₀} {σ : Type}
    (inner : QueryImpl spec₀ (StateT σ (OracleComp (gS St Blk)))) :
    QueryImpl spec₀ (StateT (σ × Cache St Blk) ProbComp) :=
  fun t => StateT.mk fun p =>
    (fun y => (y.1.1, (y.1.2, y.2))) <$> (simulateQ chainRO ((inner t).run p.1)).run p.2

variable [DecidableEq Tweak]

/-- The real phase one as a handler on (game state, cache). -/
noncomputable def conG (F : THFam St Blk PkSeed Tweak M Y ι) :
    QueryImpl F.advS (StateT (SM_DT_TCR_State Tweak M × Cache St Blk) ProbComp) :=
  fuse (tcrGameM F)

/-- The deferred symbolic phase one: the single-block game. -/
noncomputable def symD (F : THFam St Blk PkSeed Tweak M Y ι) :
    QueryImpl F.advS (StateT (SM_DT_TCR_State Tweak M × Cache St Blk) ProbComp) :=
  fuse (tcrGameM F.single)

/-- The query is a challenge query that the game accepts from the state `s`. -/
def accepts (F : THFam St Blk PkSeed Tweak M Y ι) (t : F.advS.Domain)
    (s : SM_DT_TCR_State Tweak M) : Prop :=
  match t with
  | .inr (.inr (.inl tm)) => ¬ (F.numTargets ≤ s.1.length ∨ ¬ TweakFresh Prod.fst s.1 s.2 tm.1)
  | _ => False

instance (F : THFam St Blk PkSeed Tweak M Y ι) (t : F.advS.Domain)
    (s : SM_DT_TCR_State Tweak M) : Decidable (accepts F t s) := by
  unfold accepts
  split <;> infer_instance

/-- The eager symbolic phase one: at an accepted challenge query, `L` hidden values are drawn
(before the step of `symD`) and appended to the store. -/
noncomputable def symE (F : THFam St Blk PkSeed Tweak M Y ι) (L : ℕ) :
    QueryImpl F.advS
      (StateT ((SM_DT_TCR_State Tweak M × Cache St Blk) × List (List St)) ProbComp) :=
  fun t => StateT.mk fun S =>
    if accepts F t S.1.1 then
      drawV L >>= fun h => (fun z => (z.1, (z.2, S.2 ++ [h]))) <$> (symD F t).run S.1
    else (fun z => (z.1, (z.2, S.2))) <$> (symD F t).run S.1

/-- The state of the real phase one that a symbolic state stands for. -/
def fbuild (F : THFam St Blk PkSeed Tweak M Y ι)
    (S : (SM_DT_TCR_State Tweak M × Cache St Blk) × List (List St)) :
    SM_DT_TCR_State Tweak M × Cache St Blk :=
  (S.1.1, ofLook (build F (look S.1.2) S.1.1.1 S.2))

/-- Draw the hidden values of all targets. -/
noncomputable def fillS (L : ℕ) (p : SM_DT_TCR_State Tweak M × Cache St Blk) :
    ProbComp ((SM_DT_TCR_State Tweak M × Cache St Blk) × List (List St)) :=
  (fun hs => (p, hs)) <$> drawN L p.1.1.length

end

end Ideal
