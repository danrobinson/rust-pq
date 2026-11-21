/-
Work package OPEN, item R4 for the FORS adversaries `toDspr (Lazy.bOpenPreS A)` and
`toTcr (Lazy.bOpenPreS A)`: the first phase (`choose`, everything run before `PK.seed` is
revealed, and the `State` type) does no hashing of its own.

* `forsPhase1 vp prims` : ONE explicit program over the selection-phase interface of the game
  (`ForsP1Spec prims` = private coins + challenge oracle + the (empty) collection oracle; there is
  no hash oracle in it).  Its definition mentions `prims` only through the carrier types
  `prims.PkSeed`, `prims.AdrsKey`, `prims.Y` and the address encoding `prims.adrsToKey`
  (all components of `prims.core`); neither `Thash`, `Hmsg`, `PRF`, `PRFmsg` nor the forger occur.
* `toDspr_choose_eq`, `toTcr_choose_eq` : the `choose` field of both adversaries IS that program
  (for every forger `A`).
* `Open.forsDspr_phase1_hashfree`, `Open.forsTcr_phase1_hashfree` : for all replacements `T`, `H`
  of `Thash`, `Hmsg`, the `choose` of the adversary built over `withTH prims T H` from
  `castForger T H A` equals the `choose` of the adversary built over `prims` from `A` (plain `=`;
  the `State` types coincide by `rfl`: `forsDspr_state_hashfree`, `forsTcr_state_hashfree`).
* `forsDspr_phase1_q1`, `forsTcr_phase1_q1` : the `q₁ = 0` corollary in existential form.
* `forsDspr_phase1_withHash`, `forsTcr_phase1_withHash` : the same with all FOUR hash components
  replaced (`withHash prims f`), for an arbitrary forger of the modified scheme.
-/
import Reduction.Open.WithHash
import Reduction.ForsTightFinal
import Reduction.Lazy.OpenPreSparse

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Open

open TweakableHash

set_option linter.unusedSectionVars false

/-! ## Generic, hash-free ingredients (carrier types only) -/

section Generic

variable {PkSeed Tweak M Y : Type}

/-- Commitment-phase interface of a stand-alone OpenPRE adversary: private coins and the
collection oracle of the EMPTY collection (unqueryable). -/
abbrev PickSpec (PkSeed Tweak Y : Type) :=
  unifSpec + SourceFinalValidity.collectionSpec (TweakableHashCollection.empty PkSeed Tweak Y)

/-- Selection-phase interface of the stand-alone SM-DT-DSPR / SM-DT-TCR game: private coins, the
game's challenge oracle (targets `(tweak, input)`), the empty collection oracle.  No hash oracle. -/
abbrev SelSpec (PkSeed Tweak M Y : Type) :=
  unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
    SourceFinalValidity.collectionSpec (TweakableHashCollection.empty PkSeed Tweak Y))

/-- `liftPick` of VCVio for a stand-alone problem, written without the problem (no hash). -/
def liftPickHF : QueryImpl (PickSpec PkSeed Tweak Y) (OracleComp (SelSpec PkSeed Tweak M Y))
  | .inl q => liftM ((SelSpec PkSeed Tweak M Y).query (.inl q))
  | .inr q => liftM ((SelSpec PkSeed Tweak M Y).query (.inr (.inr q)))

/-- `reductionInitialize` of VCVio for a stand-alone problem, written without the problem: one
sample of `gen` per tweak, submitted with its tweak as a target to the challenge oracle. -/
noncomputable def initHF (gen : ProbComp M) :
    List Tweak → OracleComp (SelSpec PkSeed Tweak M Y) (List (Tweak × M) × List Y)
  | [] => pure ([], [])
  | t :: ts => do
      let x ← liftM gen
      let y ← liftM ((SelSpec PkSeed Tweak M Y).query (.inr (.inl (t, x))))
      let (targets, ys) ← initHF gen ts
      return ((t, x) :: targets, y :: ys)

theorem liftPick_standalone (th : TweakableHash PkSeed Tweak M Y) (gen : ProbComp M) (n : ℕ) :
    SM_DT_OpenPRE_SourceFinalValidity.liftPick
      (SM_DT_OpenPRE_SourceFinalValidity.Problem.standalone th gen n) =
      (liftPickHF : QueryImpl (PickSpec PkSeed Tweak Y) (OracleComp (SelSpec PkSeed Tweak M Y))) := by
  funext q
  cases q <;> rfl

theorem reductionInitialize_standalone (th : TweakableHash PkSeed Tweak M Y) (gen : ProbComp M)
    (n : ℕ) (l : List Tweak) :
    SM_DT_OpenPRE_SourceFinalValidity.reductionInitialize
      (SM_DT_OpenPRE_SourceFinalValidity.Problem.standalone th gen n) l =
      (initHF gen l : OracleComp (SelSpec PkSeed Tweak M Y) (List (Tweak × M) × List Y)) := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    unfold SM_DT_OpenPRE_SourceFinalValidity.reductionInitialize initHF
    rw [ih]
    rfl

end Generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## The first phase as one explicit program -/

/-- Oracle interface of the first phase of `toDspr B` / `toTcr B`: the selection-phase interface
of the game.  It contains no hash oracle. -/
abbrev ForsP1Spec (prims : Primitives vp.params) :=
  SelSpec prims.PkSeed prims.AdrsKey prims.Y prims.Y

/-- State handed from the first to the second phase: the sparse secret table, the sampled
targets `(tweak, input)`, the images returned by the challenge oracle. -/
abbrev ForsP1State (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y

variable (vp prims) in
/-- **The first phase of `toDspr (Lazy.bOpenPreS A)` and of `toTcr (Lazy.bOpenPreS A)`**:
sample the WOTS+ cells of the table; commit to the FORS leaf tweaks; for each of the first
`openPreTargets vp` of them sample a uniform input and register `(tweak, input)` at the game's
challenge oracle; keep table, targets and returned images.  No component of `prims` other than
carrier types and `adrsToKey` occurs; the forger does not occur. -/
noncomputable def forsPhase1 : OracleComp (ForsP1Spec prims) (ForsP1State vp prims) :=
  simulateQ (liftPickHF : QueryImpl (PickSpec prims.PkSeed prims.AdrsKey prims.Y)
      (OracleComp (ForsP1Spec prims)))
      ((liftM ((fun xs => Tables.updateList (fun _ => default) (Lazy.wotsSkIdx vp) xs) <$>
          Tables.sampleList prims.Y (Lazy.wotsSkIdx vp).length) :
        OracleComp (PickSpec prims.PkSeed prims.AdrsKey prims.Y) (SecretTable vp prims)) >>=
        fun tbl => pure (tbl, forsLeafKeys vp prims)) >>= fun w =>
    initHF ($ᵗ prims.Y) (w.2.take (openPreTargets vp)) >>= fun r => pure (w.1, r.1, r.2)

/-- `State` of `toDspr (Lazy.bOpenPreS A)`. -/
theorem toDspr_state_eq (A : Forger vp prims optRand pkSeedDist) :
    (toDspr (Lazy.bOpenPreS A)).State = ForsP1State vp prims := rfl

/-- `State` of `toTcr (Lazy.bOpenPreS A)`. -/
theorem toTcr_state_eq (A : Forger vp prims optRand pkSeedDist) :
    (toTcr (Lazy.bOpenPreS A)).State = ForsP1State vp prims := rfl

private theorem choose_aux (pkSeedDist : ProbComp prims.PkSeed) :
    (simulateQ (SM_DT_OpenPRE_SourceFinalValidity.liftPick (forsOpenPreProblem vp prims pkSeedDist))
      ((liftM ((fun xs => Tables.updateList (fun _ => default) (Lazy.wotsSkIdx vp) xs) <$>
          Tables.sampleList prims.Y (Lazy.wotsSkIdx vp).length) :
        OracleComp (PickSpec prims.PkSeed prims.AdrsKey prims.Y) (SecretTable vp prims)) >>=
        fun tbl => pure (tbl, forsLeafKeys vp prims)) >>= fun w =>
    SM_DT_OpenPRE_SourceFinalValidity.reductionInitialize (forsOpenPreProblem vp prims pkSeedDist)
      (w.2.take (openPreTargets vp)) >>= fun r => pure (w.1, r.1, r.2) :
        OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) = forsPhase1 vp prims := by
  unfold forsPhase1 forsOpenPreProblem
  rw [liftPick_standalone]
  refine bind_congr fun w => ?_
  rw [reductionInitialize_standalone]

/-- **First phase of `toDspr (Lazy.bOpenPreS A)`** is the program `forsPhase1 vp prims`. -/
theorem toDspr_choose_eq (A : Forger vp prims optRand pkSeedDist) :
    ((toDspr (Lazy.bOpenPreS A)).choose : OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) =
      forsPhase1 vp prims :=
  Eq.trans rfl (choose_aux pkSeedDist)

/-- **First phase of `toTcr (Lazy.bOpenPreS A)`** is the program `forsPhase1 vp prims`. -/
theorem toTcr_choose_eq (A : Forger vp prims optRand pkSeedDist) :
    ((toTcr (Lazy.bOpenPreS A)).choose : OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) =
      forsPhase1 vp prims :=
  Eq.trans rfl (choose_aux pkSeedDist)

/-! ## Independence of `Thash`, `Hmsg` -/

section TH

variable (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
  (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)

/-- The program `forsPhase1` does not depend on `Thash`, `Hmsg`. -/
theorem forsPhase1_withTH :
    (forsPhase1 vp (withTH prims T H) : OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) =
      forsPhase1 vp prims := rfl

/-- The `State` type of the DSPR adversary does not depend on `Thash`, `Hmsg`. -/
theorem forsDspr_state_hashfree (A : Forger vp prims optRand pkSeedDist) :
    (toDspr (Lazy.bOpenPreS (castForger T H A))).State = (toDspr (Lazy.bOpenPreS A)).State := rfl

/-- The `State` type of the TCR adversary does not depend on `Thash`, `Hmsg`. -/
theorem forsTcr_state_hashfree (A : Forger vp prims optRand pkSeedDist) :
    (toTcr (Lazy.bOpenPreS (castForger T H A))).State = (toTcr (Lazy.bOpenPreS A)).State := rfl

/-- **R4 for `toDspr (Lazy.bOpenPreS A)`.**  For all replacements `T`, `H` of `Thash`, `Hmsg`:
the first phase of the adversary built over `withTH prims T H` from the same forger is EQUAL to
the first phase of the adversary built over `prims`.  (The ascription only names the common type;
both `choose` fields have it by `rfl`.) -/
theorem forsDspr_phase1_hashfree (A : Forger vp prims optRand pkSeedDist) :
    ((toDspr (Lazy.bOpenPreS (castForger T H A))).choose :
        OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) =
      (toDspr (Lazy.bOpenPreS A)).choose :=
  (toDspr_choose_eq (castForger T H A)).trans
    ((forsPhase1_withTH T H).trans (toDspr_choose_eq A).symm)

/-- **R4 for `toTcr (Lazy.bOpenPreS A)`.** -/
theorem forsTcr_phase1_hashfree (A : Forger vp prims optRand pkSeedDist) :
    ((toTcr (Lazy.bOpenPreS (castForger T H A))).choose :
        OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) =
      (toTcr (Lazy.bOpenPreS A)).choose :=
  (toTcr_choose_eq (castForger T H A)).trans
    ((forsPhase1_withTH T H).trans (toTcr_choose_eq A).symm)

/-- The commitment phase of the underlying OpenPRE adversary, likewise. -/
theorem bOpenPreS_pick_hashfree (A : Forger vp prims optRand pkSeedDist) :
    ((Lazy.bOpenPreS (castForger T H A)).pick :
        OracleComp (PickSpec prims.PkSeed prims.AdrsKey prims.Y)
          (SecretTable vp prims × List prims.AdrsKey)) =
      (Lazy.bOpenPreS A).pick := by
  rw [Lazy.bOpenPreS_pick A]
  exact Lazy.bOpenPreS_pick (castForger T H A)

end TH

/-- **`q₁ = 0` for `toDspr (Lazy.bOpenPreS ·)`.**  There is ONE program over the selection-phase
interface of the game (coins, challenge oracle, empty collection oracle; no hash oracle) which is
the first phase of the adversary for EVERY choice of `Thash`, `Hmsg` and every forger: the first
phase makes no hash evaluation of its own, the only hashing in it is the game's answer to the
registered targets. -/
theorem forsDspr_phase1_q1 :
    ∃ P : OracleComp (ForsP1Spec prims) (ForsP1State vp prims),
      ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
        (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
        (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
        (pkSeedDist : ProbComp prims.PkSeed)
        (A : Forger vp (withTH prims T H) optRand pkSeedDist),
        (toDspr (Lazy.bOpenPreS A)).choose = P :=
  ⟨forsPhase1 vp prims, fun T H _ _ A => (toDspr_choose_eq A).trans (forsPhase1_withTH T H)⟩

/-- **`q₁ = 0` for `toTcr (Lazy.bOpenPreS ·)`.** -/
theorem forsTcr_phase1_q1 :
    ∃ P : OracleComp (ForsP1Spec prims) (ForsP1State vp prims),
      ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
        (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
        (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
        (pkSeedDist : ProbComp prims.PkSeed)
        (A : Forger vp (withTH prims T H) optRand pkSeedDist),
        (toTcr (Lazy.bOpenPreS A)).choose = P :=
  ⟨forsPhase1 vp prims, fun T H _ _ A => (toTcr_choose_eq A).trans (forsPhase1_withTH T H)⟩

/-! ## Optional level: all four hash components replaced -/

section Four

variable (f : HashFns prims)

/-- The program `forsPhase1` does not depend on any of the four hash components. -/
theorem forsPhase1_withHash :
    (forsPhase1 vp (withHash prims f) : OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) =
      forsPhase1 vp prims := rfl

/-- **R4, four components, DSPR.**  For every forger `A'` of the scheme over `withHash prims f`
(no transport of a forger of `prims` is needed: the first phase does not depend on the forger),
the first phase of its DSPR adversary is the program `forsPhase1 vp prims`, i.e. the first phase
of the adversary over `prims` for any forger. -/
theorem forsDspr_phase1_withHash
    {optRand' : PublicKeyCore (withHash prims f).core → ProbComp prims.Y}
    (A' : Forger vp (withHash prims f) optRand' pkSeedDist)
    (A : Forger vp prims optRand pkSeedDist) :
    ((toDspr (Lazy.bOpenPreS A')).choose :
        OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) =
      (toDspr (Lazy.bOpenPreS A)).choose :=
  (toDspr_choose_eq A').trans ((forsPhase1_withHash f).trans (toDspr_choose_eq A).symm)

/-- **R4, four components, TCR.** -/
theorem forsTcr_phase1_withHash
    {optRand' : PublicKeyCore (withHash prims f).core → ProbComp prims.Y}
    (A' : Forger vp (withHash prims f) optRand' pkSeedDist)
    (A : Forger vp prims optRand pkSeedDist) :
    ((toTcr (Lazy.bOpenPreS A')).choose :
        OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) =
      (toTcr (Lazy.bOpenPreS A)).choose :=
  (toTcr_choose_eq A').trans ((forsPhase1_withHash f).trans (toTcr_choose_eq A).symm)

end Four

end Open
end Reduction

#print axioms Reduction.Open.forsDspr_phase1_hashfree
#print axioms Reduction.Open.forsTcr_phase1_hashfree
#print axioms Reduction.Open.forsDspr_phase1_q1
#print axioms Reduction.Open.forsTcr_phase1_q1
#print axioms Reduction.Open.forsDspr_phase1_withHash
#print axioms Reduction.Open.forsTcr_phase1_withHash
