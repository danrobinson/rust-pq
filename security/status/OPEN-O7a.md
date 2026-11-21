# OPEN-O7a — R4 (first phases do no hashing) for the FORS and class-TCR adversaries
Files (new, compile clean, oleans written, no `sorry`): `Reduction/Open/Phase1Fors.lean`,
`Reduction/Open/Phase1Tcr.lean`. Result: NO first phase depends on `Thash`/`Hmsg` (nor on
`PRF`/`PRFmsg`, nor on the forger). Mandatory AND optional level done for all three adversaries.
Method: each first phase is shown EQUAL to one explicit program whose definition mentions `prims` only via
carrier types / `adrsToKey` / `prims.core`; independence is then `rfl` on that program.
The VCVio/TcrSplit helpers take the problem (hence the hash) as an unused argument; hash-free
copies over carrier types only: `liftPickHF`, `initHF gen`, `routeStepHF P N`, `routeHF P N`
(lemmas `liftPick_standalone`, `reductionInitialize_standalone`, `route_eq_routeHF`, `restrict_choose`).

## FORS (`Phase1Fors.lean`), namespace `Reduction.Open`
```
abbrev SelSpec (PkSeed Tweak M Y) := unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y
    + SourceFinalValidity.collectionSpec (TweakableHashCollection.empty PkSeed Tweak Y))
abbrev ForsP1Spec (prims) := SelSpec prims.PkSeed prims.AdrsKey prims.Y prims.Y
abbrev ForsP1State (vp) (prims) : Type := SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y
noncomputable def forsPhase1 (vp) (prims) : OracleComp (ForsP1Spec prims) (ForsP1State vp prims)
theorem toDspr_choose_eq / toTcr_choose_eq (A : Forger vp prims optRand pkSeedDist) :
    ((toDspr (Lazy.bOpenPreS A)).choose : OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) = forsPhase1 vp prims
theorem forsPhase1_withTH (T H) / forsPhase1_withHash (f) :
    (forsPhase1 vp (withTH prims T H) : …) = forsPhase1 vp prims   -- rfl (resp. withHash prims f)
theorem forsDspr_state_hashfree / forsTcr_state_hashfree (T H) (A) :
    (toDspr (Lazy.bOpenPreS (castForger T H A))).State = (toDspr (Lazy.bOpenPreS A)).State   -- rfl (resp. toTcr)
theorem forsDspr_phase1_hashfree (T H) (A : Forger vp prims optRand pkSeedDist) :
    ((toDspr (Lazy.bOpenPreS (castForger T H A))).choose :
        OracleComp (ForsP1Spec prims) (ForsP1State vp prims)) = (toDspr (Lazy.bOpenPreS A)).choose
theorem forsTcr_phase1_hashfree  (T H) (A) : (same with toTcr); bOpenPreS_pick_hashfree (same for `.pick`)
theorem forsDspr_phase1_q1 : ∃ P : OracleComp (ForsP1Spec prims) (ForsP1State vp prims), ∀ T H optRand
    pkSeedDist (A : Forger vp (withTH prims T H) optRand pkSeedDist), (toDspr (Lazy.bOpenPreS A)).choose = P
-- forsTcr_phase1_q1: same with toTcr.  Optional level (all four components; `f : HashFns prims`)
theorem forsDspr_phase1_withHash (f) {optRand' : PublicKeyCore (withHash prims f).core → ProbComp prims.Y}
    (A' : Forger vp (withHash prims f) optRand' pkSeedDist) (A : Forger vp prims optRand pkSeedDist) :
    ((toDspr (Lazy.bOpenPreS A')).choose : …) = (toDspr (Lazy.bOpenPreS A)).choose
-- forsTcr_phase1_withHash: same with toTcr
```
## Class TCR (`Phase1Tcr.lean`), namespace `Reduction.Open`
```
abbrev Spec1 (Tweak Y) (P : List Y → Prop) := unifSpec + (SM_DT_TCR_challengeSpec Tweak {xs : List Y // P xs} Y
    + (((_ : Unit) × Tweak × List Y) →ₒ Option Y))
abbrev TcrP1Spec (prims) (n : ℕ) := Spec1 prims.AdrsKey prims.Y (fun xs => xs.length = n)
abbrev TcrP1State (vp) (prims) : Type := SecretTable vp prims × List (prims.AdrsKey × List prims.Y)
noncomputable def tcrChooseHF (vp) (prims) : OracleComp (Spec0 prims.PkSeed prims.AdrsKey prims.Y) (SecretTable vp prims)
noncomputable def tcrPhase1 (vp) (prims) (n : ℕ) : OracleComp (TcrP1Spec prims n) (TcrP1State vp prims) :=
  (simulateQ (routeHF (fun xs : List prims.Y => xs.length = n) (tcrTargets vp)) (tcrChooseHF vp prims)).run []
theorem bTcrS_choose_eq (A) : ((Lazy.bTcrS A).choose : …) = tcrChooseHF vp prims                 -- rfl
theorem bTcrArM_choose_eq (n) (A) : ((bTcrArM n A).choose : …) = tcrPhase1 vp prims n
theorem tcrPhase1_withTH (T H) (n) / tcrPhase1_withHash (f) (n) :
    (tcrPhase1 vp (withTH prims T H) n : …) = tcrPhase1 vp prims n   -- rfl (resp. withHash prims f)
theorem tcrM_state_hashfree (T H) (n) (A) : (bTcrArM n (castForger T H A)).State = (bTcrArM n A).State  -- rfl
theorem tcrM_phase1_hashfree (T H) (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    ((bTcrArM n (castForger T H A)).choose : OracleComp (TcrP1Spec prims n) (TcrP1State vp prims)) = (bTcrArM n A).choose
theorem tcrM_phase1_q1 (n) : ∃ P : OracleComp (TcrP1Spec prims n) (TcrP1State vp prims),
    ∀ T H optRand pkSeedDist (A : Forger vp (withTH prims T H) optRand pkSeedDist), (bTcrArM n A).choose = P
theorem tcrM_phase1_withHash (f) (n) {optRand'} (A' : Forger vp (withHash prims f) optRand' pkSeedDist)
    (A : Forger vp prims optRand pkSeedDist) : ((bTcrArM n A').choose : …) = (bTcrArM n A).choose
```
## Deviations / remarks (read these)
1. Plain `=`, no `HEq`. The left side carries a type ascription naming the common, visibly
   hash-free type (`OracleComp (ForsP1Spec prims) (ForsP1State vp prims)` etc.). Both `choose`
   fields have that type by `rfl`; without it the elaborator unifies the two adversaries
   structurally (incl. second phases) and times out.
2. Optional level: stated for an ARBITRARY forger `A'` of the modified scheme instead of a
   transported `A` (first phases do not depend on the forger, so no transport of `Forger` /
   `optRand` along `withHash` is needed). This is stronger than a transported statement.
3. `q₁ = 0` form (`*_phase1_q1`): one program `P` over the game's selection-phase oracle spec
   (coins + challenge oracle + collection oracle; no hash oracle in the spec) equals the first phase
   for every `T`, `H`, `optRand`, `pkSeedDist`, forger; a program-level statement, not a count in
   the `Lazy.RSpec`/`IsQueryBoundP` model.
4. Class-TCR caveat: the first phase of `bTcrArM n A` DOES use the game's COLLECTION oracle, which
   returns `Thash` values at the hidden seed for the non-class arities (`tcrTargets − arityTargets`
   queries, `bTcrArM_phase1`), besides `arityTargets vp n` challenge targets. That is hashing by
   the game (part of the SM-TCR-with-collection assumption), not by the adversary; whether the
   quantum side counts collection queries as (classical) hash queries of phase 1 is its decision.
   FORS: the collection is empty (`Empty` index), only challenge targets (≤ `openPreTargets vp`).
5. No numerals are involved (no 128s content in this item).
Axioms: `forsDspr_phase1_hashfree`, `forsTcr_phase1_hashfree`, `forsDspr_phase1_q1`, `forsTcr_phase1_q1`,
`forsDspr_phase1_withHash`, `forsTcr_phase1_withHash`, `tcrM_phase1_hashfree`, `tcrM_phase1_q1`,
`tcrM_phase1_withHash`: each `[propext, Classical.choice, Quot.sound]`.
Not done: nothing of the task is open. Not attempted: a restatement in the `Lazy.OSpec` counting
model (first phase as an `OSpec` program with 0 `.hash`-kind queries).
