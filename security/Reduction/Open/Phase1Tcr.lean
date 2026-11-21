/-
Work package OPEN, item R4 for the arity-class SM-TCR adversaries `bTcrArM n A`
(`Reduction/TcrMemo.lean`): the first phase (`choose`, everything run before `PK.seed` is
revealed, and the `State` type) does no hashing of its own.

* `tcrPhase1 vp prims n` : ONE explicit program over the selection-phase interface of the class
  game (`TcrP1Spec prims n` = private coins + challenge oracle for arity-`n` targets + the game's
  collection oracle).  Its definition mentions `prims` only through `prims.core` (carrier types,
  `adrsToKey`; the `…WithSecret` structure walk is parametrised by `prims.core` and receives every
  hash value from the game's oracles); `Thash`, `Hmsg` and the forger do not occur.
* `bTcrArM_choose_eq` : `(bTcrArM n A).choose` IS that program, for every forger `A`.
* `Open.tcrM_phase1_hashfree` : for all replacements `T`, `H` of `Thash`, `Hmsg`, the `choose` of
  the adversary built over `withTH prims T H` from `castForger T H A` equals the `choose` of the
  adversary built over `prims` from `A` (plain `=`; `State` coincides by `rfl`,
  `tcrM_state_hashfree`).
* `tcrM_phase1_q1` : the `q₁ = 0` corollary in existential form.
-/
import Reduction.Open.WithHash
import Reduction.TcrMemo

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Open

open TweakableHash

set_option linter.unusedSectionVars false

/-! ## Generic, hash-free form of the class router `TcrSplit.route` (carrier types only) -/

section Generic

variable {PkSeed Tweak Y : Type}

/-- Interface of the stand-alone all-arity game (`TcrSplit.spec₀`), written without the hash:
coins, challenge oracle on `(tweak, List Y)`, empty collection oracle. -/
abbrev Spec0 (PkSeed Tweak Y : Type) :=
  unifSpec + (SM_DT_TCR_challengeSpec Tweak (List Y) Y +
    collectionSpec (TweakableHashCollection.empty PkSeed Tweak Y))

/-- Interface of the class game (`TcrSplit.spec₁`), written without the hash: coins, challenge
oracle on `(tweak, message in class P)`, the game's collection oracle on `(tweak, List Y)`. -/
abbrev Spec1 (Tweak Y : Type) (P : List Y → Prop) :=
  unifSpec + (SM_DT_TCR_challengeSpec Tweak {xs : List Y // P xs} Y +
    (((_ : Unit) × Tweak × List Y) →ₒ Option Y))

variable [DecidableEq Tweak]

/-- `TcrSplit.routeStep` without its (unused) hash argument. -/
def routeStepHF (P : List Y → Prop) [DecidablePred P] (N : ℕ) :
    (q : (Spec0 PkSeed Tweak Y).Domain) → List (Tweak × List Y) →
      OracleComp (Spec1 Tweak Y P) ((Spec0 PkSeed Tweak Y).Range q × List (Tweak × List Y))
  | .inl q, L => (fun u => (u, L)) <$> liftM ((Spec1 Tweak Y P).query (.inl q))
  | .inr (.inl (t, xs)), L =>
      if N ≤ L.length ∨ t ∈ L.map Prod.fst then pure (none, L)
      else if h : P xs then
        (fun r => (r, L ++ [(t, xs)])) <$> liftM ((Spec1 Tweak Y P).query (.inr (.inl (t, ⟨xs, h⟩))))
      else
        (fun r => (r, L ++ [(t, xs)])) <$> liftM ((Spec1 Tweak Y P).query (.inr (.inr ⟨(), t, xs⟩)))
  | .inr (.inr q), _ => q.1.elim

/-- `TcrSplit.route` without its (unused) hash argument. -/
def routeHF (P : List Y → Prop) [DecidablePred P] (N : ℕ) :
    QueryImpl (Spec0 PkSeed Tweak Y)
      (StateT (List (Tweak × List Y)) (OracleComp (Spec1 Tweak Y P))) :=
  fun q => StateT.mk (routeStepHF P N q)

theorem route_eq_routeHF (th : TweakableHash PkSeed Tweak (List Y) Y) (P : List Y → Prop)
    [DecidablePred P] (N : ℕ) :
    TcrSplit.route th P N =
      (routeHF P N : QueryImpl (Spec0 PkSeed Tweak Y)
        (StateT (List (Tweak × List Y)) (OracleComp (Spec1 Tweak Y P)))) := by
  funext q
  rcases q with q | ⟨t, xs⟩ | q
  · rfl
  · rfl
  · exact q.1.elim

end Generic

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

-- as in `Reduction/TightCaps.lean`: never evaluate the caps during unification
attribute [local irreducible] arityTargets tcrTargets

/-! ## The first phase as one explicit program -/

/-- Oracle interface of the first phase of `bTcrArM n A`: the selection-phase interface of the
arity-`n` class game — private coins, the challenge oracle (targets `(tweak, xs)` with
`xs.length = n`), and the game's collection oracle (`(tweak, xs)` of the other arities).  Both
oracles are the GAME's; there is no further hash oracle. -/
abbrev TcrP1Spec (prims : Primitives vp.params) (n : ℕ) :=
  Spec1 prims.AdrsKey prims.Y (fun xs => xs.length = n)

/-- State handed from the first to the second phase: the sparse table and the list of the
`(tweak, input)` pairs of all hash calls of the key structure. -/
abbrev TcrP1State (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  SecretTable vp prims × List (prims.AdrsKey × List prims.Y)

variable (vp prims) in
/-- The first phase of `Lazy.bTcrS A` (stand-alone all-arity game), written out: sample the
sparse table, walk the key structure submitting every hash call `(tweak, xs)` as a target and
continuing with the returned value. -/
noncomputable def tcrChooseHF :
    OracleComp (Spec0 prims.PkSeed prims.AdrsKey prims.Y) (SecretTable vp prims) := do
  let tbl ← (monadLift (Lazy.sparseTable vp prims) :
    OracleComp (Spec0 prims.PkSeed prims.AdrsKey prims.Y) (SecretTable vp prims))
  structureVia (vp := vp) (prims := prims)
    (fun key xs => do
      let r ← ((Spec0 prims.PkSeed prims.AdrsKey prims.Y).query (Sum.inr (Sum.inl (key, xs))) :
        OracleComp (Spec0 prims.PkSeed prims.AdrsKey prims.Y) (Option prims.Y))
      pure (r.getD default))
    (fun a => pure (secretOf vp prims tbl a))
  return tbl

variable (vp prims) in
/-- **The first phase of `bTcrArM n A`**: the structure walk `tcrChooseHF`, with each hash call
routed to the class game (arity `n`: challenge oracle, other arities: collection oracle) and
recorded in the list `L`.  Neither `Thash`, `Hmsg` nor the forger occur. -/
noncomputable def tcrPhase1 (n : ℕ) : OracleComp (TcrP1Spec prims n) (TcrP1State vp prims) :=
  (simulateQ (routeHF (fun xs : List prims.Y => xs.length = n) (tcrTargets vp))
    (tcrChooseHF vp prims)).run []

/-- `State` of `bTcrArM n A`. -/
theorem bTcrArM_state_eq (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    (bTcrArM n A).State = TcrP1State vp prims := rfl

private theorem choose_aux (pkSeedDist : ProbComp prims.PkSeed) (n : ℕ) :
    ((simulateQ (TcrSplit.route (thashList vp prims pkSeedDist) (fun xs => xs.length = n)
        (tcrTargets vp)) (tcrChooseHF vp prims)).run [] :
      OracleComp (TcrP1Spec prims n) (TcrP1State vp prims)) = tcrPhase1 vp prims n := by
  unfold tcrPhase1
  rw [route_eq_routeHF]
  rfl

/-- First phase of `Lazy.bTcrS A`, written out. -/
theorem bTcrS_choose_eq (A : Forger vp prims optRand pkSeedDist) :
    ((Lazy.bTcrS A).choose :
        OracleComp (Spec0 prims.PkSeed prims.AdrsKey prims.Y) (SecretTable vp prims)) =
      tcrChooseHF vp prims := rfl

/-- `choose` of `TcrSplit.restrict`, unfolded (generic). -/
theorem restrict_choose {PkSeed Tweak Y : Type} [DecidableEq Tweak]
    {th : TweakableHash PkSeed Tweak (List Y) Y} {N : ℕ} (P : List Y → Prop)
    [DecidablePred P] (d : {xs : List Y // P xs})
    (B : SM_DT_TCR_Adversary (SM_DT_TCR_Problem.standalone th N)) :
    (TcrSplit.restrict P d B).choose = (simulateQ (TcrSplit.route th P N) B.choose).run [] := rfl

private theorem choose_aux2 (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    ((simulateQ (TcrSplit.route (thashList vp prims pkSeedDist) (fun xs => xs.length = n)
        (tcrTargets vp)) (Lazy.bTcrS A).choose).run [] :
      OracleComp (TcrP1Spec prims n) (TcrP1State vp prims)) = tcrPhase1 vp prims n := by
  rw [bTcrS_choose_eq A]
  exact choose_aux pkSeedDist n

/-- **First phase of `bTcrArM n A`** is the program `tcrPhase1 vp prims n`. -/
theorem bTcrArM_choose_eq (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    ((bTcrArM n A).choose : OracleComp (TcrP1Spec prims n) (TcrP1State vp prims)) =
      tcrPhase1 vp prims n :=
  (bTcrArM_choose n A).trans
    ((restrict_choose (fun xs : List prims.Y => xs.length = n) (arityDefault prims n)
      (Lazy.bTcrS A)).trans (choose_aux2 n A))

/-! ## Independence of `Thash`, `Hmsg` -/

section TH

variable (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
  (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)

/-- The program `tcrPhase1` does not depend on `Thash`, `Hmsg`. -/
theorem tcrPhase1_withTH (n : ℕ) :
    (tcrPhase1 vp (withTH prims T H) n : OracleComp (TcrP1Spec prims n) (TcrP1State vp prims)) =
      tcrPhase1 vp prims n := rfl

/-- The `State` type does not depend on `Thash`, `Hmsg`. -/
theorem tcrM_state_hashfree (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    (bTcrArM n (castForger T H A)).State = (bTcrArM n A).State := rfl

/-- **R4 for `bTcrArM n A`.**  For all replacements `T`, `H` of `Thash`, `Hmsg`: the first phase
of the adversary built over `withTH prims T H` from the same forger is EQUAL to the first phase
of the adversary built over `prims`.  (The ascription only names the common type.) -/
theorem tcrM_phase1_hashfree (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    ((bTcrArM n (castForger T H A)).choose :
        OracleComp (TcrP1Spec prims n) (TcrP1State vp prims)) =
      (bTcrArM n A).choose :=
  (bTcrArM_choose_eq n (castForger T H A)).trans
    ((tcrPhase1_withTH T H n).trans (bTcrArM_choose_eq n A).symm)

end TH

/-- **`q₁ = 0` for `bTcrArM n ·`.**  There is ONE program over the selection-phase interface of
the class game (coins, challenge oracle, the game's collection oracle; no further hash oracle)
which is the first phase of the adversary for EVERY choice of `Thash`, `Hmsg` and every forger:
the first phase evaluates no hash function itself; all `tcrTargets vp` hash values it uses are
answers of the game's two oracles (`bTcrArM_phase1`: `arityTargets vp n` targets, the rest
collection queries). -/
theorem tcrM_phase1_q1 (n : ℕ) :
    ∃ P : OracleComp (TcrP1Spec prims n) (TcrP1State vp prims),
      ∀ (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
        (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
        (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
        (pkSeedDist : ProbComp prims.PkSeed)
        (A : Forger vp (withTH prims T H) optRand pkSeedDist),
        (bTcrArM n A).choose = P :=
  ⟨tcrPhase1 vp prims n, fun T H _ _ A => (bTcrArM_choose_eq n A).trans (tcrPhase1_withTH T H n)⟩

/-! ## Optional level: all four hash components replaced -/

section Four

variable (f : HashFns prims)

/-- The program `tcrPhase1` does not depend on any of the four hash components. -/
theorem tcrPhase1_withHash (n : ℕ) :
    (tcrPhase1 vp (withHash prims f) n : OracleComp (TcrP1Spec prims n) (TcrP1State vp prims)) =
      tcrPhase1 vp prims n := rfl

/-- **R4, four components.**  For every forger `A'` of the scheme over `withHash prims f` (no
transport of a forger is needed: the first phase does not depend on the forger), the first phase
of `bTcrArM n A'` is the first phase of `bTcrArM n A` over `prims`, for any forger `A`. -/
theorem tcrM_phase1_withHash (n : ℕ)
    {optRand' : PublicKeyCore (withHash prims f).core → ProbComp prims.Y}
    (A' : Forger vp (withHash prims f) optRand' pkSeedDist)
    (A : Forger vp prims optRand pkSeedDist) :
    ((bTcrArM n A').choose : OracleComp (TcrP1Spec prims n) (TcrP1State vp prims)) =
      (bTcrArM n A).choose :=
  (bTcrArM_choose_eq n A').trans ((tcrPhase1_withHash f n).trans (bTcrArM_choose_eq n A).symm)

end Four

end Open
end Reduction

#print axioms Reduction.Open.tcrM_phase1_hashfree
#print axioms Reduction.Open.tcrM_phase1_q1
#print axioms Reduction.Open.tcrM_phase1_withHash
