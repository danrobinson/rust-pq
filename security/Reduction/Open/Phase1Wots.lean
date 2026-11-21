/-
Work package OPEN, item R4 for the WOTS adversaries: "first phases do no hashing of their own".

For every replacement `f : HashFns prims` of ALL FOUR hash components (`Thash`, `Hmsg`, `PRF`,
`PRFmsg`) and EVERY forger `A'` against the scheme over `withHash prims f`, the first-phase
program of `rUd/rPre/rTcr/rTcrT pkSeedDist (Lazy.bWotsS A')` (built over `withHash prims f`) is
EQUAL — a plain `=` of oracle programs over the game's own oracle interface — to the first-phase
program of the adversary built over `prims` from any forger `A`.  (`*_phase1_hashfree_all`.)
The mandatory `withTH`/`castForger` statements (`*_phase1_hashfree`) are the special cases.

The first phases are programs over `unifSpec + (challenge + collection)` only: that interface has
no hash oracle, and (`udSpec_eq`, `preSpec_eq`, `wtcrSpec_eq`) is a function of the carrier types
alone.  `*_phase1_q1_zero`: ONE program over that carrier-only interface is the first phase for
all hash functions and all forgers.
-/
import Reduction.Open.WithHash
import Reduction.TightCapsHeadline

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction
namespace Open

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable (f : HashFns prims)
variable {optRand' : PublicKeyCore (withHash prims f).core → ProbComp prims.Y}
  {pkSeedDist' : ProbComp prims.PkSeed}

/-! ## Carrier-only oracle interfaces of the three games -/

/-- Collection-oracle interface as a function of the carrier types only. -/
abbrev collSpecC (K Y : Type) : OracleSpec ((_ : Unit) × K × List Y) := _ →ₒ Option Y

/-- Interface of the SM-UD first phase: coins, challenge oracle, collection oracle. -/
abbrev udSpecC (K Y : Type) := unifSpec + (SM_DT_UD_challengeSpec K Y + collSpecC K Y)
/-- Interface of the SM-PRE first phase. -/
abbrev preSpecC (K Y : Type) := unifSpec + (SM_DT_PRE_challengeSpec K Y + collSpecC K Y)
/-- Interface of the SM-TCR first phase. -/
abbrev tcrSpecC (K Y : Type) := unifSpec + (SM_DT_TCR_challengeSpec K Y Y + collSpecC K Y)

theorem udSpec_eq : UdSpec (vp := vp) (prims := prims) pkSeedDist =
    udSpecC prims.AdrsKey prims.Y := rfl
theorem preSpec_eq : PreSpec (vp := vp) (prims := prims) pkSeedDist =
    preSpecC prims.AdrsKey prims.Y := rfl
theorem wtcrSpec_eq : WTcrSpec (vp := vp) (prims := prims) pkSeedDist =
    tcrSpecC prims.AdrsKey prims.Y := rfl

/-- State type of `Lazy.bWotsS A` (for every forger and every hash bundle). -/
abbrev WState (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y

/-- State type of `rUd/rPre/rTcr/rTcrT pkSeedDist (Lazy.bWotsS A)`. -/
abbrev RState (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  WState vp prims × List (WotsGame.Entry prims)

/-! ## The WOTS-game adversary `bWotsS` -/

theorem wColl_withHash :
    @wColl vp (withHash prims f) _ = @wColl vp prims _ := rfl

theorem topsAt_withHash (a : Adrs) (msg : WM prims prims.Y) :
    topsAt (prims := withHash prims f) a msg = topsAt a msg := by
  unfold topsAt
  refine bind_congr fun hist => ?_
  rcases h : List.find? (fun e : WotsGame.Entry prims => decide (e.1 = a)) hist with _ | e
  · refine bind_congr fun m => bind_congr fun r => ?_
    cases r with
    | none => rfl
    | some x => rfl
  · rfl

theorem msgAt_withHash (tbl : SecretTable vp prims) (l tree leaf : ℕ) :
    msgAt (prims := withHash prims f) tbl l tree leaf = msgAt tbl l tree leaf := by
  induction l generalizing tree leaf with
  | zero => rfl
  | succ l ih =>
    rw [msgAt, msgAt]
    simp only [ih, topsAt_withHash]
    rfl

theorem chooseBody_withHash (tbl : SecretTable vp prims) :
    chooseBody (prims := withHash prims f) tbl = chooseBody tbl := by
  unfold chooseBody
  simp only [msgAt_withHash, topsAt_withHash]

theorem sparseOn_withHash (is : List SecIdx) :
    Lazy.sparseOn vp (withHash prims f) is = Lazy.sparseOn vp prims is := rfl

/-- **R4, WOTS-game adversary, all four hash components replaced, any two forgers.** -/
theorem bWotsS_phase1_hashfree_all (A' : Forger vp (withHash prims f) optRand' pkSeedDist')
    (A : Forger vp prims optRand pkSeedDist) :
    @Eq (OracleComp (WSpec prims) (WState vp prims))
      (Lazy.bWotsS A').choose (Lazy.bWotsS A).choose := by
  unfold Lazy.bWotsS
  rw [Lazy.bWotsWith_choose_eq, Lazy.bWotsWith_choose_eq, sparseOn_withHash]
  simp only [chooseBody_withHash]
  rfl

/-! ## The simulator `simChoose` -/

theorem simChoose_withHash {ι : Type} {spec : OracleSpec ι} (S : Type)
    (c₁ c₂ : OracleComp (WSpec prims) S) (h : c₁ = c₂)
    (f₁ f₂ : S → prims.PkSeed → ProbComp (ℕ × prims.Y × WotsSig vp.params prims.core))
    (insts : List Adrs)
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y) :
    WotsGame.simChoose (prims := withHash prims f) ⟨S, c₁, f₁⟩ insts startVal chainHash coll =
      WotsGame.simChoose (prims := prims) ⟨S, c₂, f₂⟩ insts startVal chainHash coll := by
  subst h; rfl

theorem preStart_withHash :
    preStart (vp := vp) (prims := withHash prims f) pkSeedDist =
      preStart (vp := vp) (prims := prims) pkSeedDist := rfl
theorem preChainHash_withHash :
    preChainHash (vp := vp) (prims := withHash prims f) pkSeedDist =
      preChainHash (vp := vp) (prims := prims) pkSeedDist := rfl
theorem preColl_withHash :
    preColl (vp := vp) (prims := withHash prims f) pkSeedDist =
      preColl (vp := vp) (prims := prims) pkSeedDist := rfl
theorem tcrStart_withHash :
    tcrStart (vp := vp) (prims := withHash prims f) pkSeedDist =
      tcrStart (vp := vp) (prims := prims) pkSeedDist := rfl
theorem tcrChainHash_withHash :
    tcrChainHash (vp := vp) (prims := withHash prims f) pkSeedDist =
      tcrChainHash (vp := vp) (prims := prims) pkSeedDist := rfl
theorem wtcrColl_withHash :
    wtcrColl (vp := vp) (prims := withHash prims f) pkSeedDist =
      wtcrColl (vp := vp) (prims := prims) pkSeedDist := rfl
theorem udChainHash_withHash :
    udChainHash (vp := vp) (prims := withHash prims f) pkSeedDist =
      udChainHash (vp := vp) (prims := prims) pkSeedDist := rfl
theorem udColl_withHash :
    udColl (vp := vp) (prims := withHash prims f) pkSeedDist =
      udColl (vp := vp) (prims := prims) pkSeedDist := rfl
theorem udStart_withHash (k : ℕ) :
    udStart (vp := vp) (prims := withHash prims f) pkSeedDist k =
      udStart (vp := vp) (prims := prims) pkSeedDist k := rfl

/-! ## R4 with all four hash components replaced (optional level) -/

/-- **R4, SM-PRE adversary.** -/
theorem wotsPre_phase1_hashfree_all (A' : Forger vp (withHash prims f) optRand' pkSeedDist')
    (A : Forger vp prims optRand pkSeedDist) :
    @Eq (OracleComp (preSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rPre (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).choose
      (rPre pkSeedDist (Lazy.bWotsS A)).choose := by
  unfold rPre
  simp only [preStart_withHash, preChainHash_withHash, preColl_withHash]
  exact simChoose_withHash f _ _ _ (bWotsS_phase1_hashfree_all f A' A) _ _ _ _ _ _

/-- **R4, SM-TCR adversary (old cap).** -/
theorem wotsTcr_phase1_hashfree_all (A' : Forger vp (withHash prims f) optRand' pkSeedDist')
    (A : Forger vp prims optRand pkSeedDist) :
    @Eq (OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rTcr (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).choose
      (rTcr pkSeedDist (Lazy.bWotsS A)).choose := by
  unfold rTcr
  simp only [tcrStart_withHash, tcrChainHash_withHash, wtcrColl_withHash]
  exact simChoose_withHash f _ _ _ (bWotsS_phase1_hashfree_all f A' A) _ _ _ _ _ _

/-- **R4, SM-TCR adversary (tight cap).** -/
theorem wotsTcrT_phase1_hashfree_all (A' : Forger vp (withHash prims f) optRand' pkSeedDist')
    (A : Forger vp prims optRand pkSeedDist) :
    @Eq (OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rTcrT (vp := vp) (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).choose
      (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose := by
  dsimp only [rTcrT, TightCaps.retype]
  exact wotsTcr_phase1_hashfree_all f A' A

/-- **R4, SM-UD adversary** (first phase = `pick`). -/
theorem wotsUd_phase1_hashfree_all (A' : Forger vp (withHash prims f) optRand' pkSeedDist')
    (A : Forger vp prims optRand pkSeedDist) :
    @Eq (OracleComp (udSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rUd (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).pick
      (rUd pkSeedDist (Lazy.bWotsS A)).pick := by
  unfold rUd
  simp only [udStart_withHash, udChainHash_withHash, udColl_withHash]
  refine bind_congr fun k => ?_
  exact simChoose_withHash f _ _ _ (bWotsS_phase1_hashfree_all f A' A) _ _ _ _ _ _

/-! ## `q₁ = 0`: explicit forger-free, hash-free first-phase programs

`wotsPhase1`, `udPhase1`, `prePhase1`, `wotsTcrPhase1` take neither a forger nor hash functions as
arguments; they are programs over the game's oracle interface (coins, challenge, collection —
no hash oracle).  The first phase of each adversary, built over ANY `withHash prims f` from ANY
forger, is that one program. -/

/-- First phase of `Lazy.bWotsS`: sample the FORS secret cells, run `chooseBody`. -/
noncomputable def wotsPhase1 (vp : ValidatedParams) (prims : Primitives vp.params)
    [SampleableType prims.Y] [Inhabited prims.Y] :
    OracleComp (WSpec prims) (WState vp prims) :=
  (monadLift (Lazy.sparseOn vp prims (forsSkIdx vp)) :
      OracleComp (WSpec prims) (SecretTable vp prims)) >>= fun tbl =>
    (chooseBody tbl).run [] >>= fun x =>
      (pure (tbl, x.2, x.1) : OracleComp (WSpec prims) (WState vp prims))

/-- `wotsPhase1` run inside a reduction (the body of `WotsGame.simChoose`). -/
noncomputable def simPhase1 {ι : Type} {spec : OracleSpec ι}
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y) :
    OracleComp (unifSpec + spec) (RState vp prims) :=
  (simulateQ
    ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT (List (WotsGame.Entry prims)) (OracleComp (unifSpec + spec))) +
      (WotsGame.simSignOracle (wotsInsts vp) startVal chainHash +
        WotsGame.simCollOracle (wotsInsts vp) coll)) (wotsPhase1 vp prims)).run []

/-- First phase of the SM-UD adversary. -/
noncomputable def udPhase1 (pkSeedDist : ProbComp prims.PkSeed) :
    OracleComp (udSpecC prims.AdrsKey prims.Y) (RState vp prims) :=
  (monadLift ($ᵗ (Fin (vp.params.w - 3 + 1)) : ProbComp (Fin (vp.params.w - 3 + 1))) :
      OracleComp (udSpecC prims.AdrsKey prims.Y) (Fin (vp.params.w - 3 + 1))) >>= fun k =>
    simPhase1 (udStart pkSeedDist k.val) (udChainHash pkSeedDist) (udColl pkSeedDist)

/-- First phase of the SM-PRE adversary. -/
noncomputable def prePhase1 (pkSeedDist : ProbComp prims.PkSeed) :
    OracleComp (preSpecC prims.AdrsKey prims.Y) (RState vp prims) :=
  simPhase1 (preStart pkSeedDist) (preChainHash pkSeedDist) (preColl pkSeedDist)

/-- First phase of the SM-TCR adversary (both caps). -/
noncomputable def wotsTcrPhase1 (pkSeedDist : ProbComp prims.PkSeed) :
    OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims) :=
  simPhase1 (tcrStart pkSeedDist) (tcrChainHash pkSeedDist) (wtcrColl pkSeedDist)

theorem bWotsS_phase1_eq (A' : Forger vp (withHash prims f) optRand' pkSeedDist') :
    @Eq (OracleComp (WSpec prims) (WState vp prims))
      (Lazy.bWotsS A').choose (wotsPhase1 vp prims) := by
  unfold Lazy.bWotsS wotsPhase1
  rw [Lazy.bWotsWith_choose_eq, sparseOn_withHash]
  simp only [chooseBody_withHash]
  rfl

theorem simChoose_eq_simPhase1 {ι : Type} {spec : OracleSpec ι}
    (c₁ : OracleComp (WSpec prims) (WState vp prims)) (h : c₁ = wotsPhase1 vp prims)
    (f₁ : WState vp prims → prims.PkSeed → ProbComp (ℕ × prims.Y × WotsSig vp.params prims.core))
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y) :
    WotsGame.simChoose (prims := withHash prims f) ⟨WState vp prims, c₁, f₁⟩ (wotsInsts vp)
        startVal chainHash coll = simPhase1 startVal chainHash coll := by
  subst h; rfl

/-- **`q₁ = 0`, SM-PRE**: for all hash functions and all forgers the first phase is the fixed
program `prePhase1 pkSeedDist` over `preSpecC` (no hash oracle). -/
theorem wotsPre_phase1_q1_zero (A' : Forger vp (withHash prims f) optRand' pkSeedDist') :
    @Eq (OracleComp (preSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rPre (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).choose
      (prePhase1 pkSeedDist) := by
  unfold rPre prePhase1
  simp only [preStart_withHash, preChainHash_withHash, preColl_withHash]
  exact simChoose_eq_simPhase1 f _ (bWotsS_phase1_eq f A') _ _ _ _

/-- **`q₁ = 0`, SM-TCR (old cap).** -/
theorem wotsTcr_phase1_q1_zero (A' : Forger vp (withHash prims f) optRand' pkSeedDist') :
    @Eq (OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rTcr (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).choose
      (wotsTcrPhase1 pkSeedDist) := by
  unfold rTcr wotsTcrPhase1
  simp only [tcrStart_withHash, tcrChainHash_withHash, wtcrColl_withHash]
  exact simChoose_eq_simPhase1 f _ (bWotsS_phase1_eq f A') _ _ _ _

/-- **`q₁ = 0`, SM-TCR (tight cap).** -/
theorem wotsTcrT_phase1_q1_zero (A' : Forger vp (withHash prims f) optRand' pkSeedDist') :
    @Eq (OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rTcrT (vp := vp) (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).choose
      (wotsTcrPhase1 pkSeedDist) := by
  dsimp only [rTcrT, TightCaps.retype]
  exact wotsTcr_phase1_q1_zero f A'

/-- **`q₁ = 0`, SM-UD.** -/
theorem wotsUd_phase1_q1_zero (A' : Forger vp (withHash prims f) optRand' pkSeedDist') :
    @Eq (OracleComp (udSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rUd (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).pick
      (udPhase1 pkSeedDist) := by
  unfold rUd udPhase1
  simp only [udStart_withHash, udChainHash_withHash, udColl_withHash]
  refine bind_congr fun k => ?_
  exact simChoose_eq_simPhase1 f _ (bWotsS_phase1_eq f A') _ _ _ _

/-- The fixed first-phase programs themselves do not depend on the hash components of the
bundle they are written over. -/
theorem phase1_programs_hashfree :
    @Eq (OracleComp (udSpecC prims.AdrsKey prims.Y) (RState vp prims))
        (udPhase1 (vp := vp) (prims := withHash prims f) pkSeedDist) (udPhase1 pkSeedDist) ∧
    @Eq (OracleComp (preSpecC prims.AdrsKey prims.Y) (RState vp prims))
        (prePhase1 (vp := vp) (prims := withHash prims f) pkSeedDist) (prePhase1 pkSeedDist) ∧
    @Eq (OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims))
        (wotsTcrPhase1 (vp := vp) (prims := withHash prims f) pkSeedDist) (wotsTcrPhase1 pkSeedDist) := by
  have hw : wotsPhase1 vp (withHash prims f) = wotsPhase1 vp prims := by
    unfold wotsPhase1
    rw [sparseOn_withHash]
    simp only [chooseBody_withHash]
  have hs : ∀ {ι : Type} {spec : OracleSpec ι}
      (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
      (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
      (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y),
      simPhase1 (vp := vp) (prims := withHash prims f) startVal chainHash coll =
        simPhase1 (vp := vp) (prims := prims) startVal chainHash coll := by
    intro ι spec s c k
    unfold simPhase1
    rw [hw]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold udPhase1
    refine bind_congr fun k => ?_
    rw [udStart_withHash, udChainHash_withHash, udColl_withHash]
    exact hs _ _ _
  · unfold prePhase1
    rw [preStart_withHash, preChainHash_withHash, preColl_withHash]
    exact hs _ _ _
  · unfold wotsTcrPhase1
    rw [tcrStart_withHash, tcrChainHash_withHash, wtcrColl_withHash]
    exact hs _ _ _

/-! ## R4, mandatory level: `withTH` / `castForger` -/

section TH
variable (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
  (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)

theorem bWotsS_phase1_hashfree (A : Forger vp prims optRand pkSeedDist) :
    @Eq (OracleComp (WSpec prims) (WState vp prims))
      (Lazy.bWotsS (castForger T H A)).choose (Lazy.bWotsS A).choose :=
  bWotsS_phase1_hashfree_all ⟨T, H, prims.PRF, prims.PRFmsg⟩ (castForger T H A) A

theorem wotsUd_phase1_hashfree (A : Forger vp prims optRand pkSeedDist) :
    @Eq (OracleComp (udSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rUd (prims := withTH prims T H) pkSeedDist (Lazy.bWotsS (castForger T H A))).pick
      (rUd pkSeedDist (Lazy.bWotsS A)).pick :=
  wotsUd_phase1_hashfree_all ⟨T, H, prims.PRF, prims.PRFmsg⟩ (castForger T H A) A

theorem wotsPre_phase1_hashfree (A : Forger vp prims optRand pkSeedDist) :
    @Eq (OracleComp (preSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rPre (prims := withTH prims T H) pkSeedDist (Lazy.bWotsS (castForger T H A))).choose
      (rPre pkSeedDist (Lazy.bWotsS A)).choose :=
  wotsPre_phase1_hashfree_all ⟨T, H, prims.PRF, prims.PRFmsg⟩ (castForger T H A) A

theorem wotsTcr_phase1_hashfree (A : Forger vp prims optRand pkSeedDist) :
    @Eq (OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rTcr (prims := withTH prims T H) pkSeedDist (Lazy.bWotsS (castForger T H A))).choose
      (rTcr pkSeedDist (Lazy.bWotsS A)).choose :=
  wotsTcr_phase1_hashfree_all ⟨T, H, prims.PRF, prims.PRFmsg⟩ (castForger T H A) A

theorem wotsTcrT_phase1_hashfree (A : Forger vp prims optRand pkSeedDist) :
    @Eq (OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims))
      (rTcrT (vp := vp) (prims := withTH prims T H) pkSeedDist
        (Lazy.bWotsS (castForger T H A))).choose
      (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose :=
  wotsTcrT_phase1_hashfree_all ⟨T, H, prims.PRF, prims.PRFmsg⟩ (castForger T H A) A

end TH

end Open
end Reduction

#print axioms Reduction.Open.bWotsS_phase1_hashfree
#print axioms Reduction.Open.wotsUd_phase1_hashfree
#print axioms Reduction.Open.wotsPre_phase1_hashfree
#print axioms Reduction.Open.wotsTcr_phase1_hashfree
#print axioms Reduction.Open.wotsTcrT_phase1_hashfree
#print axioms Reduction.Open.bWotsS_phase1_hashfree_all
#print axioms Reduction.Open.wotsUd_phase1_hashfree_all
#print axioms Reduction.Open.wotsPre_phase1_hashfree_all
#print axioms Reduction.Open.wotsTcrT_phase1_hashfree_all
#print axioms Reduction.Open.wotsUd_phase1_q1_zero
#print axioms Reduction.Open.wotsPre_phase1_q1_zero
#print axioms Reduction.Open.wotsTcrT_phase1_q1_zero
#print axioms Reduction.Open.phase1_programs_hashfree
