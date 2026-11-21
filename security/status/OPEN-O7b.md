# OPEN-O7b — R4 ("first phases do no hashing of their own") for the WOTS adversaries

File (new, only one): `Reduction/Open/Phase1Wots.lean` (376 lines, compiles in ~3 s, olean written to
`.lake/build/lib/lean/Reduction/Open/Phase1Wots.olean`). Imports `Reduction.Open.WithHash`,
`Reduction.TightCapsHeadline`. Namespace `Reduction.Open`. No sorry/axiom/native_decide; no existing
file touched. Both the mandatory and the optional level are DONE; no first phase depends on any hash.

Context variables: `vp`, `prims : Primitives vp.params`, the usual instances, `optRand`, `pkSeedDist`,
`f : HashFns prims`, `optRand' : PublicKeyCore (withHash prims f).core → ProbComp prims.Y`, `pkSeedDist'`.

## Definitions
```
abbrev collSpecC (K Y : Type) : OracleSpec ((_ : Unit) × K × List Y) := _ →ₒ Option Y
abbrev udSpecC  (K Y) := unifSpec + (SM_DT_UD_challengeSpec K Y  + collSpecC K Y)
abbrev preSpecC (K Y) := unifSpec + (SM_DT_PRE_challengeSpec K Y + collSpecC K Y)
abbrev tcrSpecC (K Y) := unifSpec + (SM_DT_TCR_challengeSpec K Y Y + collSpecC K Y)
abbrev WState vp prims := SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y   -- (bWotsS A).State
abbrev RState vp prims := WState vp prims × List (WotsGame.Entry prims)                  -- (rUd/rPre/rTcr(T) ..).State
noncomputable def wotsPhase1 vp prims : OracleComp (WSpec prims) (WState vp prims)       -- sparseOn; chooseBody
noncomputable def simPhase1 startVal chainHash coll : OracleComp (unifSpec + spec) (RState vp prims)
noncomputable def udPhase1  pkSeedDist : OracleComp (udSpecC  prims.AdrsKey prims.Y) (RState vp prims)
noncomputable def prePhase1 pkSeedDist : OracleComp (preSpecC prims.AdrsKey prims.Y) (RState vp prims)
noncomputable def tcrPhase1 pkSeedDist : OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims)
```
The `*Phase1` programs take NO forger and NO hash function; explicit programs (no choice, no tables).
`udSpec_eq / preSpec_eq / wtcrSpec_eq : UdSpec pkSeedDist = udSpecC prims.AdrsKey prims.Y` etc. (`rfl`):
the game interface is a function of the carrier types only and contains no hash oracle.

## Mandatory level (`withTH`, `castForger`) — plain `=`, no HEq
```
theorem bWotsS_phase1_hashfree (T H) (A : Forger vp prims optRand pkSeedDist) :
  @Eq (OracleComp (WSpec prims) (WState vp prims))
    (Lazy.bWotsS (castForger T H A)).choose (Lazy.bWotsS A).choose
theorem wotsUd_phase1_hashfree (T H) (A) :
  @Eq (OracleComp (udSpecC prims.AdrsKey prims.Y) (RState vp prims))
    (rUd (prims := withTH prims T H) pkSeedDist (Lazy.bWotsS (castForger T H A))).pick
    (rUd pkSeedDist (Lazy.bWotsS A)).pick
theorem wotsPre_phase1_hashfree (T H) (A) :
  @Eq (OracleComp (preSpecC prims.AdrsKey prims.Y) (RState vp prims))
    (rPre (prims := withTH prims T H) pkSeedDist (Lazy.bWotsS (castForger T H A))).choose
    (rPre pkSeedDist (Lazy.bWotsS A)).choose
theorem wotsTcrT_phase1_hashfree (T H) (A) :
  @Eq (OracleComp (tcrSpecC prims.AdrsKey prims.Y) (RState vp prims))
    (rTcrT (vp := vp) (prims := withTH prims T H) pkSeedDist (Lazy.bWotsS (castForger T H A))).choose
    (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS A)).choose
```
plus `wotsTcr_phase1_hashfree` (same for `rTcr`). First phase of SM-UD is the field `pick`.

## Optional level (all four components, `withHash prims f`) — also plain `=`, and stronger
No transport is needed: the first phases never use the forger, so the statement quantifies over an
ARBITRARY forger `A'` against the replaced scheme (any `optRand'`, `pkSeedDist'`) instead of a transported
`A`; the state/spec types of `withHash prims f` are definitionally those of `prims` (only carrier types).
```
theorem bWotsS_phase1_hashfree_all (f) (A' : Forger vp (withHash prims f) optRand' pkSeedDist')
    (A : Forger vp prims optRand pkSeedDist) :
  @Eq (OracleComp (WSpec prims) (WState vp prims)) (Lazy.bWotsS A').choose (Lazy.bWotsS A).choose
theorem wotsUd_phase1_hashfree_all (f) (A') (A) : @Eq (OracleComp (udSpecC ..) (RState vp prims))
    (rUd (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).pick (rUd pkSeedDist (Lazy.bWotsS A)).pick
theorem wotsPre_phase1_hashfree_all, wotsTcr_phase1_hashfree_all, wotsTcrT_phase1_hashfree_all  -- same shape, `.choose`
```
The mandatory theorems are these at `f := ⟨T, H, prims.PRF, prims.PRFmsg⟩`, `A' := castForger T H A`.

## Corollary for the quantum side (`q₁ = 0`)
```
theorem wotsUd_phase1_q1_zero (f) (A' : Forger vp (withHash prims f) optRand' pkSeedDist') :
  @Eq (OracleComp (udSpecC prims.AdrsKey prims.Y) (RState vp prims))
    (rUd (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).pick (udPhase1 pkSeedDist)
theorem wotsPre_phase1_q1_zero  : … (rPre  (prims := withHash prims f) pkSeedDist (Lazy.bWotsS A')).choose = prePhase1 pkSeedDist
theorem wotsTcr_phase1_q1_zero  : … (rTcr  …).choose = tcrPhase1 pkSeedDist
theorem wotsTcrT_phase1_q1_zero : … (rTcrT …).choose = tcrPhase1 pkSeedDist
theorem bWotsS_phase1_eq        : (Lazy.bWotsS A').choose = wotsPhase1 vp prims
theorem phase1_programs_hashfree (f) : udPhase1 (prims := withHash prims f) pkSeedDist = udPhase1 pkSeedDist ∧
    prePhase1 (prims := withHash prims f) … = prePhase1 … ∧ tcrPhase1 (prims := withHash prims f) … = tcrPhase1 …
```
Honest reading of "q₁ = 0": for every hash bundle and every forger, the first phase IS one fixed program
over `unifSpec + (challenge + collection)`; that interface has no hash oracle, and the program is
independent of `Thash`, `Hmsg`, `PRF`, `PRFmsg` and of the forger. The hash evaluations that happen during
phase 1 are those of the GAME's challenge/collection oracles (each `preColl/udColl/wtcrColl/…Chal` call is
one such oracle query); this file does not count them (no `IsQueryBoundP` statement; no numerals here —
128s numerals: none).

## Deviations / notes for users
- Statements are written with an explicit `@Eq <type>` (carrier-only spec, `RState`) rather than a bare
  `x.choose = y.choose`. Reason: for `rTcrT` (and potentially in consumers) letting Lean unify the two
  inferred types makes `isDefEq` compare the two adversary structures (incl. `forge`, which differs)
  and times out in `whnf`. The explicit type is definitionally the inferred one on both sides. To use:
  `have h := wotsPre_phase1_hashfree T H A` then `rw`/`exact` after `dsimp only [rTcrT, TightCaps.retype]`
  or `unfold rPre`; avoid stating a bare equation between the two `.choose` projections of `rTcrT`.
- The `State` types are equal by `rfl` (`RState vp prims`, `WState vp prims`); not stated separately.
- `rfl` alone does not prove the theorems (unifier unfolds `simulateQ` over `chooseBody`); proofs go
  through `wColl/topsAt/msgAt/chooseBody/sparseOn/simChoose/…_withHash` lemmas (all in the file).
- Not done: a counted (`IsQueryBoundP`) bound on the number of collection/challenge queries of the first
  phases (exists elsewhere: `Resources.rUd_challenges_le`, `rPre_challenges_le`, `rTcrT_targets_le`).

## Axioms
`#print axioms` for `bWotsS_/wotsUd_/wotsPre_/wotsTcr_/wotsTcrT_phase1_hashfree`, the four `_all`,
`wotsUd_/wotsPre_/wotsTcrT_phase1_q1_zero`, `phase1_programs_hashfree`: each
`[propext, Classical.choice, Quot.sound]`.
