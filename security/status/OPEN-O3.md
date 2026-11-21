# OPEN-O3 — R3 and R7 for `toDspr/toTcr (Lazy.bOpenPreS A)` (FORS)

File: `Reduction/Open/Fors.lean` (namespace `Reduction.Open`; imports `Reduction.Resources2Fors`,
`Reduction.Open.WithHash`). Compiles with no error/warning; olean written
(`.lake/build/lib/lean/Reduction/Open/Fors.olean`). No `sorry`/`axiom`/`native_decide`; no
conditional theorem; no existing file touched. All proofs are reuse of `Resources2.*`.

## Inspection (R3)
Post-seed phase = `(toTcr B).forge (tbl,tg,ys) pk` / `(toDspr B).guess (tbl,tg,ys) pk`, `B = bOpenPreS A`.
The existing `findOpenFull` ALREADY contains the answer extraction (`findAnswerO`: forgery `H_msg`,
one `H_msg` per signed message, `k` `F`), keygen and all signing simulations. NO extension of the
open program was needed (no `findOpenAll`); the numerals are unchanged. Outside the `tblImpl`
interpretation there remain exactly three things, each now shown hash-free:
1. opening simulation `findOracles tg` (VCVio; arguments: only the types `AdrsKey`, `Y` and the list `tg`);
2. `StateT.run … []`;
3. post-processing: `forsTcrPost z = z.1`; `forsDsprPost tg z = (z.1.1, decide ((tg[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2))` — defined for ARBITRARY types `K`, `Y` (no `prims` at all).
1+2 are packaged as `forsRun hI tbl tg P`, which takes the hash evaluation as a parameter `hI`.

## Definitions (verbatim signatures)
```lean
abbrev ForgerProg (vp) (prims : Primitives vp.params) : Type :=
  PublicKeyCore prims.core → OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
    (List Byte × GeneralScheme.SignatureCore vp prims.core)
def runProgLog (optRand) (main : ForgerProg vp prims) (pk) (randomizer) (signR) : OracleComp (unifSpec + spec) (… × G2Log prims)
noncomputable def forsFindOpen (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (main : ForgerProg vp prims)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) : OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y)
noncomputable def forsRun (hI : QueryImpl (publicHashSpec prims.core) Id) (tbl : SecretTable vp prims)
    (tg : List (prims.AdrsKey × prims.Y)) (P : OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y)) :
    ProbComp ((ℕ × prims.Y) × List ℕ) := (simulateQ (findOracles tg) (simulateQ (Lazy.tblImpl hI tbl) P)).run []
def forsTcrPost {Y} (z : (ℕ × Y) × List ℕ) : ℕ × Y
def forsDsprPost {K Y} [DecidableEq Y] [Inhabited Y] (tg : List (K × Y)) (z : (ℕ × Y) × List ℕ) : ℕ × Bool
noncomputable def forsTcrPhase2 / forsDsprPhase2 (optRand) (main : ForgerProg vp prims)
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y) (pk : prims.PkSeed) : ProbComp _
    -- := forsRun (PublicHash.impl prims) st.1 st.2.1 (forsFindOpen optRand main pk st.2.2) >>= pure ∘ post
```
`forsFindOpen` = `findOpenFull` with `A.main` replaced by `main` (`forsFindOpen_main : forsFindOpen optRand A.main pkSeed ys = findOpenFull A pkSeed ys := rfl`; `runProgLog_main` likewise for `runForgerLog`).

## Summary lemmas (item 3; bundle fields)
```lean
theorem forsTcr_phase2_open_eq (A : Forger vp prims optRand pkSeedDist) (tbl) (tg) (ys) (pk) :
    (toTcr (Lazy.bOpenPreS A)).forge (tbl, tg, ys) pk =
      forsRun (PublicHash.impl prims) tbl tg (forsFindOpen optRand A.main pk ys) >>= fun z => pure (forsTcrPost z)
theorem forsDspr_phase2_open_eq (A) (tbl) (tg) (ys) (pk) :
    (toDspr (Lazy.bOpenPreS A)).guess (tbl, tg, ys) pk =
      forsRun (PublicHash.impl prims) tbl tg (forsFindOpen optRand A.main pk ys) >>= fun z => pure (forsDsprPost tg z)
theorem forsTcr_phase2_open_hashes / forsDspr_phase2_open_hashes (A) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) (pk : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (forsFindOpen optRand A.main pk ys) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * forsSignHashes vp + (1 + qs + vp.params.k))
theorem forsTcr_phase2_open_hashes_128s / forsDspr_phase2_open_hashes_128s (optRand) (pkSeedDist)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs) (hA) (pk) (ys) :
    IsQueryBoundP (forsFindOpen optRand A.main pk ys) (fun t => Lazy.kind t = .hash) (269839 + qs * 1950028)
```
(Tcr and Dspr use the same program, so the two `_hashes` statements are identical.)
Also `forsTcr_phase2_def`, `forsDspr_phase2_def`: the phases equal `forsTcrPhase2/forsDsprPhase2 optRand A.main (tbl,tg,ys) pk`.

## R3: nothing outside the interpretation hashes (`T`, `H` arbitrary hash functions)
```lean
theorem forsFindOpen_withTH (main) (pkSeed) (ys) :
    forsFindOpen (prims := withTH prims T H) optRand main pkSeed ys = forsFindOpen (prims := prims) optRand main pkSeed ys
theorem forsRun_withTH (hI) (tbl) (tg) (P) : forsRun (prims := withTH prims T H) hI tbl tg P = forsRun (prims := prims) hI tbl tg P  -- rfl
theorem forsDsprPost_withTH …  -- rfl
theorem forsTcr_phase2_open_eq_withTH (A : Forger vp prims optRand pkSeedDist) (tbl) (tg) (ys) (pk) :
    (toTcr (Lazy.bOpenPreS (castForger T H A))).forge (tbl, tg, ys) pk =
      forsRun (prims := prims) (PublicHash.impl (withTH prims T H)) tbl tg
        (forsFindOpen (prims := prims) optRand A.main pk ys) >>= fun z => pure (forsTcrPost z)
theorem forsDspr_phase2_open_eq_withTH …  -- same with `.guess`, `forsDsprPost tg`
theorem forsFindOpen_hashes_withTH …      -- the bound for the program over `withTH prims T H`
```
Reading: for ALL `T`, `H` the second phase over `withTH prims T H` is ONE fixed program (built over
`prims`, independent of `T`, `H`) interpreted by `PublicHash.impl (withTH prims T H)`, then hash-free
post-processing. Hence every `Thash`/`H_msg` evaluation of the second phase is a hash query of
`forsFindOpen`. (`forsFindOpen_withTH` is not `rfl` for the elaborator only because of the matcher in
`lazyRandomizer`; proof = `delta … ; rfl`.)

## R7: generic in the forger program
```lean
theorem forsFindOpen_tbl (main : ForgerProg vp prims) (tbl) (pkSeed) (ys) :
    simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (forsFindOpen optRand main pkSeed ys) =
      runProgLog optRand main (idealPk vp prims tbl pkSeed) lazyRandomizerLift
          (Reduction.openSign (idealPk vp prims tbl pkSeed) tbl ys) >>= fun z =>
        pure (openPreAnswer (idealPk vp prims tbl pkSeed) ys z.2 z.1.1 z.1.2)
theorem forsFindOpen_kindBound / _hashes / _openings / _reads / _hashes_128s (main) (qs)
    (hmain : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs) …   -- as the `findOpenFull_*` ones
```
plus the DEFINED second phases `forsTcrPhase2`, `forsDsprPhase2` (both options of R7).
Gen: `Reduction/Gen/Resources.lean` already has the general-spec (`ds + unifSpec`) analogue
`findOpenFullG ds optRand F`, `findOpenFullG_tbl` (via `wrapS`), `findOpenFullG_embed`,
`findOpenFullG_hashes`; not re-derived here and not connected to `forsFindOpen` (Gen not imported).

## Deviations / not done
- Signing-query hypothesis on `main` is `IsQueryBoundP (main pk) (·.isRight) qs` as before.
- `forsFindOpen` still takes `optRand` (the scheme's `opt_rand` sampler, a `ProbComp`; drawn through
  `liftM`, kind `.unif`). If `optRand` itself were defined via a hash this is outside `prims.Thash/Hmsg`.
- The instance arguments `[SampleableType prims.SkSeed] [SampleableType prims.SkPrf]` are still present
  on the generic theorems (section variables), unused.
- The hash-free claim is `withTH` (Thash, Hmsg); `PRF`/`PRFmsg` (`withHash`) not treated (they live in
  `prims.core`; the second phase does not call them by inspection: secrets come from `tbl`, `R` from
  `lazyRandomizer`).
- No Gen (`ds`) version of the `withTH` statements.

## Axioms
All 19 `#print axioms` lines: `[propext, Classical.choice, Quot.sound]`.
