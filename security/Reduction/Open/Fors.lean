/-
Work package OPEN, items R3 and R7 for the FORS adversaries `toDspr (Lazy.bOpenPreS A)` and
`toTcr (Lazy.bOpenPreS A)`.

Inspection result (R3).  The post-seed phase of both adversaries is `(toTcr B).forge` /
`(toDspr B).guess` at `B = Lazy.bOpenPreS A`.  By `Resources2.toTcr_bOpenPreS_forge_full` /
`toDspr_bOpenPreS_guess_full` it is

  `(simulateQ (findOracles tg) (simulateQ (tblImpl (PublicHash.impl prims) tbl)
      (findOpenFull A pk ys))).run [] >>= post`.

`findOpenFull` already contains the answer extraction (`findAnswerO`), so no extension of the
open program is needed.  What was missing is a theorem that nothing outside the `tblImpl`
interpretation evaluates a hash.  This file supplies it in the checkable sense of the brief:

* the open program is generic in the forger PROGRAM (`forsFindOpen optRand main pk ys`, R7) and is
  the SAME term for `prims` and `Open.withTH prims T H` (`forsFindOpen_withTH`, by `rfl`);
* the outer run `forsRun hI tbl tg P` takes the hash evaluation as the PARAMETER
  `hI : QueryImpl (publicHashSpec prims.core) Id` and otherwise consists of `Lazy.tblImpl`,
  VCVio's `findOracles tg` (list lookups in `tg`) and `StateT.run`: a term that does not mention
  `prims.Thash` / `prims.Hmsg`; unchanged under `withTH` (`forsRun_withTH`, by `rfl`);
* the post-processing `forsTcrPost`, `forsDsprPost tg` are closed terms over `prims.Y` (a
  projection; a comparison and a list-membership test), unchanged under `withTH` (`rfl`);
* hence, for ALL hash functions `T`, `H`, the second phase of the adversary built over
  `withTH prims T H` is the interpretation of the one fixed program by `PublicHash.impl
  (withTH prims T H)` (`forsTcr_phase2_open_eq_withTH`, `forsDspr_phase2_open_eq_withTH`).
-/
import Reduction.Resources2Fors
import Reduction.Open.WithHash

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Open

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.auxLemma false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

open Resources2
open TweakableHash.SM_DT_OpenPRE_SourceFinalValidity (findOracles)

/-! ## 1. The forger as a bare program (R7) -/

/-- A forger PROGRAM: the only way the forger enters the second phases.  (`A.main` for
`A : Forger vp prims optRand pkSeedDist`; no reference to `optRand`, `pkSeedDist` or to the hash
components of `prims`.) -/
abbrev ForgerProg (vp : ValidatedParams) (prims : Primitives vp.params) : Type :=
  PublicKeyCore prims.core →
    OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
      (List Byte × GeneralScheme.SignatureCore vp prims.core)

/-- `runForgerLog` for a forger program. -/
def runProgLog {ι : Type} {spec : OracleSpec ι}
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (main : ForgerProg vp prims)
    (pk : PublicKeyCore prims.core)
    (randomizer : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (signR : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    OracleComp (unifSpec + spec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  (simulateQ
    ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT (G2Log prims) (OracleComp (unifSpec + spec))) +
      logSignOracle optRand pk randomizer signR) (main pk)).run []

theorem runProgLog_main {ι : Type} {spec : OracleSpec ι}
    (A : Forger vp prims optRand pkSeedDist) (pk : PublicKeyCore prims.core)
    (randomizer : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (signR : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    runProgLog optRand A.main pk randomizer signR = runForgerLog A pk randomizer signR := rfl

/-- **The open second-phase program, generic in the forger program**: open key generation, one
run of `main` against the open signing simulation `forsSignOpen`, open answer extraction
`findAnswerO`.  Every `Thash` / `H_msg` evaluation is a hash query. -/
noncomputable def forsFindOpen (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (main : ForgerProg vp prims) (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y) := do
  let root ← Lazy.openKeygen prims (forsG prims) pkSeed
  let z ← runProgLog optRand main ⟨pkSeed, root⟩ lazyRandomizerLift
    (forsSignOpen ⟨pkSeed, root⟩ ys)
  findAnswerO ⟨pkSeed, root⟩ ys z.2 z.1.1 z.1.2

/-- At a forger, `forsFindOpen` is the existing `Resources2.findOpenFull`. -/
theorem forsFindOpen_main (A : Forger vp prims optRand pkSeedDist) (pkSeed : prims.PkSeed)
    (ys : List prims.Y) :
    forsFindOpen optRand A.main pkSeed ys = findOpenFull A pkSeed ys := rfl

/-- **Interpretation lemma, generic in the forger program** (`findOpenFull_tbl` without a
`Forger`): interpreting the secret oracle by `tbl` and the hash queries by `prims` gives one run
of `main` against the closed signing simulation `Reduction.openSign`, followed by
`openPreAnswer`. -/
theorem forsFindOpen_tbl (main : ForgerProg vp prims) (tbl : SecretTable vp prims)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    simulateQ (Lazy.tblImpl (PublicHash.impl prims) tbl) (forsFindOpen optRand main pkSeed ys) =
      runProgLog optRand main (idealPk vp prims tbl pkSeed) lazyRandomizerLift
          (Reduction.openSign (idealPk vp prims tbl pkSeed) tbl ys) >>= fun z =>
        pure (openPreAnswer (idealPk vp prims tbl pkSeed) ys z.2 z.1.1 z.1.2) :=
  findOpenFull_tbl (pure tbl)
    (⟨main⟩ : Forger vp prims optRand (pure pkSeed)) tbl pkSeed ys

/-- **Queries of kind `K` of `forsFindOpen`**, for a program with at most `qs` signing queries. -/
theorem forsFindOpen_kindBound (main : ForgerProg vp prims) (K : Lazy.Kind) (hK : K ≠ .unif)
    (qs : ℕ) (hmain : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (forsFindOpen optRand main pkSeed ys) (fun t => Lazy.kind t = K)
      (Lazy.keygenB vp (Lazy.ind K .sec) (Lazy.ind K .hash) +
        qs * forsSignB vp (Lazy.ind K .game) (Lazy.ind K .sec) (Lazy.ind K .hash) +
        (Lazy.ind K .hash + qs * Lazy.ind K .hash + vp.params.k * Lazy.ind K .hash)) :=
  findOpenFull_kindBound (⟨main⟩ : Forger vp prims optRand (pure pkSeed)) K hK qs hmain pkSeed ys

/-- **Hash queries of `forsFindOpen`**: key generation, `qs` signing simulations, answer
extraction. -/
theorem forsFindOpen_hashes (main : ForgerProg vp prims) (qs : ℕ)
    (hmain : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (forsFindOpen optRand main pkSeed ys) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * forsSignHashes vp + (1 + qs + vp.params.k)) :=
  findOpenFull_hashes (⟨main⟩ : Forger vp prims optRand (pure pkSeed)) qs hmain pkSeed ys

/-- Opening (game) queries of `forsFindOpen`. -/
theorem forsFindOpen_openings (main : ForgerProg vp prims) (qs : ℕ)
    (hmain : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (forsFindOpen optRand main pkSeed ys) (fun t => Lazy.kind t = .game)
      (qs * vp.params.k) :=
  findOpenFull_openings (⟨main⟩ : Forger vp prims optRand (pure pkSeed)) qs hmain pkSeed ys

/-- Secret (table) reads of `forsFindOpen`. -/
theorem forsFindOpen_reads (main : ForgerProg vp prims) (qs : ℕ)
    (hmain : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (forsFindOpen optRand main pkSeed ys) (fun t => Lazy.kind t = .sec)
      (2 ^ vp.params.hp * vp.params.len +
        qs * (vp.params.d * (2 ^ vp.params.hp * vp.params.len))) :=
  findOpenFull_reads (⟨main⟩ : Forger vp prims optRand (pure pkSeed)) qs hmain pkSeed ys

/-- Hash queries of `forsFindOpen` at SLH-DSA-SHA2-128s: `269839 + qs · 1950028`. -/
theorem forsFindOpen_hashes_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (main : ForgerProg Link.vp Link.prims) (qs : ℕ)
    (hmain : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (pkSeed : Link.prims.PkSeed) (ys : List Link.prims.Y) :
    IsQueryBoundP (forsFindOpen optRand main pkSeed ys) (fun t => Lazy.kind t = .hash)
      (269839 + qs * 1950028) :=
  findOpenFull_hashes_128s optRand (pure pkSeed)
    (⟨main⟩ : Forger Link.vp Link.prims optRand (pure pkSeed)) qs hmain pkSeed ys

/-! ## 2. The second phases, DEFINED as interpretations of the open program (R7) -/

/-- The outer run of a second phase: the open program `P` with its secret oracle read from `tbl`
and its hash queries evaluated by `hI`, then the opening queries answered by VCVio's
`findOracles tg` (list lookup in the sampled targets, recording the opened indices).

`hI` is the ONLY place a hash function enters: the term mentions no component of `prims` other
than the carrier types of `prims.core`. -/
noncomputable def forsRun (hI : QueryImpl (publicHashSpec prims.core) Id)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y))
    (P : OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y)) :
    ProbComp ((ℕ × prims.Y) × List ℕ) :=
  (simulateQ (findOracles tg) (simulateQ (Lazy.tblImpl hI tbl) P)).run []

/-- Post-processing of `toTcr`: forward the output (drop the list of opened indices). -/
def forsTcrPost {Y : Type} (z : (ℕ × Y) × List ℕ) : ℕ × Y := z.1

/-- Post-processing of `toDspr`: one comparison with the `j`-th sampled input and one
list-membership test.  Stated for an arbitrary type `Y`: it cannot evaluate a hash. -/
def forsDsprPost {K Y : Type} [DecidableEq Y] [Inhabited Y] (tg : List (K × Y))
    (z : (ℕ × Y) × List ℕ) : ℕ × Bool :=
  (z.1.1, decide ((tg[z.1.1]?.map Prod.snd).getD default ≠ z.1.2 ∨ z.1.1 ∈ z.2))

/-- **Second phase of the SM-TCR adversary, defined from the open program**, for an arbitrary
forger program. -/
noncomputable def forsTcrPhase2 (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (main : ForgerProg vp prims)
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pk : prims.PkSeed) : ProbComp (ℕ × prims.Y) :=
  forsRun (PublicHash.impl prims) st.1 st.2.1 (forsFindOpen optRand main pk st.2.2) >>=
    fun z => pure (forsTcrPost z)

/-- **Second phase of the SM-DSPR adversary, defined from the open program**, for an arbitrary
forger program. -/
noncomputable def forsDsprPhase2 (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (main : ForgerProg vp prims)
    (st : SecretTable vp prims × List (prims.AdrsKey × prims.Y) × List prims.Y)
    (pk : prims.PkSeed) : ProbComp (ℕ × Bool) :=
  forsRun (PublicHash.impl prims) st.1 st.2.1 (forsFindOpen optRand main pk st.2.2) >>=
    fun z => pure (forsDsprPost st.2.1 z)

/-! ## 3. Summary lemmas (fields of the later bundle) -/

/-- **`toTcr (bOpenPreS A)`, second phase = interpretation of the open program.** -/
theorem forsTcr_phase2_open_eq (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pk : prims.PkSeed) :
    (toTcr (Lazy.bOpenPreS A)).forge (tbl, tg, ys) pk =
      forsRun (PublicHash.impl prims) tbl tg (forsFindOpen optRand A.main pk ys) >>=
        fun z => pure (forsTcrPost z) :=
  toTcr_bOpenPreS_forge_full A tbl tg ys pk

/-- **`toDspr (bOpenPreS A)`, second phase = interpretation of the open program.** -/
theorem forsDspr_phase2_open_eq (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pk : prims.PkSeed) :
    (toDspr (Lazy.bOpenPreS A)).guess (tbl, tg, ys) pk =
      forsRun (PublicHash.impl prims) tbl tg (forsFindOpen optRand A.main pk ys) >>=
        fun z => pure (forsDsprPost tg z) :=
  toDspr_bOpenPreS_guess_full A tbl tg ys pk

/-- The second phase of `toTcr (bOpenPreS A)` IS the defined one at `A.main`. -/
theorem forsTcr_phase2_def (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pk : prims.PkSeed) :
    (toTcr (Lazy.bOpenPreS A)).forge (tbl, tg, ys) pk =
      forsTcrPhase2 optRand A.main (tbl, tg, ys) pk :=
  forsTcr_phase2_open_eq A tbl tg ys pk

/-- The second phase of `toDspr (bOpenPreS A)` IS the defined one at `A.main`. -/
theorem forsDspr_phase2_def (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pk : prims.PkSeed) :
    (toDspr (Lazy.bOpenPreS A)).guess (tbl, tg, ys) pk =
      forsDsprPhase2 optRand A.main (tbl, tg, ys) pk :=
  forsDspr_phase2_open_eq A tbl tg ys pk

/-- **Hash queries of the open second-phase program of `toTcr (bOpenPreS A)`.** -/
theorem forsTcr_phase2_open_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pk : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (forsFindOpen optRand A.main pk ys) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * forsSignHashes vp + (1 + qs + vp.params.k)) :=
  findOpenFull_hashes A qs hA pk ys

/-- **Hash queries of the open second-phase program of `toDspr (bOpenPreS A)`** (the same
program). -/
theorem forsDspr_phase2_open_hashes (A : Forger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pk : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (forsFindOpen optRand A.main pk ys) (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * forsSignHashes vp + (1 + qs + vp.params.k)) :=
  findOpenFull_hashes A qs hA pk ys

/-- SLH-DSA-SHA2-128s: `≤ 269839 + qs · 1950028` hash queries (`toTcr`). -/
theorem forsTcr_phase2_open_hashes_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pk : Link.prims.PkSeed) (ys : List Link.prims.Y) :
    IsQueryBoundP (forsFindOpen optRand A.main pk ys) (fun t => Lazy.kind t = .hash)
      (269839 + qs * 1950028) :=
  findOpenFull_hashes_128s optRand pkSeedDist A qs hA pk ys

/-- SLH-DSA-SHA2-128s: `≤ 269839 + qs · 1950028` hash queries (`toDspr`). -/
theorem forsDspr_phase2_open_hashes_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs)
    (pk : Link.prims.PkSeed) (ys : List Link.prims.Y) :
    IsQueryBoundP (forsFindOpen optRand A.main pk ys) (fun t => Lazy.kind t = .hash)
      (269839 + qs * 1950028) :=
  findOpenFull_hashes_128s optRand pkSeedDist A qs hA pk ys

/-! ## 4. Nothing outside the interpretation hashes (R3) -/

section HashFree

variable (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
  (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)

/-- **The open program does not depend on the hash functions**: built over `withTH prims T H`
it is the same term. -/
theorem forsFindOpen_withTH (main : ForgerProg vp prims) (pkSeed : prims.PkSeed)
    (ys : List prims.Y) :
    forsFindOpen (prims := withTH prims T H) optRand main pkSeed ys =
      forsFindOpen (prims := prims) optRand main pkSeed ys := by
  delta forsFindOpen lazyRandomizerLift lazyRandomizer lazyRandomizer.match_1
  rfl

/-- **The outer run does not depend on the hash functions** except through its argument `hI`. -/
theorem forsRun_withTH (hI : QueryImpl (publicHashSpec prims.core) Id)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y))
    (P : OracleComp (Lazy.OSpec prims (forsG prims)) (ℕ × prims.Y)) :
    forsRun (prims := withTH prims T H) hI tbl tg P = forsRun (prims := prims) hI tbl tg P := rfl

/-- The post-processing of `toDspr` does not depend on the hash functions. -/
theorem forsDsprPost_withTH (tg : List (prims.AdrsKey × prims.Y))
    (z : (ℕ × prims.Y) × List ℕ) :
    forsDsprPost (K := (withTH prims T H).AdrsKey) (Y := (withTH prims T H).Y) tg z =
      forsDsprPost (K := prims.AdrsKey) (Y := prims.Y) tg z := rfl

/-- **R3 for `toTcr (bOpenPreS ·)`, all hash functions at once.**  For every `T`, `H`: the second
phase of the adversary over `withTH prims T H` (same forger program) is the interpretation of
the ONE program `forsFindOpen optRand A.main pk ys` (built over `prims`) with hash queries
evaluated by `T`, `H`, followed by `forsTcrPost`.  So every `Thash` / `H_msg` evaluation of the
second phase is a hash query of that program. -/
theorem forsTcr_phase2_open_eq_withTH (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pk : prims.PkSeed) :
    (toTcr (Lazy.bOpenPreS (castForger T H A))).forge (tbl, tg, ys) pk =
      forsRun (prims := prims) (PublicHash.impl (withTH prims T H)) tbl tg
          (forsFindOpen (prims := prims) optRand A.main pk ys) >>=
        fun z => pure (forsTcrPost z) :=
  (forsTcr_phase2_open_eq (prims := withTH prims T H) (castForger T H A) tbl tg ys pk).trans
    (congrArg (fun P => forsRun (prims := prims) (PublicHash.impl (withTH prims T H)) tbl tg P >>=
      fun z => pure (forsTcrPost z)) (forsFindOpen_withTH T H A.main pk ys))

/-- **R3 for `toDspr (bOpenPreS ·)`, all hash functions at once.** -/
theorem forsDspr_phase2_open_eq_withTH (A : Forger vp prims optRand pkSeedDist)
    (tbl : SecretTable vp prims) (tg : List (prims.AdrsKey × prims.Y)) (ys : List prims.Y)
    (pk : prims.PkSeed) :
    (toDspr (Lazy.bOpenPreS (castForger T H A))).guess (tbl, tg, ys) pk =
      forsRun (prims := prims) (PublicHash.impl (withTH prims T H)) tbl tg
          (forsFindOpen (prims := prims) optRand A.main pk ys) >>=
        fun z => pure (forsDsprPost tg z) :=
  (forsDspr_phase2_open_eq (prims := withTH prims T H) (castForger T H A) tbl tg ys pk).trans
    (congrArg (fun P => forsRun (prims := prims) (PublicHash.impl (withTH prims T H)) tbl tg P >>=
      fun z => pure (forsDsprPost tg z)) (forsFindOpen_withTH T H A.main pk ys))

/-- The hash-query bound holds for the program whatever the hash functions are (it is a
statement about the program alone; recorded for the bundle). -/
theorem forsFindOpen_hashes_withTH (main : ForgerProg vp prims) (qs : ℕ)
    (hmain : ∀ pk, IsQueryBoundP (main pk) (fun i => i.isRight = true) qs)
    (pkSeed : prims.PkSeed) (ys : List prims.Y) :
    IsQueryBoundP (forsFindOpen (prims := withTH prims T H) optRand main pkSeed ys)
      (fun t => Lazy.kind t = .hash)
      (Lazy.keygenHashes vp + qs * forsSignHashes vp + (1 + qs + vp.params.k)) :=
  forsFindOpen_hashes (prims := withTH prims T H) main qs hmain pkSeed ys

end HashFree

end Open
end Reduction

#print axioms Reduction.Open.forsFindOpen_tbl
#print axioms Reduction.Open.forsFindOpen_kindBound
#print axioms Reduction.Open.forsFindOpen_hashes
#print axioms Reduction.Open.forsFindOpen_openings
#print axioms Reduction.Open.forsFindOpen_reads
#print axioms Reduction.Open.forsFindOpen_hashes_128s
#print axioms Reduction.Open.forsTcr_phase2_open_eq
#print axioms Reduction.Open.forsDspr_phase2_open_eq
#print axioms Reduction.Open.forsTcr_phase2_def
#print axioms Reduction.Open.forsDspr_phase2_def
#print axioms Reduction.Open.forsTcr_phase2_open_hashes
#print axioms Reduction.Open.forsDspr_phase2_open_hashes
#print axioms Reduction.Open.forsTcr_phase2_open_hashes_128s
#print axioms Reduction.Open.forsDspr_phase2_open_hashes_128s
#print axioms Reduction.Open.forsFindOpen_withTH
#print axioms Reduction.Open.forsRun_withTH
#print axioms Reduction.Open.forsTcr_phase2_open_eq_withTH
#print axioms Reduction.Open.forsDspr_phase2_open_eq_withTH
#print axioms Reduction.Open.forsFindOpen_hashes_withTH
