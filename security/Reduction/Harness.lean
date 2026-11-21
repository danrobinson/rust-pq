import Reduction.Steps

/-!
# Shared simulation harness for the reductions

`runForger` runs the forger with its uniform-sampling queries forwarded and its signing queries
answered by an arbitrary signing procedure in the reduction's own monad, recording the queried
messages.  Every reduction that runs `A` uses it, so that the "runs `A` once" claim is syntactic.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- The signing oracle of a reduction: answer by `sign`, record the message. -/
def harnessSignOracle {ι : Type} {spec : OracleSpec ι}
    (sign : List Byte → OracleComp spec (GeneralScheme.SignatureCore vp prims.core)) :
    QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (StateT (List (List Byte)) (OracleComp spec)) :=
  fun msg => do
    let sig ← (monadLift (sign msg) :
      StateT (List (List Byte)) (OracleComp spec) (GeneralScheme.SignatureCore vp prims.core))
    modify (· ++ [msg])
    return sig

/-- Run the forger once inside a reduction whose oracle interface is `unifSpec + spec`. -/
def runForger {ι : Type} {spec : OracleSpec ι} (A : Forger vp prims optRand pkSeedDist)
    (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    OracleComp (unifSpec + spec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × List (List Byte)) :=
  (simulateQ
    ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT (List (List Byte)) (OracleComp (unifSpec + spec))) +
      harnessSignOracle sign) (A.main pk)).run []

/-- The final check every forgery reduction/distinguisher performs: fresh and valid. -/
def harnessValid (pk : PublicKeyCore prims.core) (msgs : List (List Byte)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) : Bool :=
  decide (msg ∉ msgs) && GeneralScheme.verifyInternal vp prims msg sig pk

/-! ## Transcript-recording harness (shape of `G2`) -/

/-- The signing oracle of a reduction that simulates `G2`: `opt_rand` is drawn as in the scheme,
the randomizer comes from `randomizer` (given the transcript so far), the signature from `signR`,
and the transcript entry `(M, opt_rand, R)` is recorded. -/
def logSignOracle {ι : Type} {spec : OracleSpec ι}
    (optRand : PublicKeyCore prims.core → ProbComp prims.Y) (pk : PublicKeyCore prims.core)
    (randomizer : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (signR : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    QueryImpl (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)
      (StateT (G2Log prims) (OracleComp (unifSpec + spec))) :=
  fun msg => do
    let addrnd ← (monadLift ((monadLift (optRand pk) : OracleComp (unifSpec + spec) prims.Y)) :
      StateT (G2Log prims) (OracleComp (unifSpec + spec)) prims.Y)
    let log ← get
    let R ← (monadLift (randomizer log msg addrnd) :
      StateT (G2Log prims) (OracleComp (unifSpec + spec)) prims.Y)
    let sig ← (monadLift (signR msg R) :
      StateT (G2Log prims) (OracleComp (unifSpec + spec))
        (GeneralScheme.SignatureCore vp prims.core))
    set (log ++ [(msg, addrnd, R)])
    return sig

/-- Run the forger once against `logSignOracle`; returns the forgery and the transcript. -/
def runForgerLog {ι : Type} {spec : OracleSpec ι} (A : Forger vp prims optRand pkSeedDist)
    (pk : PublicKeyCore prims.core)
    (randomizer : G2Log prims → List Byte → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (signR : List Byte → prims.Y →
      OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    OracleComp (unifSpec + spec)
      ((List Byte × GeneralScheme.SignatureCore vp prims.core) × G2Log prims) :=
  (simulateQ
    ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT (G2Log prims) (OracleComp (unifSpec + spec))) +
      logSignOracle optRand pk randomizer signR) (A.main pk)).run []

/-- The randomizer of `G2` inside a reduction: reuse the recorded value or sample afresh. -/
noncomputable def lazyRandomizerLift {ι : Type} {spec : OracleSpec ι} (log : G2Log prims)
    (msg : List Byte) (addrnd : prims.Y) : OracleComp (unifSpec + spec) prims.Y :=
  monadLift (lazyRandomizer log msg addrnd)

end Reduction
