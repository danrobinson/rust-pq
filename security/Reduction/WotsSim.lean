import Reduction.Harness

/-!
# Generic simulator of the WOTS game inside an SM-game adversary

`simChoose` runs the first phase of a WOTS-game adversary `W` inside a reduction: `W`'s signing
queries are answered from `startVal` (how the revealed chain value is produced) and `chainHash`
(how the chain is continued to its end), its collection queries from `coll`, and the signing
history is mirrored exactly as the game records it.  The three reductions of `Reduction.WotsUD`
and `Reduction.WotsFinal` are instances.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace WotsGame

variable {vp : ValidatedParams} {prims : Primitives vp.params}

/-- Simulated signing oracle. -/
def simSignOracle {ι : Type} {spec : OracleSpec ι} (insts : List Adrs)
    (startVal : Adrs → ℕ → OracleComp spec prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp spec prims.Y) :
    QueryImpl (signSpec prims) (StateT (List (Entry prims)) (OracleComp spec)) :=
  fun q => do
    let hist ← get
    if q.1 ∉ insts ∨ q.1 ∈ hist.map (·.1) then
      return none
    else
      let sig ← (monadLift (Vector.ofFnM fun i : Fin vp.params.len =>
          startVal (wotsChainAdrs q.1 i.val) (chainStepsCore prims.core q.2 i.val) :
          OracleComp spec (WotsSig vp.params prims.core)) :
        StateT (List (Entry prims)) (OracleComp spec) (WotsSig vp.params prims.core))
      let tops ← (monadLift (wotsPkFromSigTopsWith prims.core chainHash sig q.2 q.1 :
          OracleComp spec (Vector prims.Y vp.params.len)) :
        StateT (List (Entry prims)) (OracleComp spec) (Vector prims.Y vp.params.len))
      set (hist ++ [(q.1, q.2, sig, tops)])
      return some (sig, tops)

/-- Simulated collection oracle (same refusal rule as the game). -/
def simCollOracle {ι : Type} {spec : OracleSpec ι} [DecidableEq prims.AdrsKey]
    (insts : List Adrs) (coll : prims.AdrsKey → List prims.Y → OracleComp spec prims.Y) :
    QueryImpl (collSpec prims) (StateT (List (Entry prims)) (OracleComp spec)) :=
  fun q =>
    if reservedKey insts q.1 then pure none
    else (monadLift (some <$> coll q.1 q.2 : OracleComp spec (Option prims.Y)) :
      StateT (List (Entry prims)) (OracleComp spec) (Option prims.Y))

/-- Run phase 1 of `W` inside a reduction with oracle interface `unifSpec + spec`. -/
def simChoose {ι : Type} {spec : OracleSpec ι} [DecidableEq prims.AdrsKey]
    (W : Adversary prims) (insts : List Adrs)
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y) :
    OracleComp (unifSpec + spec) (W.State × List (Entry prims)) :=
  (simulateQ
    ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))).liftTarget
        (StateT (List (Entry prims)) (OracleComp (unifSpec + spec))) +
      (simSignOracle insts startVal chainHash + simCollOracle insts coll)) W.choose).run []

/-- The winning predicate of the WOTS game on a history (as in `hyb`). -/
def win [DecidableEq prims.Y] (pk : prims.PkSeed) (hist : List (Entry prims)) (j : ℕ)
    (m' : prims.Y) (sig' : WotsSig vp.params prims.core) : Bool :=
  match hist[j]? with
  | none => false
  | some (a, m, _, tops) => decide (m' ≠ m ∧ wotsPkFromSigTops prims sig' m' pk a = tops)

end WotsGame
end Reduction
