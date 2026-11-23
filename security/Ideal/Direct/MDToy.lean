import Ideal.Direct.MDCore

/-!
# A small instance of the Merkle–Damgård core (`status/DIRECT.md` §11)

`St = Blk = Bool`, `IV = false`.  The program `toyX`: the honest party walks the block list
`[true, false]` (two compression cells) and the "forger" then queries the compression function
at the first cell `(false, true)` and at the cell `(v₁, false)` it reaches, and reports whether
its chain value equals the honest one (in the real game it always does).  The core (`md_core`)
bounds the event by the deferred game plus twice the probability of `Bad`; the instance is
`toy_core`.  (With
one-bit chaining values `Bad` is likely; the test is that the generic statement instantiates and
composes, not the size of the bound.)
-/

open OracleComp OracleSpec

namespace Ideal.Direct.MD.Toy

/-- A walk query. -/
def wq (bs : List Bool) : OracleComp (OSp Bool Bool) Bool :=
  (liftM ((OSp Bool Bool).query (.inr bs)) : OracleComp (OSp Bool Bool) Bool)

/-- A compression query. -/
def pq (q : Bool × Bool) : OracleComp (OSp Bool Bool) Bool :=
  (liftM ((OSp Bool Bool).query (.inl (.inr q))) : OracleComp (OSp Bool Bool) Bool)

/-- The toy program. -/
def toyX : OracleComp (OSp Bool Bool) Bool := do
  let h ← wq [true, false]
  let v₁ ← pq (false, true)
  let v₂ ← pq (v₁, false)
  pure (decide (v₂ = h))

/-- **The instance of the core.** -/
theorem toy_core :
    Pr{let z ← (simulateQ (Cell Bool Bool).romImpl (simulateQ (cellsR false) toyX)).run' ∅}[
        z = true] ≤
      Pr{let z ← (simulateQ (mdG (Blk := Bool) false).deferredImpl
            (simulateQ (labI false) toyX)).run ((∅, ∅), [])
         let _st ← RelabelState.endFill z.2}[z.1 = true] + 2 *
      Pr{let z ← (simulateQ (mdG (Blk := Bool) false).deferredImpl
            (simulateQ (labI false) toyX)).run ((∅, ∅), [])
         let st ← RelabelState.endFill z.2}[(mdG (Blk := Bool) false).Bad st] :=
  md_core false toyX (· = true)

end Ideal.Direct.MD.Toy

#print axioms Ideal.Direct.MD.Toy.toy_core
